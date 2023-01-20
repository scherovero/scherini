{- |
   Module      : Pomc.SetMap
   Copyright   : 2021 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari, Francesco Pontiggia
-}

module Pomc.Trace ( TraceType(..)
                  , TraceId
                  , Trace
                  , TraceMap
                  , unIdTrace
                  , toInputTrace
                  , showTrace
                  , insert
                 -- , insertDBG
                 -- , emptyDBG
                 -- , lookupDBG
                 -- , insertSummary
                  , lookup
                 -- , modifyAll
                  , empty
                  , unrollTrace
                  ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), Alphabet)
import Pomc.Potl (Formula(..))
import Pomc.Check (EncPrecFunc, makeOpa)
import Pomc.PropConv (APType, PropConv(..), convProps)
import Pomc.State(Input, State(..), showState, showAtom)
import Pomc.Encoding (PropSet, BitEncoding, extractInput, decodeInput)
import Pomc.SatUtil
--import Pomc.SCCAlgorithm
--import Pomc.SetMap

import Prelude hiding (lookup)
import Control.Monad (foldM)
import qualified Control.Monad.ST as ST
import Data.Maybe
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)
import qualified Data.Vector.Mutable as MV
--import Data.Set (Set)
import qualified Data.Set as Set

import qualified Debug.Trace as DBG

-- Trace data type
data TraceType = Push | Shift | Pop | Summary | Found deriving (Eq, Ord, Show)
type TraceChunk state = [(TraceType, StateId state, Stack state, StateId state)]
type TraceId state = [(TraceType, StateId state, Stack state)]
type Trace state = [(TraceType, state, Maybe (Input, state))]

-- Begin debugging stuff
unIdTrace :: TraceId state -> Trace state
unIdTrace trace =
  map (\(moveType, q, g) ->
         (moveType, getState q, fmap (\(b, r) -> (b, getState r)) g)) trace

toInputTrace :: (SatState state) => BitEncoding -> Trace state -> [(state, PropSet)]
toInputTrace be trace = foldr foldInput [] trace
  where foldInput (moveType, q, _) rest
          | moveType == Push || moveType == Shift || moveType == Pop =
            (q, stateToInput q) : rest
          | moveType == Summary =
            (q, Set.empty) : rest
          | moveType == Found =
            (q, Set.singleton End) : rest
          | otherwise = rest
        stateToInput q =
          (decodeInput be) . (extractInput be) . current . getSatState $ q

showTrace :: (SatState state, Show state, Show a)
          => BitEncoding
          -> PropConv a
          -> Trace state
          -> String
showTrace be pconv trace = concatMap showMove trace
  where showMove (moveType, q, g) =
          show moveType     ++ ":\nRaw State:\n" ++
          show q ++ "\nCheck State:\n" ++
          showState be pconv (getSatState q) ++ "\nStack:\n" ++
          showStack g ++ "\n\n"
        showStack (Just (b, r)) =
          showAtom be pconv b ++ "\n" ++
          show r ++ "\n" ++
          showState be pconv (getSatState r)
        showStack Nothing = "Bottom"
-- End debugging stuff

-- Map to TraceId chains
type TraceMap s state = MV.MVector s (TraceChunk state, TraceChunk state, TraceChunk state)

-- append a trace chunk at the corresponding index into TraceMap
insert :: STRef s (TraceMap s state)
       -> Int
       -> (TraceType, StateId state, Stack state, StateId state)
       -> ST.ST s ()
insert tmref idx trctuple = do
  tm <- readSTRef tmref
  let len = MV.length tm
  if idx < len
    then do
      tl <- MV.read tm idx
      let newtuple = insertInTuple tl trctuple
      MV.write tm idx newtuple
    else let newLen = computeLen len idx
             computeLen size newIdx | newIdx < size = size
                                    | otherwise = computeLen (size*2) newIdx
           in do { grown <- MV.grow tm (newLen-len)
                 ; mapM_ (\i -> MV.write grown i ([],[],[])) [len..(newLen-1)]
                 ; let { newtuple = insertInTuple ([],[],[]) trctuple }
                 ; MV.write grown idx newtuple
                 ; writeSTRef tmref grown
                 }
                 
insertInTuple :: (TraceChunk state, TraceChunk state, TraceChunk state) 
              -> (TraceType, StateId state, Stack state, StateId state)
              -> (TraceChunk state, TraceChunk state, TraceChunk state)              
insertInTuple tpl@(push, shift, pop) trctuple@(movetype, _, _, _)
                  | (movetype == Push) && (isNotPresentTuple push trctuple) = (trctuple : push, shift, pop)
                  | (movetype == Shift || movetype == Summary) && (isNotPresentTuple shift trctuple) = (push, trctuple : shift, pop)
                  | (movetype == Pop) && (isNotPresentTuple pop trctuple) = (push, shift, trctuple : pop)
                  | otherwise = tpl

-- check if a tuple is in the corresponding traceChunk
isPresentTuple :: TraceChunk state -> (TraceType, StateId state, Stack state, StateId state) -> Bool
isPresentTuple trchunk trctuple = trctuple `elem` trchunk
{-isPresentTuple :: TraceChunk state -> (TraceType, StateId state, Stack state, StateId state) -> Bool
isPresentTuple trchunk trctuple = False-}

isNotPresentTuple :: TraceChunk state -> (TraceType, StateId state, Stack state, StateId state) -> Bool
isNotPresentTuple trchunk trctuple = not (isPresentTuple trchunk trctuple)
 
-- an empty TraceMap, an array of 3-tuple of empty lists
empty :: ST.ST s (STRef s (TraceMap s state))
empty = do
  tm <- MV.replicate 4 ([],[],[])
  newSTRef tm
                                   
-- extract trace from TraceMap
lookup :: STRef s (TraceMap s state) -> Int -> ST.ST s (TraceChunk state, TraceChunk state, TraceChunk state)
lookup tmref idx = do
  tm <- readSTRef tmref
  if idx < MV.length tm
    then MV.read tm idx
    else return ([],[],[])
    
readTraceChunk :: (TraceChunk state, TraceChunk state, TraceChunk state) -> TraceType -> TraceChunk state
readTraceChunk (push, _, _) Push = push
readTraceChunk (_, shift, _) Shift = shift
readTraceChunk (_, shift, _) Summary = shift
readTraceChunk (_, _, pop) Pop = pop

unrollTrace :: (Show state) => STRef s (TraceMap s state) -> [TraceId state] -> ST.ST s (TraceId state)
unrollTrace tmref traceList = do
                        newTraceList <- mapM (unrollSingleTrace tmref) traceList
                        let concNewTraceList = concat newTraceList
                            realTrace = takeClosedSummary concNewTraceList
                        if not (null realTrace)
                         then return (realTrace)
                         else unrollTrace tmref (fmap reverse concNewTraceList)

-- complete the trace given substituting recursively the summaries with the saved trace chunks
unrollSingleTrace :: (Show state) => STRef s (TraceMap s state) -> TraceId state -> ST.ST s ([TraceId state])
unrollSingleTrace tmref trace = 
  let foldTrace acc sum@(Summary, q, g) = do
        tm <- readSTRef tmref
        --allpop <- findAllPop tmref
        (pushes, shifts, pops) <- MV.read tm (getId q)
        let allPossibleChunks = concatMap (findSingleCompletion (pushes, shifts, pops)) acc
            --shiftTrc = completeShift
            --shiftTrc = (searchChunk shifts $ takeLookAheadState2 popTrc) ++ popTrc
            --pushTrc = (searchChunk pushes $ takeLookAheadState2 shiftTrc) ++ shiftTrc
            --popTrc = searchTuple allpop $ takeLookAheadState acc
        -- TODO: confrontare le pop con un look-ahead della transizione successiva per trovare quella giusta
        --       andare a ritroso fino alla push
        --       srotolare ricorsivamente i summary ottenuti
        --DBG.traceM ((show $ (length popTrace == 1)) ++ "\n")
        --unrolled <- unrollTrace tmref (reverse pushTrc)
        --return (popTrc ++ acc)
        --return (concshift ++ acc)
        return (allPossibleChunks)
      foldTrace acc (moveType, q, g) = do
        --DBG.traceM ((show $ getState q) ++ "\n")
        --DBG.traceM $ (show (moveType, q, g) ++ "\n")
        return (fmap (\chunk -> (moveType, q, g):chunk) acc)
  in do
    foldM foldTrace [[]] trace

chunkToTrace :: TraceChunk state -> TraceId state
chunkToTrace tc = fmap (\(mt,a,b,c) -> (mt,a,b)) tc

takeLookAheadState :: TraceId state -> StateId state
takeLookAheadState trc = (\(_, fwdst, _) -> fwdst) $ head trc

takeLookAheadState2 :: TraceChunk state -> StateId state
takeLookAheadState2 trc = (\(_, fwdst, _, _) -> fwdst) $ head trc

isThereSummary :: TraceId state -> Bool
isThereSummary [] = False
isThereSummary ((mt, q, g):tpls) | mt == Summary = True
                                 | otherwise = isThereSummary tpls

takeClosedSummary :: [TraceId state] -> TraceId state
takeClosedSummary [] = []
takeClosedSummary (tc:tcs) | not (isThereSummary tc) = tc
                           | otherwise = takeClosedSummary tcs
                           
findSingleCompletion :: (TraceChunk state, TraceChunk state, TraceChunk state)
                     -> TraceId state
                     -> [TraceId state]
findSingleCompletion (pushes, shifts, pops) acc = 
            let popTrc = fmap (\tpl -> [tpl]) (searchTuples pops $ takeLookAheadState acc)
                --shiftTrc = fmap chunkToTrace (completeShift shifts popTrc)
                shiftTrc = completeShift shifts popTrc
                pushTrc = fmap (\chunk -> (searchTuples pushes $ takeLookAheadState (chunkToTrace chunk)) ++ chunk) shiftTrc
            in fmap (\chunk -> chunk ++ acc) (fmap chunkToTrace pushTrc)

    
filterShift shift = foldr (\(mt, q, g, p) acc -> if mt == Summary then acc else (mt, q, g, p):acc) [] shift

findSummary :: TraceId state -> TraceId state
findSummary trc = foldr (\(mt,q,g) acc -> if mt == Summary then [(mt,q,g)] else acc) [] trc

findCorrespondingPushPop :: TraceChunk state -> TraceChunk state -> TraceChunk state
findCorrespondingPushPop push pop = foldr (\(mt, q, g, p) acc -> foldr (\(mt2, q2, g2, p2) acc2 -> if q == (snd (fromJust g2)) then ((mt, q, g, p) : (mt2, q2, g2, p2) : acc) else acc2) acc pop) [] push

matchChunks :: TraceChunk state -> TraceChunk state -> TraceChunk state
matchChunks push pop = foldr (\(mt, q, g, p) acc -> foldr (\(mt2, q2, g2, p2) acc2 -> if p == q2 then ([(mt, q, g, p)] ++ [(mt2, q2, g2, p2)]) else acc2) acc pop) [] push
  
-- search all the tuples inside a TraceChunk that has the corresponding future state    
          
searchTuples :: TraceChunk state -> StateId state -> TraceChunk state
searchTuples trchunk fwdst = foldr (\(movetype, q, g, p) acc -> if p == fwdst then ((movetype, q, g, p):acc) else acc) [] trchunk
          
{-completePush :: TraceChunk state -> StateId state -> [TraceChunk state]
completePush trchunk fwdst = searchTuples trchunk fwdst

completePush2 :: TraceChunk state -> TraceId state -> StateId state -> TraceId state
completePush2 trchunk shifttrc fwdst = if null shifttrc
                                        then searchTuple trchunk fwdst
                                        else let (_, fwdstPush, _) = head shifttrc
                                             in searchTuple trchunk fwdstPush-}

completeShift :: TraceChunk state -> [TraceChunk state] -> [TraceChunk state]
completeShift shifts trcpopList = concatMap (completeShiftSinglePop shifts) trcpopList

completeShiftSinglePop :: TraceChunk state -> TraceChunk state -> [TraceChunk state]
completeShiftSinglePop shifts tp = 
                         let matchingTpls = searchTuples shifts $ takeLookAheadState (chunkToTrace tp) in
                         if null matchingTpls
                           then [tp]
                           else completeShift shifts (fmap (\chunk -> chunk : tp) matchingTpls)

{-completePop :: TraceChunk state -> StateId state -> TraceId state
completePop trchunk fwdst = searchTuples trchunk fwdst-}

findAllShift :: STRef s (TraceMap s state) -> ST.ST s (TraceChunk state)
findAllShift tmref = do
  tm <- readSTRef tmref
  MV.foldM (\acc (_, shift,_) -> return (acc ++ (filterShift shift))) [] tm
  
findAllPop :: STRef s (TraceMap s state) -> ST.ST s (TraceChunk state)
findAllPop tmref = do
  tm <- readSTRef tmref
  MV.foldM (\acc (_,_, pop) -> return (acc ++ pop)) [] tm

findAllPush :: STRef s (TraceMap s state) -> ST.ST s (TraceChunk state)
findAllPush tmref = do
  tm <- readSTRef tmref
  MV.foldM (\acc (push,_,_) -> return (acc ++ push)) [] tm
  
{-
modifyAll :: (Ord state) => STRef s (TraceMap s state) 
                         -> ((TraceType, StateId state, Stack state) -> (TraceType, StateId state, Stack state)) 
                         -> ST.ST s ()
modifyAll tmref f = do
  tm <- readSTRef tmref
  mapM_ (MV.unsafeModify tm $ map f) [0..((MV.length tm) -1)]
  
--DBG-----------------------------  
emptyDBG :: ST.ST s (STRef s (TraceMap s state))
emptyDBG = do
  tm <- MV.replicate 30 []
  newSTRef tm
  
insertDBG :: STRef s (TraceMap s state) -> Int -> (TraceType, StateId state, Stack state) -> ST.ST s ()
insertDBG tmref idx trchunk = do
  tm <- readSTRef tmref
  tl <- MV.unsafeRead tm idx
  MV.unsafeWrite tm idx (trchunk : tl)
  
lookupDBG :: STRef s (TraceMap s state) -> Int -> ST.ST s (TraceId state)
lookupDBG tmref idx = do
  tm <- readSTRef tmref
  MV.unsafeRead tm idx
exploreTraceMap :: STRef s (TraceMap s state) -> ST.ST s (TraceId state)
exploreTraceMap tmref = do
  tm <- readSTRef tmref
  MV.foldM (\acc str -> return (acc ++ str)) [] tm
  
takeChunkTraceMap :: STRef s (TraceMap s state) -> StateId state -> (TraceType, StateId state, Stack state) -> ST.ST s (TraceId state)  
takeChunkTraceMap tmref stat sum = do
  tm <- readSTRef tmref
  MV.foldM (\acc str -> if null str then return (sum : acc) else takeStat acc str stat) [] tm
takeStat :: TraceId state -> TraceId state -> StateId state -> ST.ST s (TraceId state)  
takeStat acc str stat = let r@(mt, q, g) = head str
                        in do
                          return (r : acc)
-}
