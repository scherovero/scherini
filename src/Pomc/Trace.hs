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

-- Trace data type
data TraceType = Push | Shift | Pop | Summary | Found deriving (Eq, Show)
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
          | moveType == Push || moveType == Shift =
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
      tl <- MV.unsafeRead tm idx
      let newtuple = insertInTuple tl trctuple
      MV.unsafeWrite tm idx newtuple
    else let newLen = computeLen len idx
             computeLen size newIdx | newIdx < size = size
                                    | otherwise = computeLen (size*2) newIdx
           in do { grown <- MV.grow tm (newLen-len)
                 ; mapM_ (\i -> MV.unsafeWrite grown i ([],[],[])) [len..(newLen-1)]
                 ; let { newtuple = insertInTuple ([],[],[]) trctuple }
                 ; MV.unsafeWrite grown idx newtuple
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
    then MV.unsafeRead tm idx
    else return ([],[],[])
    
readTraceChunk :: (TraceChunk state, TraceChunk state, TraceChunk state) -> TraceType -> TraceChunk state
readTraceChunk (push, _, _) Push = push
readTraceChunk (_, shift, _) Shift = shift
readTraceChunk (_, shift, _) Summary = shift
readTraceChunk (_, _, pop) Pop = pop

-- complete the trace given substituting recursively the summaries with the saved trace chunks
unrollTrace :: STRef s (TraceMap s state) -> TraceId state -> ST.ST s (TraceId state)
unrollTrace tmref trace = 
  let foldTrace acc sum@(Summary, q, _) = do
        (push, shift, pop) <- lookup tmref (getId q)
        let (_, fwdstPop, _) = head acc
            poptrc = completePop pop fwdstPop
            (_, fwdstShift, _) = head poptrc
            shifttrc = completeShift shift fwdstShift
            --(_, fwdstShift2, _) = head shifttrc
            --shifttrc2 = searchTuple shift fwdstShift2
            --shifttrc = completeShift shift fwdstShift
            --(_, fwdstPush, _) = head shifttrc
            --(_, fwdstPush, _, _) = head shift
            pushtrc = completePush2 push shifttrc fwdstPop
        --return (pushtrc ++ shifttrc ++ poptrc ++ acc)
        --return ((fmap (\(mt, q, g, p) -> (mt, q, g)) (filterShift shift)) ++ (fmap (\(mt, q, g) -> (Shift, q, g)) poptrc) ++ acc)
        --return (shifttrc ++ (fmap (\(mt, q, g) -> (Shift, q, g)) poptrc) ++ acc)
        return (pushtrc ++ shifttrc ++ (fmap (\(mt, q, g) -> (Shift, q, g)) poptrc) ++ acc)
        --return ((fmap (\(mt, q, g) -> (Shift, q, g)) poptrc) ++ acc)
      foldTrace acc (moveType, q, g) = do
        return ((moveType, q, g) : acc)
  in do
    foldM foldTrace [] trace
    
filterShift shift = foldr (\(mt, q, g, p) acc -> if mt == Summary then acc else (mt, q, g, p):acc) [] shift


    
-- search a tuple inside a TraceChunk that has the corresponding future state    
searchTuple :: TraceChunk state -> StateId state -> TraceId state
searchTuple [] _ = []
searchTuple ((movetype, q, g, p):rest) fwdst =
          if p == fwdst then [(movetype, q, g)] else searchTuple rest fwdst
          
searchTuple2 :: TraceChunk state -> StateId state -> TraceId state
searchTuple2 trchunk fwdst = foldr (\(movetype, q, g, p) acc -> if p == fwdst then ((movetype, q, g):acc) else acc) [] trchunk
          
completePush :: TraceChunk state -> StateId state -> TraceId state
completePush trchunk fwdst = searchTuple trchunk fwdst

completePush2 :: TraceChunk state -> TraceId state -> StateId state -> TraceId state
completePush2 trchunk shifttrc fwdst = if null shifttrc
                                        then searchTuple trchunk fwdst
                                        else let (_, fwdstPush, _) = head shifttrc
                                             in searchTuple trchunk fwdstPush


completeShift :: TraceChunk state -> StateId state -> TraceId state
completeShift tc fs = completeShiftPartial tc fs []
  where completeShiftPartial trchunk fwdst precres =
          let tuple = searchTuple trchunk fwdst
              partres = tuple ++ precres
          in if partres == precres
               then partres
               else 
                 let (_, q, _) = head tuple
                 in completeShiftPartial trchunk q partres

completePop :: TraceChunk state -> StateId state -> TraceId state
completePop trchunk fwdst = searchTuple trchunk fwdst
    
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
