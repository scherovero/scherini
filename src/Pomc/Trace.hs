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
                  , lookup
                  , empty
                  , unrollTraceFirst
                  ) where

import Pomc.Prop (Prop(..))
import Pomc.PropConv (PropConv(..))
import Pomc.State(Input, State(..), showState, showAtom)
import Pomc.Encoding (PropSet, BitEncoding, extractInput, decodeInput)
import Pomc.SatUtil

import Prelude hiding (lookup)
import Control.Monad (foldM)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)
import qualified Data.Vector.Mutable as MV
import qualified Data.Set as Set
import Data.Maybe

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



-- PER IL PROF: praticamente mi sono accorto che ci possono essere loop infiniti nello srotolare alcune summary
-- (per esempio nel 32 c'é [(3,Summary)] che contiene [(2,Summary)] e [(2,Summary)] contiene [(3,Summary]))
-- e in più ogni Summary può essere sostituito con più combinazioni compatibili. L'unico modo per non farlo cadere in loop
-- infiniti che mi è venuto in mente è quello di srotolare un passo alla volta tutte le possibili tracce che si creano combinando
-- tutte le possibilità finchè non si trova una traccia conclusa senza più Summary, che dovrebbe essere quella giusta (o quantomeno
-- il controesempio più breve)

-- Quindi per esempio per quanto riguarda il 32 lo sviluppo è
--     unrollTrace [ [...,(1,["call"]),(2,["..."]),(5,["exc"]),(6,["exc"]),...] ]
--     unrollTrace [ [...,(1,["call"]),(2,["call"]),(3,["..."]),(18,["exc"]),(5,["exc"]),(6,["exc"]),...] ]
--     unrollTrace [ [...,(1,["call"]),(2,["call"]),(3,["call"]),(2,["..."]),(5,["exc"]),(18,["exc"]),(5,["exc"]),(6,["exc"]),...] questa combinazione srotolata porta al loop
--                   [...,(1,["call"]),(2,["call"]),(3,["call"]),(2,["..."]),(5,["exc"]),(18,["exc"]),(5,["exc"]),(6,["exc"]),...]] questa è quella giusta
--     unrollTrace [ [...,(1,["call"]),(2,["call"]),(3,["call"]),(2,["call"]),(3,["..."]),(18,["exc"]),(5,["exc"]),(18,["exc"]),(5,["exc"]),(6,["exc"]),...]
--                   [...,(1,["call"]),(2,["call"]),(3,["call"]),(2,["call"]),(3,["..."]),(18,["exc"]),(5,["exc"]),(18,["exc"]),(5,["exc"]),(6,["exc"]),...] ]
--     unrollTrace [ [...,(1,["call"]),(2,["call"]),(3,["call"]),(2,["call"]),(3,["call"]),(2,["..."]),(5,["exc"]),(18,["exc"]),(5,["exc"]),(18,["exc"]),(5,["exc"]),(6,["exc"]),...]
--                 [ [...,(1,["call"]),(2,["call"]),(3,["call"]),(2,["call"]),(3,["call"]),(3,["call"]),(5,["exc"]),(5,["exc"]),(18,["exc"]),(5,["exc"]),(18,["exc"]),(5,["exc"]),(6,["exc"]),...] ] ------> e questa seconda è quella giusta conclusa

unrollTraceFirst :: (Show state) => STRef s (TraceMap s state) -> TraceId state -> ST.ST s (TraceId state)
unrollTraceFirst tmref unrTr = do
                               --DBG.traceM ((show (checkTraceConsistency (traceToChunk (reverse unrTr)))) ++ "\n")
                               unrollTrace tmref [(traceToChunk (reverse unrTr))]

-- take a list of traces and obtain another list with every trace unrolled by one-step
-- then check if there is a closed trace without summaries, take it or unroll a step more
unrollTrace :: (Show state) => STRef s (TraceMap s state) -> [TraceChunk state] -> ST.ST s (TraceId state)
unrollTrace tmref traceList = do
                        newTraceList <- mapM (unrollSingleTrace tmref) traceList
                        --DBG.traceM ((show traceList) ++ "\n")
                        let concNewTraceList = filter checkTraceConsistency (fmap reverse $ concat newTraceList)
                            realTrace = takeClosedSummary concNewTraceList
                        if not (null realTrace)
                         then do
                           --DBG.traceM ((show concNewTraceList) ++ "\n")
                           return (chunkToTrace realTrace)
                         else do
                           --DBG.traceM ((show concNewTraceList) ++ "\n")
                           unrollTrace tmref concNewTraceList
                         
{-unrollTrace :: (Show state) => STRef s (TraceMap s state) -> [TraceChunk state] -> ST.ST s (TraceId state)
unrollTrace tmref traceList = do
                        newTraceList <- mapM (unrollSingleTrace tmref) traceList
                        --DBG.traceM ("aaaaaaaaaaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\n\n\n\n")
                        let concNewTraceList = filter checkTraceConsistency (fmap reverse $ concat newTraceList)
                        --DBG.traceM ((show concNewTraceList) ++ "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n")
                        return (chunkToTrace (head concNewTraceList))-}
                        
-- take a single TraceId and unroll by one step the Summary, returning a list of all the possible TraceIds
unrollSingleTrace :: (Show state) => STRef s (TraceMap s state) -> TraceChunk state -> ST.ST s ([TraceChunk state])
unrollSingleTrace tmref trace = 
  let foldTrace acc (Summary, q, g, p) = do
        tm <- readSTRef tmref
        (pushes, shifts, pops) <- MV.read tm (getId q)
        --DBG.traceM ((show $ findMatchChunk pushes2 pops3) ++ "\n")
        let allPossibleChunks = concatMap (findSingleCompletion (pushes, shifts, pops) g) acc
        --DBG.traceM ((show allPossibleChunks) ++ "\n\n\n\n\n\n\n\n\n\n\n\n\n\n")
        --DBG.traceM ("aaaaaaaaaaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\n\n\n\n")
        return (allPossibleChunks)
      foldTrace acc (moveType, q, g, p) = do
        --DBG.traceM ((show $ getState q) ++ "\n")
        --DBG.traceM $ (show (moveType, q, g) ++ "\n")
        --DBG.traceM ("aaaaaaaaaaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\n\n\n\n")
        return (fmap (\chunk -> (moveType, q, g, p):chunk) acc)
  in do
    foldM foldTrace [[]] trace

chunkToTrace :: TraceChunk state -> TraceId state
chunkToTrace tc = fmap (\(mt, q, g, _) -> (mt, q, g)) tc

traceToChunk :: TraceId state -> TraceChunk state
traceToChunk trc = traceToChunkSupp (tail trc) (head trc)

traceToChunkSupp :: TraceId state -> (TraceType, StateId state, Stack state) -> TraceChunk state
traceToChunkSupp [] (mt, q, g) = [(mt, q, g, q)]
traceToChunkSupp (tpl@(mt, q, g):trc) (mtprev, qprev, gprev) = (mtprev, qprev, gprev, q):(traceToChunkSupp trc tpl)

checkTraceConsistency :: TraceChunk state -> Bool
checkTraceConsistency trc = checkTraceConsistencySupp (tail trc) (head trc)

checkTraceConsistencySupp :: TraceChunk state -> (TraceType, StateId state, Stack state, StateId state) -> Bool
checkTraceConsistencySupp [] _ = True
checkTraceConsistencySupp (cur@(mt, q, g, p):trc) (mtprev, qprev, gprev, pprev) 
                                                              | not (pprev == q) = False
                                                              | (mtprev == Push) && (not (qprev == snd (fromJust g))) = False
                                                              | (mtprev == Shift || mtprev == Summary)
                                                                && (not (gprev == Nothing)) 
                                                                && (not (g == Nothing)) 
                                                                && (not (snd (fromJust gprev) == snd (fromJust g))) = False
                                                              | otherwise = checkTraceConsistencySupp trc cur
                                                    
takeLookAheadFwdState :: TraceChunk state -> StateId state
takeLookAheadFwdState trc = (\(_, _, _, fwdst) -> fwdst) $ head trc

takeLookAheadState :: TraceId state -> StateId state
takeLookAheadState trc = (\(_, fwdst, _) -> fwdst) $ head trc

takeLookAheadState2 :: TraceChunk state -> StateId state
takeLookAheadState2 trc = (\(_, fwdst, _, _) -> fwdst) $ head trc

isThereSummary :: TraceChunk state -> Bool
isThereSummary [] = False
isThereSummary ((mt, _, _, _):tpls) | mt == Summary = True
                                    | otherwise = isThereSummary tpls

takeClosedSummary :: [TraceChunk state] -> TraceChunk state
takeClosedSummary [] = []
takeClosedSummary (tc:tcs) | not (isThereSummary tc) = tc
                           | otherwise = takeClosedSummary tcs

-- find all the possible substituting chunk traces for a Summary, and put them in a list
findSingleCompletion :: (Show state) => (TraceChunk state, TraceChunk state, TraceChunk state)
                     -> Stack state
                     -> TraceChunk state
                     -> [TraceChunk state]
findSingleCompletion (pushes, shifts, pops) g acc = 
            let pushTrc = fmap (\tpl -> [tpl]) pushes --(searchTuplesByStack pushes $ takeLookAheadState acc)
                shiftTrc = completeShift shifts pushTrc
                --pushTrc = fmap (\chunk -> (completePush pushes (takeLookAheadState (chunkToTrace chunk)) g) ++ chunk) shiftTrc
                popTrc = completePop pops shiftTrc 
            in do
              DBG.traceM ((show (filter checkTraceConsistency (fmap reverse popTrc))) ++ "\n\n\n\n\n\n\n")
              --DBG.traceM ((show shiftTrc) ++ "\n")
              fmap (\chunk -> chunk ++ acc) popTrc
              --fmap (\chunk -> chunk ++ acc) (fmap reverse $ (filter checkTraceConsistency (fmap reverse popTrc)))
  
-- search all the tuples inside a TraceChunk that has the corresponding future state              
searchTuples :: TraceChunk state -> StateId state -> TraceChunk state
searchTuples trchunk fwdst = foldr (\(movetype, q, g, p) acc -> if p == fwdst then ((movetype, q, g, p):acc) else acc) [] trchunk

searchTuplesByStack :: TraceChunk state -> StateId state -> TraceChunk state
searchTuplesByStack trchunk prevst = foldr (\(movetype, q, g, p) acc -> if (snd (fromJust g)) == prevst then ((movetype, q, g, p):acc) else acc) [] trchunk

searchTuplesByState :: TraceChunk state -> StateId state -> TraceChunk state
searchTuplesByState trchunk st = foldr (\(movetype, q, g, p) acc -> if q == st then ((movetype, q, g, p):acc) else acc) [] trchunk

-- search the tuples with corresponding future state and take only the one that has same stack as Summary's
completePush :: TraceChunk state -> StateId state -> Stack state -> TraceChunk state
completePush trchunk fwdst stck = foldr (\(movetype, q, g, p) acc -> if g == stck then [(movetype, q, g, p)] else acc) [] (searchTuples trchunk fwdst)

completeShift :: TraceChunk state -> [TraceChunk state] -> [TraceChunk state]
completeShift shifts trcpushList = concatMap (completeShiftSinglePop shifts) trcpushList

-- take a single list of chunks and check if it can be completed, if not return it, otherwise for each compatible chunk found
-- create a new list chunk_found:(input_list), then call recursively completeShift on the list of the new list of chunks
-- completeShift [ chunk_found1:(input_list), chunk_found2:(input_list), chunk_found3:(input_list), ... ] 
completeShiftSinglePop :: TraceChunk state -> TraceChunk state -> [TraceChunk state]
completeShiftSinglePop shifts tp = 
                         let matchingTpls = searchTuplesByState shifts $ takeLookAheadFwdState tp in
                         if null matchingTpls
                           then [tp]
                           else completeShift shifts (fmap (\chunk -> chunk : tp) matchingTpls)

completePop :: TraceChunk state -> [TraceChunk state] -> [TraceChunk state]
completePop pops trcpopList = foldr (\chunk acc -> let matchingTpls = completeSinglePop pops chunk in
                                      if not (null matchingTpls)
                                        then ((fmap (\poptpl -> poptpl:chunk) matchingTpls) ++ acc)
                                        else acc) [] trcpopList

completeSinglePop :: TraceChunk state -> TraceChunk state -> TraceChunk state
completeSinglePop pops chunk = searchTuplesByState pops (takeLookAheadFwdState chunk)

-------- DEBUG ---------------
findAllPop :: STRef s (TraceMap s state) -> ST.ST s (TraceChunk state)
findAllPop tmref = do
                 tm <- readSTRef tmref
                 MV.foldM (\acc (pushes,shifts,pops) -> return (pops ++ acc)) [] tm
                 
findMatchChunk :: TraceChunk state -> TraceChunk state -> TraceChunk state
findMatchChunk tr1 tr2 = foldr (\(mt1, q1, g1, p1) acc1 -> foldr (\(mt2, q2, g2, p2) acc2 -> if p1 == q2 then ([(mt1, q1, g1, p1)] ++ [(mt2, q2, g2, p2)] ++ acc2) else acc2) acc1 tr2) [] tr1
