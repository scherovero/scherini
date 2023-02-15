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


takeMoveTypeTuple :: (TraceType, StateId state, Stack state, StateId state) -> TraceType
takeMoveTypeTuple (mt, q, g, p) = mt

takeStateTuple :: (TraceType, StateId state, Stack state, StateId state) -> StateId state
takeStateTuple (mt, q, g, p) = q

takeStackTuple :: (TraceType, StateId state, Stack state, StateId state) -> Stack state
takeStackTuple (mt, q, g, p) = g

takeFwdStateTuple :: (TraceType, StateId state, Stack state, StateId state) -> StateId state
takeFwdStateTuple (mt, q, g, p) = p

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

unrollTraceFirst :: (Show state) => STRef s (TraceMap s state) -> Int -> TraceId state -> ST.ST s (TraceId state)
unrollTraceFirst tmref level unrTr = do
                               --DBG.traceM ((show (checkTraceConsistency (traceToChunk (reverse unrTr)))) ++ "\n")
                               trchunk <- browseTraceInit tmref [] level (traceToChunk (reverse unrTr))
                               DBG.traceM ((show $ reverse trchunk) ++ "\n\n\n\n\n\n\n")
                               if null trchunk
                                 then unrollTraceFirst tmref (level+1) unrTr
                                 else return (reverse $ chunkToTrace trchunk)
                               --return (reverse $ chunkToTrace trchunk)

-- take a list of traces and obtain another list with every trace unrolled by one-step
-- then check if there is a closed trace without summaries, take it or unroll a step more
{-unrollTrace :: (Show state) => STRef s (TraceMap s state) -> [TraceChunk state] -> ST.ST s (TraceId state)
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
                           unrollTrace tmref concNewTraceList-}
                         
{-unrollTrace :: (Show state) => STRef s (TraceMap s state) -> [TraceChunk state] -> ST.ST s (TraceId state)
unrollTrace tmref traceList = do
                        newTraceList <- mapM (unrollSingleTrace tmref) traceList
                        --DBG.traceM ("aaaaaaaaaaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\n\n\n\n")
                        let concNewTraceList = filter checkTraceConsistency (fmap reverse $ concat newTraceList)
                        --DBG.traceM ((show concNewTraceList) ++ "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n")
                        return (chunkToTrace (head concNewTraceList))-}

browseTraceInit :: (Show state) => STRef s (TraceMap s state) -> TraceChunk state -> Int -> TraceChunk state -> ST.ST s (TraceChunk state)
browseTraceInit tmref badTpl level trc = let (left:(middle:rest)) = trc
                      in browseTrace tmref left middle rest badTpl level [left]
                        
browseTrace :: (Show state) => STRef s (TraceMap s state) 
            -> (TraceType, StateId state, Stack state, StateId state)
            -> (TraceType, StateId state, Stack state, StateId state)
            -> TraceChunk state
            -> TraceChunk state
            -> Int
            -> TraceChunk state
            -> ST.ST s (TraceChunk state)
browseTrace tmref left middle [] badTpl level acc = return (middle:acc)
browseTrace tmref left middle@(mtmiddle, qmiddle, gmiddle, pmiddle) (right:rest) badTpl level acc
                                   | mtmiddle == Summary = do
                                                             solvedSum <- resolveSummary tmref left middle right badTpl level
                                                             if null solvedSum
                                                               then return []
                                                               else browseTrace tmref middle right rest badTpl level (solvedSum ++ acc)
                                   | otherwise = browseTrace tmref middle right rest badTpl level (middle:acc)
                                   
resolveSummary :: (Show state) => STRef s (TraceMap s state)
               -> (TraceType, StateId state, Stack state, StateId state)
               -> (TraceType, StateId state, Stack state, StateId state)
               -> (TraceType, StateId state, Stack state, StateId state)
               -> TraceChunk state
               -> Int
               -> ST.ST s (TraceChunk state)
resolveSummary tmref left middle@(mt, q, g, p) right badTpl level = do
      if isSummaryVisited badTpl middle
        then return []
        else do
               tm <- readSTRef tmref
               (pushes, shifts, pops) <- MV.read tm (getId q)
               --(pushes55, shifts55, pops55) <- MV.read tm 29
               --DBG.traceM ((show pops55) ++ "\n\n\n\n\n\n\n")
               allPossibleSub <- findCompletion tmref (pushes, shifts, pops) left right level
               let consistentTrc = filter (addExtremeCheckConsistency left right) allPossibleSub
               --DBG.traceM ((show $ fmap reverse consistentTrc) ++ "\n\n\n\n\n\n\n")
               if null consistentTrc
                 then return []
                 else let realTrace = takeClosedSummary consistentTrc in
                      if not (null realTrace)
                        then return realTrace
                        else do
                               traceList <- mapM (browseTraceInit tmref (middle:badTpl) level) (fmap reverse consistentTrc)
                               --DBG.traceM ((show $ fmap reverse traceList) ++ "\n\n\n\n\n\n\n")
                               return (takeShortestList $ filter (not . null) traceList)
   
      
findCompletion :: (Show state) => STRef s (TraceMap s state)
               -> (TraceChunk state, TraceChunk state, TraceChunk state)
               -> (TraceType, StateId state, Stack state, StateId state)
               -> (TraceType, StateId state, Stack state, StateId state)
               -> Int
               -> ST.ST s ([TraceChunk state])
findCompletion tmref (pushes, shifts, pops) left right level = do
            pushTrc <- mapM (\push -> completePush tmref [] level push) (filter (\push -> checkTraceConsistency (left:[push])) pushes)
            --DBG.traceM ((show $ filter checkTraceConsistency (concat pushTrc)) ++ "\n\n\n\n\n\n\n\n\n\n\n\n")
            shiftTrc <- completeShift tmref (filter checkTraceConsistency $ concat pushTrc)
            --DBG.traceM ((show shiftTrc) ++ "\n\n\n\n\n\n\n\n\n\n\n\n")
            popTrc <- mapM (completePop tmref pops (takeStateTuple right) level) shiftTrc
            --DBG.traceM ((show $ concat popTrc) ++ "\n\n\n\n\n\n\n\n\n\n\n\n")
            return (fmap reverse (concat popTrc))

completePush :: (Show state) => STRef s (TraceMap s state) 
             -> TraceChunk state
             -> Int
             -> (TraceType, StateId state, Stack state, StateId state)
             -> ST.ST s ([TraceChunk state])
completePush _ _ 1 tpl@(mt, q, g, p) = return [[tpl]]
completePush tmref badTpl level tpl@(mt, q, g, p) =
                    if isStateVisited badTpl tpl
                      then return [[]]
                      else do
                        tm <- readSTRef tmref
                        (pushes, _, _) <- MV.read tm (getId p)
                        if null pushes
                          then return [[tpl]]
                          else let morePushes = fmap (\(mtpush, qpush, gpush, ppush) -> 
                                       (mtpush, qpush, Just (fst (fromJust gpush), q), ppush)) 
                                       (filter (\(mtpush, qpush, gpush, ppush) -> not ((snd (fromJust gpush)) == q)) pushes)
                               in do
                                 combinations <- mapM (completePush tmref (tpl:badTpl) (level-1)) (pushes ++ morePushes)
                                 let filtConcCombinations = filter checkTraceConsistency $ filter (not . null) (concat combinations)
                                     newCombinations = fmap (\chunk -> tpl:chunk) filtConcCombinations
                                 --DBG.traceM ((show newCombinations) ++ "\n\n\n\n\n\n\n")
                                 return ([[tpl]] ++ newCombinations)
                                 
completeShift :: STRef s (TraceMap s state) -> [TraceChunk state] -> ST.ST s ([TraceChunk state])
completeShift tmref trcpushList = do
                             shiftComb <- mapM (completeShiftInit tmref) trcpushList
                             return (concat shiftComb)
                             
completeShiftInit :: STRef s (TraceMap s state) -> TraceChunk state -> ST.ST s ([TraceChunk state])
completeShiftInit tmref trcpush = 
                       let (_, q, _, p)= head $ reverse trcpush
                       in do
                         tm <- readSTRef tmref
                         (_, shifts, _) <- MV.read tm (getId q)
                         let matchingTpls = searchTuplesByState shifts p
                         if null matchingTpls
                           then return [trcpush]
                           else return (fmap (\chunk -> trcpush ++ chunk) (concatMap (completeSingleShift shifts []) matchingTpls))
                         
completeSingleShift :: TraceChunk state
                    -> TraceChunk state
                    -> (TraceType, StateId state, Stack state, StateId state)
                    -> [TraceChunk state]
completeSingleShift shifts badTpl tpl@(mt, q, g, p) = 
                         if isStateVisited badTpl tpl
                           then [[]]
                           else let matchingTpls = searchTuplesByState shifts p in
                                if null matchingTpls
                                  then [[tpl]]
                                  else let combinations = fmap (completeSingleShift shifts (tpl:badTpl)) matchingTpls
                                           filtConcCombinations = filter (not . null) (concat combinations)
                                           newCombinations = fmap (\chunk -> tpl:chunk) filtConcCombinations
                                       in newCombinations
                                       
completePop :: (Show state) => STRef s (TraceMap s state) -> TraceChunk state -> StateId state -> Int -> TraceChunk state -> ST.ST s ([TraceChunk state])
completePop tmref pops fwdSt level pushShiftTrc = do
                     popComb <- mapM (completeSinglePop tmref (tail pushShiftTrc) level) (searchTuples pops fwdSt)
                     let filtConcCombinations = filter checkTraceConsistency $ filter (not . null) (fmap reverse $ concat popComb)
                     return (fmap (\chunk -> pushShiftTrc ++ chunk) filtConcCombinations)
                     
completeSinglePop :: (Show state) => STRef s (TraceMap s state) 
                  -> TraceChunk state
                  -> Int
                  -> (TraceType, StateId state, Stack state, StateId state)
                  -> ST.ST s ([TraceChunk state])
completeSinglePop _ [] _ tpl@(mt, q, g, p) = return [[tpl]]
completeSinglePop tmref pushShiftTrc level tpl@(mt, q, g, p) = do
                      let (mtpush, qpush, gpush, ppush) = head pushShiftTrc
                      if not (mtpush == Push)
                        then return [[tpl]]
                        else do
                               tm <- readSTRef tmref
                               (_, _, pops) <- MV.read tm (getId qpush)
                               let possiblePops = searchTuples pops q
                               --DBG.traceM ((show possiblePops) ++ "\n\n\n\n\n\n\n")
                               if null possiblePops
                                 then return [[]]
                                 else do
                                 combinations <- mapM (completeSinglePop tmref (tail pushShiftTrc) (level-1)) possiblePops
                                 let filtConcCombinations = filter (not . null) (concat combinations)
                                     newCombinations = fmap (\chunk -> tpl:chunk) filtConcCombinations
                                 --DBG.traceM ((show newCombinations) ++ "\n\n\n\n\n\n\n")
                                 return newCombinations
                     
-- take a single TraceId and unroll by one step the Summary, returning a list of all the possible TraceIds
{-unrollSingleTrace :: (Show state) => STRef s (TraceMap s state) -> TraceChunk state -> ST.ST s ([TraceChunk state])
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
    foldM foldTrace [[]] trace-}

chunkToTrace :: TraceChunk state -> TraceId state
chunkToTrace tc = fmap (\(mt, q, g, _) -> (mt, q, g)) tc

traceToChunk :: TraceId state -> TraceChunk state
traceToChunk trc = traceToChunkSupp (tail trc) (head trc)

traceToChunkSupp :: TraceId state -> (TraceType, StateId state, Stack state) -> TraceChunk state
traceToChunkSupp [] (mt, q, g) = [(mt, q, g, q)]
traceToChunkSupp (tpl@(mt, q, g):trc) (mtprev, qprev, gprev) = (mtprev, qprev, gprev, q):(traceToChunkSupp trc tpl)

takeShortestList :: [TraceChunk state] -> TraceChunk state
takeShortestList lol = if null lol then [] else takeShortestListSupp (tail lol) (head lol) 

takeShortestListSupp :: [TraceChunk state] -> TraceChunk state -> TraceChunk state
takeShortestListSupp [] shortest = shortest
takeShortestListSupp (chunk:rest) shortest | length chunk < length shortest = takeShortestListSupp rest chunk
                                           | otherwise = takeShortestListSupp rest shortest

addExtremeCheckConsistency :: (TraceType, StateId state, Stack state, StateId state)
                           -> (TraceType, StateId state, Stack state, StateId state)
                           -> TraceChunk state
                           -> Bool
addExtremeCheckConsistency left right trc = checkTraceConsistency (left:(reverse (right:trc)))
                           
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
                           
isSummaryVisited :: TraceChunk state -> (TraceType, StateId state, Stack state, StateId state) -> Bool
isSummaryVisited badTpl middle = foldr (\btpl acc -> if (takeStateTuple btpl) == (takeStateTuple middle) then True else acc) False badTpl

isStateVisited :: TraceChunk state -> (TraceType, StateId state, Stack state, StateId state) -> Bool
isStateVisited badTpl tuple = foldr (\btpl acc -> if (takeStateTuple btpl) == (takeStateTuple tuple) then True else acc) False badTpl

-- find all the possible substituting chunk traces for a Summary, and put them in a list
{-findSingleCompletion :: (Show state) => (TraceChunk state, TraceChunk state, TraceChunk state)
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
              --fmap (\chunk -> chunk ++ acc) (fmap reverse $ (filter checkTraceConsistency (fmap reverse popTrc)))-}
  
-- search all the tuples inside a TraceChunk that has the corresponding future state              
searchTuples :: TraceChunk state -> StateId state -> TraceChunk state
searchTuples trchunk fwdst = foldr (\(movetype, q, g, p) acc -> if p == fwdst then ((movetype, q, g, p):acc) else acc) [] trchunk

searchTuplesByStack :: TraceChunk state -> StateId state -> TraceChunk state
searchTuplesByStack trchunk prevst = foldr (\(movetype, q, g, p) acc -> if (snd (fromJust g)) == prevst then ((movetype, q, g, p):acc) else acc) [] trchunk

searchTuplesByState :: TraceChunk state -> StateId state -> TraceChunk state
searchTuplesByState trchunk st = foldr (\(movetype, q, g, p) acc -> if q == st then ((movetype, q, g, p):acc) else acc) [] trchunk

searchTuplesForPop :: TraceChunk state -> StateId state -> StateId state -> TraceChunk state
searchTuplesForPop pops fwdStateLeft stateRight = foldr (\(movetype, q, g, p) acc -> if (fwdStateLeft == q) && (p == stateRight) then ((movetype, q, g, p):acc) else acc) [] pops

{--- search the tuples with corresponding future state and take only the one that has same stack as Summary's
completePush :: TraceChunk state -> StateId state -> Stack state -> TraceChunk state
completePush trchunk fwdst stck = foldr (\(movetype, q, g, p) acc -> if g == stck then [(movetype, q, g, p)] else acc) [] (searchTuples trchunk fwdst)-}

{-completeShift :: TraceChunk state -> [TraceChunk state] -> [TraceChunk state]
completeShift shifts trcpushList = concatMap (completeShiftSinglePop shifts) trcpushList

-- take a single list of chunks and check if it can be completed, if not return it, otherwise for each compatible chunk found
-- create a new list chunk_found:(input_list), then call recursively completeShift on the list of the new list of chunks
-- completeShift [ chunk_found1:(input_list), chunk_found2:(input_list), chunk_found3:(input_list), ... ] 
completeShiftSinglePop :: TraceChunk state -> TraceChunk state -> [TraceChunk state]
completeShiftSinglePop shifts tp = 
                         let matchingTpls = searchTuplesByState shifts $ takeLookAheadFwdState tp in
                         if null matchingTpls
                           then [tp]
                           else completeShift shifts (fmap (\chunk -> chunk : tp) matchingTpls)-}

{-completePop :: TraceChunk state
            -> (TraceType, StateId state, Stack state, StateId state)
            -> [TraceChunk state]
            -> [TraceChunk state]
completePop pops right trcpopList = foldr (\chunk acc -> let matchingTpls = completeSinglePop pops (head chunk) right in
                                      if not (null matchingTpls)
                                        then ((fmap (\poptpl -> poptpl:chunk) matchingTpls) ++ acc)
                                        else acc) [] trcpopList

completeSinglePop :: TraceChunk state
                  -> (TraceType, StateId state, Stack state, StateId state)
                  -> (TraceType, StateId state, Stack state, StateId state)
                  -> TraceChunk state
completeSinglePop pops left right = searchTuplesForPop pops (takeFwdStateTuple left) (takeStateTuple right)-}

-------- DEBUG ---------------
findAllPop :: STRef s (TraceMap s state) -> ST.ST s (TraceChunk state)
findAllPop tmref = do
                 tm <- readSTRef tmref
                 MV.foldM (\acc (pushes,shifts,pops) -> return (pops ++ acc)) [] tm
                 
findMatchChunk :: TraceChunk state -> TraceChunk state -> TraceChunk state
findMatchChunk tr1 tr2 = foldr (\(mt1, q1, g1, p1) acc1 -> foldr (\(mt2, q2, g2, p2) acc2 -> if p1 == q2 then ([(mt1, q1, g1, p1)] ++ [(mt2, q2, g2, p2)] ++ acc2) else acc2) acc1 tr2) [] tr1

