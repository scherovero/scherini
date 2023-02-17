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
import Data.Set (Set)
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

----------------------------------------------------------------------------------------------------------------
--------- FASE UNROLL-------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------------

unrollTraceFirst :: (Show state) => STRef s (TraceMap s state) -> Int -> TraceId state -> ST.ST s (TraceId state)
unrollTraceFirst tmref level unrTr = do
                               --DBG.traceM ("\n\naaaaa\n\n\n\n\n")
                               --allPops <- findAllPop tmref
                               --(pushes55, shifts55, pops55) <- MV.read tm 2487
                               --DBG.traceM ((show {-$ filter (\(mt,q,g,p) -> getId p == 13070)-} shifts55) ++ "\n\n\n\n\n\n\n")
                               --DBG.traceM ((show $ searchTuplesByIdx allPops 13070) ++ "\n\n\n\n\n\n\n")
                               --DBG.traceM ((show (checkTraceConsistency (traceToChunk (reverse unrTr)))) ++ "\n")
                               trchunk <- browseTraceInit tmref Set.empty level (traceToChunk (reverse unrTr))
                               DBG.traceM ((show $ reverse trchunk) ++ "\n\n\n\n\n\n\n")
                               return (reverse $ chunkToTrace trchunk)
                               
browseTraceInit :: (Show state) => STRef s (TraceMap s state) 
                -> Set (StateId state)
                -> Int
                -> TraceChunk state
                -> ST.ST s (TraceChunk state)
browseTraceInit tmref badTpl level trc = let (left:(middle:rest)) = trc
                      in browseTrace tmref left middle rest badTpl level [left]
                        
browseTrace :: (Show state) => STRef s (TraceMap s state) 
            -> (TraceType, StateId state, Stack state, StateId state)
            -> (TraceType, StateId state, Stack state, StateId state)
            -> TraceChunk state
            -> Set (StateId state)
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
               -> Set (StateId state)
               -> Int
               -> ST.ST s (TraceChunk state)
resolveSummary tmref left middle@(mt, q, g, p) right badTpl level = do
      if isStateVisited badTpl q
        then return []
        else do
               tm <- readSTRef tmref
               (pushes, shifts, pops) <- MV.read tm (getId q)
               --allPops <- findAllPop tmref
               --(pushes55, shifts55, pops55) <- MV.read tm 2487
               --DBG.traceM ((show $ filter (\(mt,q,g,p) -> getId p == 2217) pushes55) ++ "\n\n\n\n\n\n\n")
               --DBG.traceM ((show $ searchTuplesByIdx allPops 13070) ++ "\n\n\n\n\n\n\n")
               allPossibleSub <- findCompletion tmref (pushes, shifts, pops) left right 1
               let consistentTrc = filter (addExtremeCheckConsistency left right) allPossibleSub
               --DBG.traceM ((show $ fmap reverse consistentTrc) ++ "\n\n\n\n\n\n\n")
               if null consistentTrc
                 then return []
                 else let realTrace = takeClosedSummary consistentTrc in
                      if not (null realTrace)
                        then return realTrace
                        else do
                               traceList <- mapM (browseTraceInit tmref (Set.insert q badTpl) level) (fmap reverse consistentTrc)
                               --DBG.traceM ((show $ fmap reverse traceList) ++ "\n\n\n\n\n\n\n")
                               return (takeShortestList $ filter (not . null) traceList)
      
      
---------------------- FUNZIONI PER RISOLVERE IL SINGOLO SOMMARIO -------------------------------
      
findCompletion :: (Show state) => STRef s (TraceMap s state)
               -> (TraceChunk state, TraceChunk state, TraceChunk state)
               -> (TraceType, StateId state, Stack state, StateId state)
               -> (TraceType, StateId state, Stack state, StateId state)
               -> Int
               -> ST.ST s ([TraceChunk state])
findCompletion tmref (pushes, shifts, pops) left right level = do
            pushTrc <- mapM (\push -> completePush tmref Set.empty level push) (filter (\push -> checkTraceConsistency (left:[push])) pushes)
            --DBG.traceM ((show $ filter checkTraceConsistency (concat pushTrc)) ++ "\n\n\n\n\n\n\n\n\n\n\n\n")
            let filtPushTrc = filter checkTraceConsistency $ concat pushTrc
            shiftTrc <- mapM (\chunk -> completeShiftInit tmref (takeStateTuple $ last chunk) (takeFwdStateTuple $ last chunk) chunk) filtPushTrc
            --DBG.traceM ((show $ filter checkTraceConsistency (concat shiftTrc)) ++ "\n\n\n\n\n\n\n\n\n\n\n\n")
            popTrc <- mapM (completePop tmref (takeStateTuple right) ) (filter checkTraceConsistency $ concat shiftTrc)
            --DBG.traceM ((show $ concat popTrc) ++ "\n\n\n\n\n\n\n\n\n\n\n\n")
            let allComb = fmap reverse (concat popTrc)
            --DBG.traceM ((show $ fmap reverse allComb) ++ "\n\n\n\n\n\n\n\n\n\n\n\n")
            if null allComb
              then do
                DBG.traceM ((show $ level+1) ++ "\n\n\n\n\n\n\n\n\n\n\n\n")
                findCompletion tmref (pushes, shifts, pops) left right (level+1)
              else do
                DBG.traceM ((show $ fmap reverse allComb) ++ "\n\n\n\n\n\n\n\n\n\n\n\n")
                return allComb

completePush :: (Show state) => STRef s (TraceMap s state) 
             -> Set (StateId state)
             -> Int
             -> (TraceType, StateId state, Stack state, StateId state)
             -> ST.ST s ([TraceChunk state])
completePush _ _ 1 tpl@(mt, q, g, p) = return [[tpl]]
completePush tmref badTpl level tpl@(mt, q, g, p) =
                    if isStateVisited badTpl q
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
                                 combinations <- mapM (completePush tmref (Set.insert q badTpl) (level-1)) (pushes ++ morePushes)
                                 let filtConcCombinations = filter checkTraceConsistency $ filter (not . null) (concat combinations)
                                     newCombinations = fmap (\chunk -> tpl:chunk) filtConcCombinations
                                 --DBG.traceM ((show newCombinations) ++ "\n\n\n\n\n\n\n")
                                 return ([[tpl]] ++ newCombinations)
                                 
{-completeShift :: STRef s (TraceMap s state) -> [TraceChunk state] -> ST.ST s ([TraceChunk state])
completeShift tmref trcpushList = do
                             shiftComb <- mapM (completeShiftInit tmref) trcpushList
                             return (concat shiftComb)-}
                             
completeShiftInit :: STRef s (TraceMap s state) -> StateId state -> StateId state -> TraceChunk state -> ST.ST s ([TraceChunk state])
completeShiftInit tmref pushSt fwdSt trcpush = 
                       do
                         tm <- readSTRef tmref
                         (_, shifts, _) <- MV.read tm (getId pushSt)
                         let matchingTpls = searchTuplesByState shifts fwdSt
                         if null matchingTpls
                           then return [trcpush]
                           else return (fmap (\chunk -> trcpush ++ chunk) (concatMap (completeSingleShift shifts) matchingTpls))
                         
completeSingleShift :: TraceChunk state
                    -> (TraceType, StateId state, Stack state, StateId state)
                    -> [TraceChunk state]
completeSingleShift shifts tpl@(mt, q, g, p) = 
                         let matchingTpls = searchTuplesByState shifts p
                         in if null matchingTpls
                              then [[tpl]]
                              else let combinations = fmap (completeSingleShift shifts) matchingTpls
                                       filtConcCombinations = filter (not . null) (concat combinations)
                                       newCombinations = fmap (\chunk -> tpl:chunk) filtConcCombinations
                                   in newCombinations
                                   
completePop :: (Show state) => STRef s (TraceMap s state) -> StateId state -> TraceChunk state -> ST.ST s ([TraceChunk state])
completePop tmref fwdSt shiftTrc = do
                               --DBG.traceM ((show shiftTrc) ++ "\n\n\n\n\n\n\n")
                               let pushAcc = reverse $ takeWhile (\(mt, q, g, p) -> mt == Push) shiftTrc
                               tm <- readSTRef tmref
                               (_, _, pops) <- MV.read tm (getId (takeStateTuple $ head pushAcc))
                               let matchingTuples = searchTuplesByState pops (takeFwdStateTuple $ last shiftTrc)
                               --DBG.traceM ((show matchingTuples) ++ "\n\n\n\n\n\n\n")
                               combinations <- mapM (completePopFindShift tmref (tail pushAcc) fwdSt) matchingTuples
                               let filtConcCombinations = filter (not . null) (concat combinations)
                               return (fmap (\chunk -> shiftTrc ++ chunk) filtConcCombinations)
                               
completePopFindShift :: (Show state) => STRef s (TraceMap s state) 
                     -> TraceChunk state
                     -> StateId state
                     -> (TraceType, StateId state, Stack state, StateId state)
                     -> ST.ST s ([TraceChunk state])
completePopFindShift _ [] fwdSt tpl@(mt, q, g, p) = if p == fwdSt then return [[tpl]] else return [[]]
completePopFindShift tmref pushAcc@((mtpush, qpush, gpush, ppush):rest) fwdSt tpl@(mt, q, g, p) = do
                      popShiftList <- completeShiftInit tmref qpush p [tpl]
                      --DBG.traceM ((show popShiftList) ++ "\n\n\n\n\n\n\n")
                      --DBG.traceM ((show pushAcc) ++ "\n\n\n\n\n\n\n")
                      combinations <- mapM (findShiftPopComb tmref pushAcc fwdSt) popShiftList
                      let filtConcCombinations = filter (not . null) (concat combinations)
                      return filtConcCombinations
                                                       
findShiftPopComb :: (Show state) => STRef s (TraceMap s state) 
                 -> TraceChunk state
                 -> StateId state
                 -> TraceChunk state
                 -> ST.ST s ([TraceChunk state])
findShiftPopComb tmref ((mtpush, qpush, gpush, ppush):pushAcc) fwdSt miniPopPushTrc = do
                             tm <- readSTRef tmref
                             (_, _, pops) <- MV.read tm (getId qpush)
                             let matchingTpls = searchTuplesByState pops (takeFwdStateTuple $ last miniPopPushTrc)
                             if null matchingTpls
                               then return [[]]
                               else do 
                                      combinations <- mapM (completePopFindShift tmref pushAcc fwdSt) matchingTpls
                                      let filtConcCombinations = filter (not . null) (concat combinations)
                                          newCombinations = fmap (\chunk -> miniPopPushTrc ++ chunk) filtConcCombinations
                                      return newCombinations
                                    
                                    
---------------------------- FUNZIONI AUSILIARIE -----------------------------------                                    

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
                           
isStateVisited :: Set (StateId state) -> StateId state -> Bool
isStateVisited badTpl st = Set.member st badTpl


------------------------- FUNZIONI DI RICERCA TUPLE IN UN TRACECHUNK ------------------------

searchTuples :: TraceChunk state -> StateId state -> TraceChunk state
searchTuples trchunk fwdst = foldr (\(movetype, q, g, p) acc -> if p == fwdst then ((movetype, q, g, p):acc) else acc) [] trchunk

searchTuplesByStack :: TraceChunk state -> StateId state -> TraceChunk state
searchTuplesByStack trchunk prevst = foldr (\(movetype, q, g, p) acc -> if (snd (fromJust g)) == prevst then ((movetype, q, g, p):acc) else acc) [] trchunk

searchTuplesByState :: TraceChunk state -> StateId state -> TraceChunk state
searchTuplesByState trchunk st = foldr (\(movetype, q, g, p) acc -> if q == st then ((movetype, q, g, p):acc) else acc) [] trchunk

searchTuplesForPop :: TraceChunk state -> StateId state -> StateId state -> TraceChunk state
searchTuplesForPop pops fwdStateLeft stateRight = foldr (\(movetype, q, g, p) acc -> if (fwdStateLeft == q) && (p == stateRight) then ((movetype, q, g, p):acc) else acc) [] pops

searchTuplesByIdx :: TraceChunk state -> Int -> TraceChunk state
searchTuplesByIdx trchunk idx = foldr (\(movetype, q, g, p) acc -> if getId p == idx then ((movetype, q, g, p):acc) else acc) [] trchunk


-------- DEBUG ---------------
findAllPop :: STRef s (TraceMap s state) -> ST.ST s (TraceChunk state)
findAllPop tmref = do
                 tm <- readSTRef tmref
                 MV.foldM (\acc (pushes,shifts,pops) -> return (pops ++ acc)) [] tm
                 
findAllShift :: STRef s (TraceMap s state) -> ST.ST s (TraceChunk state)
findAllShift tmref = do
                 tm <- readSTRef tmref
                 MV.foldM (\acc (pushes,shifts,pops) -> return (shifts ++ acc)) [] tm
                 
findAllPush :: STRef s (TraceMap s state) -> ST.ST s (TraceChunk state)
findAllPush tmref = do
                 tm <- readSTRef tmref
                 MV.foldM (\acc (pushes,shifts,pops) -> return (pushes ++ acc)) [] tm
                 
findMatchChunk :: TraceChunk state -> TraceChunk state -> TraceChunk state
findMatchChunk tr1 tr2 = foldr (\(mt1, q1, g1, p1) acc1 -> foldr (\(mt2, q2, g2, p2) acc2 -> if p1 == q2 then ([(mt1, q1, g1, p1)] ++ [(mt2, q2, g2, p2)] ++ acc2) else acc2) acc1 tr2) [] tr1

