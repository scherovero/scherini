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
                 -- , lookup
                 -- , modifyAll
                  , empty
                 -- , unrollTrace
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
       -> TraceType
       -> ST.ST s ()
insert tmref idx trctuple movetype = do
  tm <- readSTRef tmref
  let len = MV.length tm
  if idx < len
    then do
      tl <- MV.unsafeRead tm idx
      let newtuple = insertInTuple tl trctuple movetype
      MV.unsafeWrite tm idx newtuple
    else let newLen = computeLen len idx
             computeLen size newIdx | newIdx < size = size
                                    | otherwise = computeLen (size*2) newIdx
           in do { grown <- MV.grow tm (newLen-len)
                 ; mapM_ (\i -> MV.unsafeWrite grown i ([],[],[])) [len..(newLen-1)]
                 ; let { newtuple = insertInTuple ([],[],[]) trctuple movetype }
                 ; MV.unsafeWrite grown idx newtuple
                 ; writeSTRef tmref grown
                 }
                 
insertInTuple :: (TraceChunk state, TraceChunk state, TraceChunk state) 
              -> (TraceType, StateId state, Stack state, StateId state)
              -> TraceType
              -> (TraceChunk state, TraceChunk state, TraceChunk state)              
insertInTuple (push, shift, pop) trctuple movetype
                  | movetype == Push = (trctuple : push, shift, pop)
                  | movetype == Shift || movetype == Summary = (push, trctuple : shift, pop)
                  | otherwise = (push, shift, trctuple : pop)
                  
-- an empty TraceMap, an array of 3-tuple of empty lists
empty :: ST.ST s (STRef s (TraceMap s state))
empty = do
  tm <- MV.replicate 4 ([],[],[])
  newSTRef tm
                                   
-- insert a Summary trace chunk before a push in the previous chain
{-insertSummary :: STRef s (TraceMap s state) -> StateId state -> Stack state -> ST.ST s ()
insertSummary tmref q g = do
  if isNothing g
    then return ()
    else
      let idx = getId (snd . fromJust $ g)
      in do
        trace <- lookup tmref idx
        if not (null trace)                     --potrebbe essere un controllo inutile perchè se g è nello stack almeno una push l'ha subito e quindi di sicuro è partita la catena
          then insert tmref idx (Summary, q, g)
          else return () 
               
-- extract trace from TraceMap
lookup :: STRef s (TraceMap s state) -> Int -> ST.ST s (TraceId state)
lookup tmref idx = do
  tm <- readSTRef tmref
  if idx < MV.length tm
    then MV.unsafeRead tm idx
    else return []

modifyAll :: (Ord state) => STRef s (TraceMap s state) 
                         -> ((TraceType, StateId state, Stack state) -> (TraceType, StateId state, Stack state)) 
                         -> ST.ST s ()
modifyAll tmref f = do
  tm <- readSTRef tmref
  mapM_ (MV.unsafeModify tm $ map f) [0..((MV.length tm) -1)]

-- an empty TraceMap, an array of empty lists
empty :: ST.ST s (STRef s (TraceMap s state))
empty = do
  tm <- MV.replicate 4 ([],[],[])
  newSTRef tm
  
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

-- complete the trace given substituting recursively the summaries with the saved trace chunks
unrollTrace :: STRef s (TraceMap s state) -> TraceId state -> ST.ST s (TraceId state)
unrollTrace tmref trace = 
  let foldTrace acc sum@(Summary, q, _) = do
        ts <- lookup tmref (getId q)
        --tc <- unrollTrace tmref ts
        return ((reverse ts) ++ acc)
        --lst <- exploreTraceMap tmref
        --lst <- takeChunkTraceMap tmref q sum
        --return (lst ++ acc)
        --tm <- readSTRef tmref
        --tl <- MV.unsafeRead tm 1 
        --return (((sum : tl) ++ [sum]) ++ acc)
      foldTrace acc (moveType, q, g) = do
        return ((moveType, q, g) : acc)
        --return acc 
  in do
    foldM foldTrace [] trace-}                   
