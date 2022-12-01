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
                  , insertSummary
                  , lookup
                  , modifyAll
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
import Pomc.SCCAlgorithm
--import Pomc.SetMap

import Prelude hiding (lookup)
import qualified Control.Monad.ST as ST
import Data.Maybe
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)
import qualified Data.Vector.Mutable as MV
import Data.Set (Set)
import qualified Data.Set as Set

-- Trace data type
data TraceType = Push | Shift | Pop | Summary | Found deriving (Eq, Show)
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
type TraceMap s state = MV.MVector s (TraceId state)

-- append a trace chunk at the corresponding index into TraceMap
insert :: STRef s (TraceMap s state) -> Int -> (TraceType, StateId state, Stack state) -> ST.ST s ()
insert tmref idx trchunk = do
  tm <- readSTRef tmref
  let len = MV.length tm
  if idx < len
    then do
      tl <- MV.unsafeRead tm idx
      MV.unsafeWrite tm idx (trchunk : tl)
      else let newLen = computeLen len idx
               computeLen size newIdx | newIdx < size = size
                                      | otherwise = computeLen (size*2) newIdx
           in do { grown <- MV.grow tm (newLen-len)
                 ; mapM_ (\i -> MV.unsafeWrite grown i []) [len..(newLen-1)]
                 ; MV.unsafeModify grown ((:) trchunk) idx
                 ; writeSTRef tmref grown
                 }
                 
-- insert a Summary trace chunk before a push in the previous chain
insertSummary :: STRef s (TraceMap s state) -> StateId state -> Stack state -> ST.ST s ()
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
  tm <- MV.replicate 4 []
  newSTRef tm
  

unrollTrace :: STRef s (TraceMap s state) -> TraceId state -> TraceId state
unrollTrace tmref trace = foldr foldTrace [] trace
  where foldTrace (moveType, q, g) rest
          | moveType == Summary = 
            let traceSum = ST.runST (lookup tmref (getId q))
            in traceSum ++ rest
          | otherwise = (moveType, q, g) : rest
          
{-unrollTrace :: STRef s (TraceMap s state) -> TraceId state -> ST.ST s (TraceId state)
unrollTrace tmref trace = do
  tr <- lookup tmref 0
  return tr-}
          
{-unrollTrace :: STRef s (TraceMap s state) -> TraceId state -> ST.ST s (TraceId state)
unrollTrace tmref trace = do
  foldr foldTrace [] trace
     where foldTrace acc (moveType, q, g)
       | moveType == Summary = 
          let traceSum = do
              tm <- lookup tmref (getId q)
              return tm
          in (unrollTrace tmref traceSum) ++ acc
       | otherwise = (moveType, q, g) : acc
-}          
