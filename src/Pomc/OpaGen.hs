{- |
   Module      : Pomc.OpaGen
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.OpaGen ( FunctionSkeleton(..)
                   , Statement(..)
                   , FunctionName
                   , skeletonsToOpa
                   ) where

import Pomc.Prop (Prop(..))
import Pomc.ModelChecker (ExplicitOpa(..))
import Pomc.Example (stlPrecRelV2Text, stlPrecV2slsText)

import System.Random
import System.IO
import System.FilePath ((</>))
import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (isNothing, fromJust)

type FunctionName = Text
data Statement = Call FunctionName
               | TryCatch [Statement] [Statement]
               | IfThenElse [Statement] [Statement]
               | Throw deriving Show
data FunctionSkeleton = FunctionSkeleton { skName :: FunctionName
                                         , skStmts ::[Statement]
                                         } deriving Show


genIndices :: RandomGen g => g -> Int -> Int -> ([Int], g)
genIndices gen maxNum maxIndex =
  let (num, gen') = randomR (0, maxNum) gen
  in (iterate genIndex ([], gen')) !! num
  where genIndex (indices, oldGen) =
          let (idx, newGen) = randomR (0, maxIndex) oldGen
          in (idx : indices, newGen)

genFunctionSkeleton :: RandomGen g
                    => g
                    -> [FunctionName]
                    -> Int
                    -> Int
                    -> FunctionName
                    -> (FunctionSkeleton, g)
genFunctionSkeleton gen fs maxCalls maxDepth fname =
  let (statements, gen') = genBlock gen fs maxCalls maxDepth [genTryCatch, genIfThenElse, genThrow]
  in (FunctionSkeleton fname statements, gen')

genBlock :: RandomGen g
         => g
         -> [FunctionName]
         -> Int
         -> Int
         -> [g -> [FunctionName] -> Int -> Int -> (Statement, g)]
         -> ([Statement], g)
genBlock gen fs maxCalls maxDepth stmtGens =
  foldl createStatements ([], gen') stmtIndices
  where (stmtIndices, gen') = genIndices gen maxCalls (length fs + length stmtGens - 1)
        createStatements (stmts, oldGen) idx
          | idx < length fs || maxDepth == 0 = ((Call (fs !! (idx `mod` length fs))) : stmts, oldGen)
          | otherwise = let (tcStmt, newGen) = (stmtGens !! (idx - length fs)) oldGen fs maxCalls (maxDepth-1)
                        in (tcStmt : stmts, newGen)

genTryCatch :: RandomGen g => g -> [FunctionName] -> Int -> Int -> (Statement, g)
genTryCatch gen fs maxCalls maxDepth =
  let (try, gen') = genBlock gen fs maxCalls maxDepth [genIfThenElse, genThrow]
      (catch, gen'') = genBlock gen' fs maxCalls maxDepth [genIfThenElse]
  in (TryCatch try catch, gen'')

genIfThenElse :: RandomGen g => g -> [FunctionName] -> Int -> Int -> (Statement, g)
genIfThenElse gen fs maxCalls maxDepth =
  let (thenBlock, gen') = genBlock gen fs maxCalls maxDepth [genTryCatch, genIfThenElse, genThrow]
      (elseBlock, gen'') = genBlock gen' fs maxCalls maxDepth [genTryCatch, genIfThenElse, genThrow]
  in (IfThenElse thenBlock elseBlock, gen'')

genThrow :: RandomGen g => g -> [FunctionName] -> Int -> Int -> (Statement, g)
genThrow gen _ _ _ = (Throw, gen)

genSkeletons :: RandomGen g => g -> Int -> Int -> Int -> ([FunctionSkeleton], g)
genSkeletons gen nf maxCalls maxDepth = foldl foldSkeletons ([], gen) fs
  where fs = map (\n -> T.pack $ "p" ++ show n) [nf, nf-1 .. 0]
        foldSkeletons (sks, oldGen) fname =
          let (sk, newGen) = genFunctionSkeleton oldGen fs maxCalls maxDepth fname
          in (sk : sks, newGen)


printFunctions :: Int -> Int -> Int -> IO ()
printFunctions nf maxCalls maxDepth = do
  gen <- newStdGen
  (skeletons, _) <- return $ genSkeletons gen nf maxCalls maxDepth
  putStrLn $ show skeletons
  let opa = skeletonsToOpa skeletons
  putStrLn $ show opa
  hWriteOpa opa stdout


skeletonsToOpa :: [FunctionSkeleton] -> ExplicitOpa Word Text
skeletonsToOpa sks = ExplicitOpa
  { sigma = (stlPrecV2slsText, map (Prop . skName) sks)
  , precRel = stlPrecRelV2Text
  , initials = [0]
  , finals = [1]
  , deltaPush = toListDelta $ dPush''
  , deltaShift = toListDelta $ lsDShift lowerState
  , deltaPop = toListDelta $ dPop'''
  }
  where lowerState = lowerFunction sksMap (LowerState M.empty M.empty M.empty M.empty 3) (head sks)
        sksMap = M.fromList $ map (\sk -> (skName sk, sk)) sks
        toListDelta deltaMap = map (\((a, b), dt) -> (a, b, resolveTarget dt)) $ M.toList deltaMap
        firstFname = skName $ head sks
        firstFinfo = fromJust $ M.lookup firstFname (lsFinfo lowerState)
        dPush' = M.insert (0, makeInputSet [T.pack "call", firstFname])
                 (EntryStates firstFname) (lsDPush lowerState)
        dPop' = M.insert (fiRetPad firstFinfo, 0) (States [1]) (lsDPop lowerState)
        dPop'' = M.insert (fiThrow firstFinfo, 0) (States [2]) dPop'
        dPush'' = M.insert (2, makeInputSet [T.pack "exc"]) (States [1]) dPush'
        dPop''' = M.insert (1, 2) (States [1]) dPop''

        resolveTarget (EntryStates fname) =
          fiEntry . fromJust $ M.lookup fname (lsFinfo lowerState)
        resolveTarget (States s) = s

data DeltaTarget = EntryStates Text | States [Word]

data FunctionInfo = FunctionInfo { fiName :: Text
                                 , fiEntry :: [Word]
                                 , fiRetPad :: Word
                                 , fiThrow :: Word
                                 , fiExcPad :: Word
                                 }
data LowerState = LowerState { lsDPush :: Map (Word, Set (Prop Text)) DeltaTarget
                             , lsDShift :: Map (Word, Set (Prop Text)) DeltaTarget
                             , lsDPop :: Map (Word, Word) DeltaTarget
                             , lsFinfo :: Map Text FunctionInfo
                             , lsSid :: Word
                             }

-- Thunk that links a list of states as the successors of the previous statement(s)
type PredLinker = LowerState -> [Word] -> LowerState

dInsert :: (Ord k) => k -> [Word] -> Map k DeltaTarget -> Map k DeltaTarget
dInsert _ [] delta = delta
dInsert key states delta =
  case M.lookup key delta of
    Nothing            -> M.insert key (States states) delta
    Just (States olds) -> M.insert key (States $ olds ++ states) delta
    _                  -> error "DeltaTarget mismatch."

lowerFunction :: Map Text FunctionSkeleton
              -> LowerState
              -> FunctionSkeleton
              -> LowerState
lowerFunction sks lowerState0 fsk =
  let sidRet = lsSid lowerState0
      thisFinfo = FunctionInfo (skName fsk) [] (sidRet + 1) (sidRet + 2) (sidRet + 3)
      lowerState1 = lowerState0 {
        lsFinfo = M.insert (skName fsk) thisFinfo (lsFinfo lowerState0)
        , lsSid = sidRet + 4
        }
      addEntry ls es =
        let tfinfo = fromJust $ M.lookup (skName fsk) (lsFinfo ls)
            finfo1 = M.insert (skName fsk) (tfinfo { fiEntry = (fiEntry tfinfo) ++ es }) (lsFinfo ls)
        in ls { lsFinfo = finfo1 }

      (lowerState2, linkPred) = lowerBlock sks lowerState1 thisFinfo addEntry (skStmts fsk)

      dShift' = M.insert (sidRet, makeInputSet [T.pack "ret", skName fsk])
                 (States [fiRetPad thisFinfo]) (lsDShift lowerState2)
      dShift'' = M.insert (fiThrow thisFinfo, makeInputSet [T.pack "exc"])
                 (States [fiExcPad thisFinfo]) dShift'
  in linkPred (lowerState2 { lsDShift = dShift'' }) [sidRet]

lowerStatement :: Map Text FunctionSkeleton
               -> LowerState
               -> FunctionInfo
               -> PredLinker
               -> Statement
               -> (LowerState, PredLinker)
lowerStatement sks lowerState0 thisFinfo linkPred (Call fname) =
  let callSid = lsSid lowerState0
      calleeFinfo0 = M.lookup fname $ lsFinfo lowerState0
      lowerState1 = lowerState0 { lsSid = callSid + 1 }
      lowerState2 = if isNothing calleeFinfo0
                    then lowerFunction sks lowerState1 (fromJust $ M.lookup fname sks)
                    else lowerState1
      calleeFinfo1 = fromJust $ M.lookup fname (lsFinfo lowerState2)
      dPush'' = M.insert (callSid, makeInputSet [T.pack "call", fname])
                (EntryStates fname) (lsDPush lowerState2)
      dPop'' = M.insert (fiThrow calleeFinfo1, callSid)
               (States [fiThrow thisFinfo]) (lsDPop lowerState2)

      linkCall lowerState successorStates =
          let dPop' = dInsert (fiRetPad calleeFinfo1, callSid) successorStates (lsDPop lowerState)
          in lowerState { lsDPop = dPop' }

  in ( linkPred (lowerState2 { lsDPush = dPush'', lsDPop = dPop'', lsSid = lsSid lowerState2 + 1}) [callSid]
     , linkCall )

lowerStatement sks ls0 thisFinfo linkPred0 (TryCatch try catch) =
  let hanSid = lsSid ls0
      dummySid0 = hanSid + 1
      dummySid1 = dummySid0 + 1
      ls1 = linkPred0 (ls0 { lsSid = dummySid1 + 1 }) [hanSid]

      linkHandler lowerState successorStates =
        let dPushH = dInsert (hanSid, makeInputSet [T.pack "han"])
                     successorStates (lsDPush lowerState)
        in lowerState { lsDPush = dPushH }

      (ls2, linkPredTry) = lowerBlock sks ls1 thisFinfo linkHandler try
      -- add dummy exc to exit try block
      ls3 = linkPredTry ls2 [dummySid0]
      dShift' = M.insert (dummySid0, makeInputSet [T.pack "exc"])
                (States [dummySid1]) (lsDShift ls3)
      ls4 = ls3 { lsDShift = dShift' }

      linkTry lowerState successorStates =
        let dPopD = dInsert (dummySid1, hanSid) successorStates (lsDPop lowerState)
        in lowerState { lsDPop = dPopD }

      linkCatch lowerState successorStates =
        let dPopC = dInsert (fiExcPad thisFinfo, hanSid) successorStates (lsDPop lowerState)
        in lowerState { lsDPop = dPopC }

      (ls5, linkPredCatch) = lowerBlock sks ls4 thisFinfo linkCatch catch

      linkTryCatch ls succStates = linkPredCatch (linkTry ls succStates) succStates
  in (ls5, linkTryCatch)

lowerStatement sks ls0 thisFinfo linkPred0 (IfThenElse thenBlock elseBlock) =
  let (ls1, linkPred1) = lowerBlock sks ls0 thisFinfo linkPred0 thenBlock
      (ls2, linkPred2) = lowerBlock sks ls1 thisFinfo linkPred0 elseBlock
      linkPredITE lowerState succStates = linkPred2 (linkPred1 lowerState succStates) succStates
  in (ls2, linkPredITE)

lowerStatement _ lowerState thisFinfo linkPred Throw =
  (linkPred lowerState [fiThrow thisFinfo], (\ls _ -> ls))

lowerBlock :: Map Text FunctionSkeleton
           -> LowerState
           -> FunctionInfo
           -> PredLinker
           -> [Statement]
           -> (LowerState, PredLinker)
lowerBlock _ lowerState _ linkPred [] = (lowerState, linkPred)
lowerBlock sks lowerState thisFinfo linkPred block =
  foldBlock lowerState linkPred block
  where foldBlock lowerState1 linkPred1 [] = (lowerState1, linkPred1)

        foldBlock lowerState1 linkPred1 (Throw : _) =
          let (lowerState2, linkPred2) =
                lowerStatement sks lowerState1 thisFinfo linkPred1 Throw
          in (lowerState2, linkPred2)

        foldBlock lowerState1 linkPred1 (stmt : stmts) =
          let (lowerState2, linkPred2) =
                lowerStatement sks lowerState1 thisFinfo linkPred1 stmt
          in foldBlock lowerState2 linkPred2 stmts


insertAll :: Ord k => [(k, v)] -> Map k v -> Map k v
insertAll kvPairs m = m `M.union` M.fromList kvPairs

makeInputSet :: (Ord a) => [a] -> Set (Prop a)
makeInputSet ilst = S.fromList $ map Prop ilst


genOpa :: String -> Int -> Int -> Int -> IO ()
genOpa file nf maxCalls maxDepth = do
  gen <- newStdGen
  (skeletons, _) <- return $ genSkeletons gen nf maxCalls maxDepth
  opa <- return $ skeletonsToOpa skeletons
  withFile file WriteMode (hWriteOpa opa)

genBench :: String -> IO ()
genBench dir = do
  gen <- newStdGen
  _ <- foldM genSomeOpa gen [4..36]
  return ()
  where genSomeOpa gen maxCalls = foldM genSingleOpa gen [1..8]
          where genSingleOpa :: RandomGen g => g -> Int -> IO (g)
                genSingleOpa gen' n = do
                  (skeletons, gen'') <- return $ genSkeletons gen' (maxCalls `div` 4) maxCalls 4
                  opa <- return $ skeletonsToOpa skeletons
                  withFile (dir </> (show maxCalls ++ "-" ++ show n ++ ".pomc"))
                    WriteMode (hWriteOpa opa)
                  return gen''


hWriteOpa :: (Show s, Show a) => ExplicitOpa s a -> Handle -> IO ()
hWriteOpa opa h = do
  hPutStrLn h evalHeader
  hPutStrLn h $ "  initials = " ++ formatList (map show $ initials opa) ++ ";"
  hPutStrLn h $ "  finals = " ++ formatList (map show $ finals opa) ++ ";"
  hPutStrLn h $ "  deltaPush = " ++ formatDeltaInput (deltaPush opa) ++ ";"
  hPutStrLn h $ "  deltaShift = " ++ formatDeltaInput (deltaShift opa) ++ ";"
  hPutStrLn h $ "  deltaPop = " ++ formatDeltaPop (deltaPop opa) ++ ";"

formatList :: [String] -> String
formatList [] = ""
formatList (x : []) = x
formatList (x : xs) = foldl (\acc y -> acc ++ " " ++ y) ("(" ++ x) xs ++ ")"

formatDeltaInput :: (Show s, Show a) => [(s, Set (Prop a), [s])] -> String
formatDeltaInput di = formatDeltaList $ map formatRel di
  where formatRel (q, b, ps) =
          "(" ++ show q ++ ", " ++ formatPropSet b ++ ", " ++ formatStateList ps ++ ")"
        formatPropSet b = formatList $ map unProp (S.toList b)

        unProp (Prop p) = show p
        unProp End = "#"

formatDeltaPop :: (Show s) => [(s, s, [s])] -> String
formatDeltaPop dp = formatDeltaList $ map formatRel dp
  where formatRel (q, r, ps) =
          "(" ++ show q ++ ", " ++ show r ++ ", " ++ formatStateList ps ++ ")"

formatDeltaList :: [String] -> String
formatDeltaList [] = ""
formatDeltaList (x : []) = x
formatDeltaList (x : xs) = foldl (\acc rel -> acc ++ ", " ++ rel) x xs

formatStateList :: (Show s) => [s] -> String
formatStateList sl = formatList $ map show sl

evalHeader :: String
evalHeader =
  "prec = Mcall;\n\
  \\n\
  \formulas = PNd (PNd (call And (XNu exc))),\
  \\n           PNd (han And (XNd (exc And (XBu call)))),\
  \\n           G (exc --> XBu call),\
  \\n           T Ud exc,\
  \\n           F (HNd p1),\
  \\n           F (HBd p2),\
  \\n           G ((call And p0) --> (~ p1) HUu p2),\
  \\n           F (HNu p1),\
  \\n           F (HBu p1),\
  \\n           F (p0 And (call HUu p1)),\
  \\n           F (p1 And (call HSu p0)),\
  \\n           G (call --> XNd ret),\
  \\n           G (call --> Not (PNu exc)),\
  \\n           G ((call And p0) --> ~ (PNu exc Or XNu exc)),\
  \\n           G (exc --> ~ (PBu (call And p0) Or XBu (call And p0))),\
  \\n           G ((call And p2 And (call Sd (call And p1))) --> (PNu exc Or XNu exc)),\
  \\n           G (han --> XNu ret),\
  \\n           G (call And p2 --> (T Uu (exc And XBd han))),\
  \\n           call Ud (ret And p1),\
  \\n           XNd (call And ((call Or exc) Su p0));\
  \\n\
  \\nopa:"
