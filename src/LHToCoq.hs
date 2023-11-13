{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module LHToCoq (run) where

import Prelude
import GHC.Core
import qualified Liquid.GHC.Interface as LhLib (getTargetInfos)
import GHC.Types.Var (tyVarName)
import GHC.Types.Name (getOccString)
import qualified Language.Haskell.Liquid.Types as LhLib
import qualified Language.Haskell.Liquid.UX.CmdLine as LhLib (getOpts)
import qualified Language.Fixpoint.Types.Names as F (symbolString)
import qualified Data.Map as M
import qualified Data.HashSet as H
import Data.List
import qualified Data.Bifunctor as B
import GHC.Utils.Outputable
import Control.Monad.Reader
import System.Directory
import System.IO 


import qualified CoreToLH as CLH
import qualified LH
import qualified Coq as C
import qualified SpecToLH as SLH
import           Simplify (simplify)
import Preamble (preamble)
import Util

import Debug.Trace

run :: [String] -> IO ()
run args = do
    (src, binds,specs) <- B.first (filter (not . isIgnoredBind)) <$> getBindsAndSpecs args
    let
      dataDecls = undefined  -- we need to somehow get the data declarations from the LH source as well, but they are not contained in the binds
      specMap = SLH.transSig <$> M.fromList specs
      inputFilePath = split '/' (head args)
      fileName = last inputFilePath 
      inputFolderName = intercalate "/" (init inputFilePath)
    inputFolderPath <- getCurrentDirectory
    let
      inputFolder = inputFolderPath ++ "/" ++ inputFolderName
    putStrLn $ "Input file directory: " ++ inputFolder
    let
      outputPath = "out/"++fileName++".v"
      lhDefs = map CLH.transBind (simplify <$> binds)
      defsAndProofs = parseDefsAndProofs $ pairLHDefsWithSigs lhDefs specMap

    parsedSource <- parseSourceContent (inputFolder, fileName) defsAndProofs src
    let
      Result (state, translatedSourceContent) = translateToCoq parsedSource
      translatedFile = map show translatedSourceContent
      output = intercalate "\n" (preamble++translatedFile)
     
    -- mapM_ (putStrLn . show) dataDecls --(putStrLn . (\x -> showSDocUnsafe $ ppr x)) dataDecls
    -- mapM_ (putStrLn . (\x -> showSDocUnsafe $ ppr x)) binds

    -- mapM_ print lhDefs

    putStrLn $ "\nThe translation to Coq yields: \n" ++ output
    putStrLn $ "Writing output to file at "++outputPath
    writeFile outputPath output

type SpecPair = (Id, LhLib.SpecType)

-- Get the stuff that we need from LH parser, namely: Binds and Specs.
-- @args has the filename inside (and other flags that we might have set).
getBindsAndSpecs :: [String] -> IO (LhLib.TargetSrc, [CoreBind], [SpecPair])
getBindsAndSpecs args = do
    cfg <- LhLib.getOpts args
    (LhLib.TargetInfo src specs:_, _)
      <- LhLib.getTargetInfos Nothing cfg (LhLib.files cfg)
    return (src, LhLib.giCbs src, getSpecPairs specs)
  where
    getSpecPairs :: LhLib.TargetSpec -> [SpecPair]
    getSpecPairs = map (B.bimap showStripped LhLib.val) . LhLib.gsTySigs . LhLib.gsSig

pairLHDefsWithSigs :: [LH.Def] -> M.Map Id LH.Signature -> [(LH.Def, Maybe LH.Signature)]
pairLHDefsWithSigs defs specMap = map single defs
  where
    single :: LH.Def -> (LH.Def, Maybe LH.Signature)
    single def@(LH.Def id _ _) =  (def, M.lookup id specMap)

parseDefsAndProofs :: [(LH.Def, Maybe LH.Signature)] -> [Either (Either LH.Def (LH.Def, LH.Signature)) LH.Proof]
parseDefsAndProofs = map mapIntoEither
  where
    mapIntoEither (def, Nothing) = Left (Left def)
    mapIntoEither (def, Just sig) 
        | LH.isProof sig = Right $ LH.Proof def sig
        | otherwise = Left $ Right (def, sig)

isIgnoredBind :: Show b => Bind b -> Bool
isIgnoredBind bind = name `startsWith` '$' || name == "?"
  where
    name = showStripped $
      case bind of
        NonRec b _    -> b
        Rec ((b,_):_) -> b
    startsWith xs c = c == head xs

parseSourceContent :: (String, String) -> [Either (Either LH.Def (LH.Def, LH.Signature)) LH.Proof] -> LhLib.TargetSrc -> IO [LH.SourceContent]
parseSourceContent (inputFolder, filename) defsAndProofs src = do
    otherFiles <- getDirectoryContents inputFolder
    let
      otherFilePaths = map ((inputFolder  ++ "/") ++) otherFiles 
      sourceFiles = filter (isSuffixOf ".hs") otherFilePaths
    handles <- mapM (`openFile` ReadMode)  sourceFiles
    contents <- mapM hGetContents handles
    let
      fileContents = zip sourceFiles contents
      filteredContents = filter (\(f, content) -> isImported content && not (filename `isSubsequenceOf` f)) fileContents
      imports = map (\(f, _) -> LH.Import f) filteredContents
      nonImports = map parseDefsAndProofs defsAndProofs
      sourceContents = imports ++ nonImports
      sortedSourceContents = sortBy (LH.orderSourceContent identifierOrderSource)
    pure $ imports ++ nonImports
    where 
      identifierOrderSource = map (getOccString . tyVarName) (LhLib.giDefVars src)
      srcImports = H.toList $ LhLib.gsAllImps src
      importNames = map F.symbolString srcImports
      isImported content = any (`isSubsequenceOf` ("module "++content)) importNames
      parseDefsAndProofs (Left def) = parseDef def
      parseDefsAndProofs (Right prf) = parseProof prf
    
data InternalState = State {defSpecs:: [(Id, [C.CoqArg], C.CoqArg)], thmSpecs:: [(Id, [C.CoqArg], C.Prop)], datatypeMeasures:: [(Id, Id)], warnings :: [String]} deriving Show
emptyState :: InternalState
emptyState = State [] [] [] []

concatState :: InternalState -> InternalState -> InternalState
concatState (State dsp1 tsp1 m1 w1) (State dsp2 tsp2 m2 w2)= State (dsp1 ++ dsp2) (tsp1 ++ tsp2) (m1 ++ m2) (w1 ++ w2)

data StateResult a where
  Result :: (InternalState, a) -> StateResult a
deriving instance Show a => Show (StateResult a)
instance Functor StateResult where
  fmap f (Result (state, x)) = Result (state, f x)
instance Applicative StateResult where
  pure x = Result (emptyState, x)
  (<*>) (Result (fState, f)) (Result (xState, x)) = Result (concatState fState xState, f x) 
instance Monad StateResult where
  (>>=) (Result (state, x)) statefulF = Result (concatState state fState, fRes) where
    (Result (fState, fRes)) = statefulF x

registerDefSpecs :: Id -> [C.CoqArg] -> C.CoqArg -> StateResult ()
registerDefSpecs name args ret = Result (State [(name, args, ret)] [] [] [], ())

registerThmSpecs :: Id -> [C.CoqArg] -> C.Prop -> StateResult ()
registerThmSpecs name args claim = Result (State [] [(name, args, claim)] [] [], ())

parseDef :: Either LH.Def (LH.Def, LH.Signature) -> LH.SourceContent
parseDef (Left (LH.Def name [] body)) = LH.Alias name body
parseDef (Left (LH.Def name args body)) | not (null args) = error $ "Found definition (of constant/function \"" ++ name ++ "\") without type specification. This is unsupported by the translation. "
parseDef (Right (LH.Def name args body, LH.Signature sigArgs sigRes)) = LH.Definition name sigArgs sigRes $ runRename body where
      zippedArgLists = zip args sigArgs
      renames = M.fromList $ map (\(n, LH.LHArg argId _ _) -> (n, argId)) zippedArgLists
      runRename = flip runReader renames . LH.renameExpr

parseProof :: LH.Proof -> LH.SourceContent
parseProof (LH.Proof (LH.Def name args body) (LH.Signature sigArgs (LH.LHArg _ _ reft))) = LH.Theorem name sigArgs reft  $ runRename body where
      zippedArgLists = zip args sigArgs
      renames = M.fromList $ map (\(n, LH.LHArg argId _ _) -> (n, argId)) zippedArgLists
      runRename = flip runReader renames . LH.renameExpr

-- TODO: use the state information for refinement checking during translation
-- in particular use it to figure out when we need to inject, project out of/into
-- subset types.
-- Such functionality also allows abbreviating {v: T | True} as T by adding required injections/projections
translateToCoq :: [LH.SourceContent] -> StateResult [C.CoqContent]
translateToCoq srcConts = intercalate [] <$> mapM translate srcConts where
  translate :: LH.SourceContent -> StateResult [C.CoqContent]
  translate (LH.Import moduleName) = pure [C.LoadDeclaration $ C.Load moduleName]
  translate (LH.Data n mO branches) = pure [C.InductiveDeclaration $ C.Inductive n (map translateBranch branches)] where
    translateBranch :: (Id, [LH.Type]) -> (Id, C.Type)
    translateBranch (n, argTps) = 
      let 
        args = map (C.TExpr . LH.transType) argTps
        dom:codom = args
      in (n, foldl C.TFun dom codom)
  translate (LH.Alias n expr) = pure [C.ConstantDeclaration $ C.Const n (LH.transExpr expr)] -- pure ["Definition "++n++" := "++ show expr]
  translate (LH.Definition name args retrf@(LH.LHArg resId ret post) body) = 
    do
      let 
        argNames = map (\(LH.LHArg n _ _) -> n) args 
        coqArgs = map LH.transLHArg args
        renames = M.fromList [(name, unrefName)]
        runRename = flip runReader renames . LH.renameExpr
        unrefinedBody = runRename body
        coqDefinien = LH.transExpr unrefinedBody
        unrefName = C.unrefinedName name
        unrefRet = LH.transLHArg retrf
        unrefinedDef = C.Def unrefName argNames coqDefinien
      registerDefSpecs unrefName coqArgs unrefRet      
      let
        refRet = (resId, C.TExpr $ LH.transType ret, LH.transProp post)
        refinedDef = C.RefDef name coqArgs refRet coqDefinien
      registerDefSpecs name coqArgs refRet
      pure $ map C.DefinitionDeclaration [unrefinedDef, refinedDef]
  translate (LH.Theorem name args lhClaim body) = 
    do
      let
        argNames = map (\(LH.LHArg n _ _) -> n) args 
        coqArgs = map LH.transLHArg args
        claim = LH.transProp lhClaim
        tacs = LH.transformTop (LH.Def name argNames body)
        thm = C.Theorem name coqArgs claim tacs
      registerThmSpecs name coqArgs claim
      pure [C.TheoremDeclaration thm]