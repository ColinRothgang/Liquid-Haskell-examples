{-# LANGUAGE GADTs #-}

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
import LH
import qualified Coq as C
import qualified SpecToLH as SLH
import           Simplify (simplify)
import Preamble (lhPreamble, preamble)
import Util

import Debug.Trace

run :: [String] -> IO ()
run args = do
    (src, binds,specs) <- B.first (filter (not . isIgnoredBind)) <$> getBindsAndSpecs args
    let
      dataDecls = undefined  -- we need to somehow get the data declarations from the LH source as well, but they are not contained in the binds
      specMap = SLH.transSig <$> M.fromList specs
      inputFilePath = split '/' (head args)
      stripSuffix suf s = maybe s reverse (stripPrefix (reverse suf) (reverse s))
      fileName = last inputFilePath
      filename = stripSuffix ".hs" fileName
      inputFolderName = intercalate "/" (init inputFilePath)
    inputFolderPath <- getCurrentDirectory
    let
      inputFolder = inputFolderPath ++ "/" ++ inputFolderName
    putStrLn $ "\nInput file directory: " ++ inputFolder
    let
      outputPath = "out/"++filename++".v"
      lhDefs = map CLH.transBind (simplify <$> binds)
      defsAndProofs = parseDefsAndProofs $ pairLHDefsWithSigs lhDefs specMap

    parsedSource <- parseSourceContent (inputFolder, fileName) defsAndProofs src
    let
      lhSource = lhPreamble ++ parsedSource
      LH.Result (state, translatedSourceContent) = translateToCoq lhSource
      translatedFile = preamble ++ map show translatedSourceContent
      output = intercalate "\n" translatedFile
     
    -- mapM_ (putStrLn . show) dataDecls --(putStrLn . (showSDocUnsafe . ppr)) dataDecls
    -- mapM_ (putStrLn . (showSDocUnsafe . ppr)) binds
    -- putStrLn ((showSDocUnsafe . ppr) $ head binds)
    -- mapM_ (putStrLn . (\x -> show x)) defsAndProofs


    -- mapM_ print lhDefs
    -- mapM_ print parsedSource

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

pairLHDefsWithSigs :: [Def] -> M.Map Id Signature -> [(Def, Maybe Signature)]
pairLHDefsWithSigs defs specMap = map single defs
  where
    single :: Def -> (Def, Maybe Signature)
    single def@(Def id _ _) =  (def, M.lookup id specMap)

parseDefsAndProofs :: [(Def, Maybe Signature)] -> [Either (Either Def (Def, Signature)) Proof]
parseDefsAndProofs = map mapIntoEither
  where
    mapIntoEither (def, Nothing) = Left (Left def)
    mapIntoEither (def, Just sig) 
        | isProof sig = Right $ Proof def sig
        | otherwise = Left $ Right (def, sig)

isIgnoredBind :: Show b => Bind b -> Bool
isIgnoredBind bind = name `startsWith` '$' || name == "?"
  where
    name = showStripped $
      case bind of
        NonRec b _    -> b
        Rec ((b,_):_) -> b
    startsWith xs c = c == head xs

parseSourceContent :: (String, String) -> [Either (Either Def (Def, Signature)) Proof] -> LhLib.TargetSrc -> IO [SourceContent]
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
      importedFiles = map (getModuleName . fst) filteredContents
      imports = map Import importedFiles
      nonImports = map parseDefsAndProofs defsAndProofs
      sourceContents = imports ++ nonImports
      sortedSourceContents = sortBy (orderSourceContent identifierOrderSource) sourceContents
    pure sortedSourceContents
    where 
      identifierOrderSource = map (getOccString . tyVarName) (LhLib.giDefVars src)
      srcImports = H.toList $ LhLib.gsAllImps src
      importNames = map F.symbolString srcImports
      isImported content = any (`isSubsequenceOf` ("module "++content)) importNames
      parseDefsAndProofs (Left def) = parseDef def
      parseDefsAndProofs (Right prf) = parseProof prf
      getModuleName :: String -> String
      getModuleName s = intercalate "." (init $ split '.' (last $ split '/' s))

parseDef :: Either Def (Def, Signature) -> SourceContent
parseDef (Left (Def name [] body)) = Alias name body
parseDef (Left (Def name args body)) | not (null args) = error $ "Found definition (of constant/function \"" ++ name ++ "\") without type specification. This is unsupported by the translation. "
parseDef (Right (Def name args body, Signature sigArgs sigRes)) = Definition name sigArgs sigRes $ runRename body where
      zippedArgLists = zip args sigArgs
      renames = M.fromList $ map (\(n, LHArg argId _ _) -> (n, argId)) zippedArgLists
      runRename = flip runReader renames . renameExpr

parseProof :: Proof -> SourceContent
parseProof (Proof (Def name args body) (Signature sigArgs (LHArg _ _ reft))) = Theorem name sigArgs reft  $ runRename body where
      zippedArgLists = zip args sigArgs
      renames = M.fromList $ map (\(n, LHArg argId _ _) -> (n, argId)) zippedArgLists
      runRename = flip runReader renames . renameExpr

-- TODO: use the state information for refinement checking during translation
-- in particular use it to figure out when we need to inject, project out of/into
-- subset types.
-- Such functionality also allows abbreviating {v: T | True} as T by adding required injections/projections
translateToCoq :: [SourceContent] -> StateResult [C.CoqContent]
translateToCoq srcConts = 
  let 
    smap :: [SourceContent] -> (StateResult SourceContent -> StateResult [C.CoqContent]) -> StateResult [C.CoqContent]
    smap [] _       = pure []
    smap [x] trans  = trans (pure x)
    smap (x:xs) trans = foldl combine init xs where
      init = trans (pure x)
      combine (Result (s, ys)) x = let Result (t, y) = trans (Result (s,x)) in Result (s `concatState` t, ys ++ y)
  
  in smap srcConts translate where
  translate :: StateResult SourceContent -> StateResult [C.CoqContent]
  translate (Result (state, Import moduleName)) = pure [C.LoadDeclaration $ C.Load moduleName]
  translate (Result (s, Data n mO branches)) = mapM (translateBranch n s) branches >>= (\br -> pure [C.InductiveDeclaration $ C.Inductive n br]) where
    translateBranch :: Id -> InternalState -> (Id, [Type]) -> StateResult (Id, C.Type)
    translateBranch n s (bn, argTps) = 
      do
        registerDataDefSpecs bn coqArgs (bn, ret, C.TT)

        pure (bn, funcTyp)
        where
          argsT = map (C.TExpr . transType s) argTps
          coqArgs = zipWith (\i x -> ("x"++show i, x, C.TT)) [1..] argsT
          ret = C.TExpr $ C.Var n
          funcTyp = transFuncType s argsT ret
          
  translate (Result (s,Alias n expr)) = pure [C.ConstantDeclaration $ C.Const n (transExpr s expr)]
  translate (Result (s, Definition name args retrf@(LHArg resId ret post) body)) = 
    let 
      argNames = map (\(LHArg n _ _) -> n) args
      renames = M.fromList [(name, unrefName)]
      runRename = flip runReader renames . renameExpr
      unrefinedBody = runRename body
      coqArgs = map (transLHArg s) args
      unrefName = C.unrefinedName name
      unrefRet = transLHArg s retrf
      unrefDefState = State [(unrefName, coqArgs, Left unrefRet)] [] [] [] DefProofMode
      definModeS = s `concatState` unrefDefState
      coqDefinien = transformTop definModeS (Def unrefName argNames unrefinedBody)
      unrefinedDef = C.SpecDef unrefName coqArgs unrefRet coqDefinien

      defnState = definModeS `concatState` definitionModeState
      unrefAppl = refineApplyArg defnState unrefName coqArgs
      unrefApply = LH.projectIfNeeded defnState unrefAppl
      postRef = C.Brel C.Eq unrefApply (LH.projectIfNeeded defnState $ C.Var resId)
      refRet = let (resId, typ, _) = unrefRet in (resId, typ, postRef)
      refDefState = State [(name, coqArgs, Left refRet)] [] [] [] DefinitionSpecMode
      refinedDef = C.RefDef name coqArgs refRet (C.fromSpecs [(unrefName, coqArgs, Left unrefRet), (name, coqArgs, Left refRet)])
    in Result (unrefDefState `concatState`  refDefState, map C.DefinitionDeclaration [unrefinedDef, refinedDef])
  translate (Result (s,Theorem name args lhClaim body)) = 
    let
      argNames = map (\(LHArg n _ _) -> n) args 
      coqArgs = map (transLHArg s) args
      claimTransState = s `concatState` State [(name, coqArgs, Right C.TT)] [] [] [] DefinitionMode
      claim = transProp claimTransState lhClaim
      prfState = State [(name, coqArgs, Right claim)] [] [] [] ProofMode
      proofModeS = s `concatState` prfState
      tacs = transformTop proofModeS (Def name argNames body)
      thm = C.Theorem name coqArgs claim tacs
    in Result (prfState `concatState` definitionModeState, [C.TheoremDeclaration thm])