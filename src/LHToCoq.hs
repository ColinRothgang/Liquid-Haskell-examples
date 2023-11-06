module LHToCoq (run) where

import Prelude
import GHC.Core
import qualified Liquid.GHC.Interface as LhLib (getTargetInfos)
import qualified Language.Haskell.Liquid.Types as LhLib
import qualified Language.Haskell.Liquid.UX.CmdLine as LhLib (getOpts)
import qualified Data.Map as M
import qualified Data.Bifunctor as B


import qualified CoreToLH as CLH
import qualified LH
import qualified SpecToLH as SLH
import           Simplify (simplify)
import Preamble (preamble)
import Util


run :: [String] -> IO ()
run args = do
    (binds,specs) <- B.first (filter (not . isIgnoredBind)) <$> getBindsAndSpecs args
    let
      specMap = SLH.transSig <$> M.fromList specs
      fileName = last $ split '/' (head args)
      outputPath = "out/"++fileName++".v"
      lhDefs = map CLH.transBind (simplify <$> binds)
      defsAndProofs = parseDefsAndProofs $ pairLHDefsWithSigs lhDefs specMap
      translatedDefsAndProofs = map (B.bimap LH.transDef LH.transLH) defsAndProofs
      translations = map (\v -> case v of { Left x -> show x; Right x -> show x }) translatedDefsAndProofs
      output = intercalate "\n" (preamble++translations)
     
    mapM_ putStrLn preamble
    mapM_ putStrLn translations
    writeFile outputPath output
    

type SpecPair = (Id, LhLib.SpecType)

-- Get the stuff that we need from LH parser, namely: Binds and Specs.
-- @args has the filename inside (and other flags that we might have set).
getBindsAndSpecs :: [String] -> IO ([CoreBind], [SpecPair])
getBindsAndSpecs args = do
    cfg <- LhLib.getOpts args
    (LhLib.TargetInfo src specs:_, _)
      <- LhLib.getTargetInfos Nothing cfg (LhLib.files cfg)
    return (LhLib.giCbs src, getSpecPairs specs)
  where
    getSpecPairs :: LhLib.TargetSpec -> [SpecPair]
    getSpecPairs = map (B.bimap showStripped LhLib.val) . LhLib.gsTySigs . LhLib.gsSig

pairLHDefsWithSigs :: [LH.Def] -> M.Map Id LH.Signature -> [(LH.Def, Maybe LH.Signature)]
pairLHDefsWithSigs defs specMap = map single defs
  where
    single :: LH.Def -> (LH.Def, Maybe LH.Signature)
    single def@(LH.Def id _ _) =  (def, M.lookup id specMap)

parseDefsAndProofs :: [(LH.Def, Maybe LH.Signature)] -> [Either LH.Def LH.Proof]
parseDefsAndProofs = map mapIntoEither
  where
    mapIntoEither (def, Nothing) = Left def
    mapIntoEither (def, Just sig) 
        | LH.isProof sig = Right $ LH.Proof def sig
        | otherwise = Left def

isIgnoredBind :: Show b => Bind b -> Bool
isIgnoredBind bind = name `startsWith` '$' || name == "?"
  where
    name = showStripped $
      case bind of
        NonRec b _    -> b
        Rec ((b,_):_) -> b
    startsWith xs c = c == head xs

