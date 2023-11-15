module SpecToLH where

import Prelude
import Language.Haskell.Liquid.Types
import qualified Language.Fixpoint.Types as F
import qualified Data.Bifunctor as B
import Debug.Trace

import qualified LH
import Util

transCon :: RTyCon -> LH.Type
transCon (RTyCon tc pvars info) = LH.TDat (showppStripped tc) $ map (LH.TVar . showpp) pvars

showppStripped :: PPrint a => a -> String
showppStripped = strip . showpp

-- SpecType = RType RTyCon RTyVar RReft
retType :: SpecType -> LH.LHArg
retType (RFun _ _ _ t_out _) = retType t_out
retType (RImpF _ _ _ t_out _) = retType t_out
retType (RAllT _ _ _) = undefined
retType (RAllP _ _) = undefined
retType t@RApp {} = LH.LHArg "v" `uncurry` trans t
retType (RAllE _ _ _) = undefined
retType (REx _ _ _) = undefined
retType (RExprArg _) = undefined
retType (RAppTy _ _ _) = undefined
retType (RRTy _ _ _ _) = undefined
retType t = error $ "unsupported spec: "++ show t

-- isProof :: SpecType -> Bool
-- isProof t = showppStripped (rt_bind (retType t)) == "()"

transArgs :: SpecType -> [LH.LHArg]
transArgs (RFun id _ t_in t_out _) =
  LH.LHArg (showppStripped id) `uncurry` trans t_in : transArgs t_out
transArgs _ = []

trans :: SpecType -> (LH.Type, LH.LHExpr)
trans (RApp con _ _ reft) = (transCon con, snd $ transRReft reft)
trans sp = error $ "undefined translation from LH SpecType to LH.TypeExpr: \n"
                ++ showpp sp

transRReft :: RReft -> (Id, LH.LHExpr)
transRReft = B.bimap showppStripped transExpr . unreft . ur_reft

unreft (F.Reft t) = t
transExpr :: F.Expr -> LH.LHExpr
transExpr (F.PAtom brel e1 e2)  = LH.Brel (transBrel brel) (transExpr e1) (transExpr e2)
transExpr app@F.EApp{}          = uncurry LH.LHApp $ flattenApp app
transExpr (F.EVar sym)          = LH.LHVar (showppStripped sym)
transExpr (F.PAnd [])           = LH.LHTrue
transExpr (F.PAnd [e])          = transExpr e
transExpr (F.PAnd es)           = LH.And $ map transExpr es
transExpr (F.PIff ante concl)   = LH.LHImpl (transExpr ante) $ transExpr concl
transExpr (F.ESym sym)          = LH.LHSym $ show sym
transExpr (F.ECon c)            = LH.LHSym $ show c
transExpr (F.ENeg form)         = LH.LHNeg $ transExpr form
transExpr e = error $ "undefined expr translation: \n"
                    ++ showpp e

flattenApp :: F.Expr -> (Id, [LH.LHExpr])
flattenApp (F.EApp f x) = (++ [transExpr x]) `B.second` flattenApp f
flattenApp (F.EVar name) = (showppStripped name, [])

transSig :: SpecType -> LH.Signature
transSig f = LH.Signature (transArgs f) (retType f)

transBrel :: F.Brel -> LH.Brel
transBrel F.Eq = LH.Eq
transBrel _    = error "undefined brel translation"