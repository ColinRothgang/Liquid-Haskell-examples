module CoreToLH where

import Prelude
import GHC.Core
import qualified Liquid.GHC.Interface() -- show instances for some GHC things.
import GHC.Types.Literal
import GHC.Utils.Outputable
import Data.Bifunctor as B

import qualified LH
import Util

-- Top level binds.
transBind :: Show b => Bind b -> LH.Def
transBind  (NonRec b e) =
  LH.Def (showStripped b) `uncurry` flattenFun e
transBind  (Rec ((b,e): _)) =
  LH.Def (showStripped b) `uncurry` flattenFun e

-- Expressions.
trans :: Show b => Expr b -> LH.Expr
trans (Var id)  | name == "()" = LH.Unit
                | otherwise = LH.Term $ LH.LHVar name
                where name = showStripped id
trans app@App{}
  | name == "***" && qed == LH.LHVar "QED" && typ == typ2 = transEqns firstTerm lastTerm
  | name == "?" = LH.QMark first second
  | name == "patError" = LH.Unit -- patError parts replaced by trivial.
  | name == "()" = LH.Unit
  | otherwise   = LH.Term $ LH.LHApp name (map LH.evaluate args)
  where (name, args)     = flattenApp app
        (_:_:first:second:_) = args
        [typ, eqChain, qed] = map LH.evaluate args
        (LH.LHApp "===" (typ2:firstTerm:[lastTerm])) = eqChain
        
trans l@Lam{}            = error "lambda expression not supported."
trans (Case e b t alts)  = LH.Case (trans  e) (showStripped b) (map altToClause alts)
trans c@Cast{}           = error "cast expression not supported."
trans (Tick tick e)      = trans e -- ignore ticks
trans (Type t)           = LH.Term. LH.LHVar $ showSDocUnsafe (ppr t) -- "[@type]"
trans c@Coercion{}       = error "coercion expression not supported."
trans (Let bind e) =
    case e' of
      Lit{} -> trans e  -- ignore let lit (part of patError)
      _     -> LH.Let (show x) (trans e') (trans e)
  where
    (x, e') = deconstructBind bind
trans (Lit (LitNumber _ n)) = LH.Term . LH.LHSym $ show n 
trans (Lit (LitString s)) = LH.Term . LH.LHSym $ show s
trans (Lit (LitFloat x)) = LH.Term . LH.LHSym $ show x
trans (Lit (LitDouble x)) = LH.Term . LH.LHSym $ show x
-- Deconstruct binds.

deconstructBind :: Bind b -> (b, Expr b)
deconstructBind (Rec ((b,e):_) ) = (b, e)
deconstructBind (NonRec b e)     = (b, e)

-- case-of branches.
altToClause :: Show b => Alt b -> (LH.Pat, LH.Expr)
altToClause (Alt con bs e) = (LH.Pat (go con) (map showStripped bs), trans e)
  where go :: AltCon -> String
        go (DataAlt dc) = showStripped dc
        go (LitAlt lit) = "LitAltTODO"
        go DEFAULT      = "_"

flattenFun :: Show b => Expr b -> ([Id], LH.Expr)
flattenFun (Lam b e) = B.first (showStripped b:) $ flattenFun e
flattenFun e         = ([], trans e)

flattenApp :: Show b => Expr b -> (Id, [LH.Expr])
flattenApp (App f x) = (++ [trans x]) `B.second` flattenApp f
flattenApp (Var name) = (showStripped name, [])
flattenApp t          = error "cannot flatten expr."

flattenQmarks :: LH.Expr -> ([LH.LHExpr], LH.Expr)
flattenQmarks (LH.QMark tm hint) = 
  let (hints, expr) = flattenQmarks tm
  in (LH.evaluate hint:hints, tm)
flattenQmarks expr@LH.Term{} = ([], expr)


transEqns :: LH.LHExpr -> LH.LHExpr -> LH.Expr
transEqns (LH.LHApp "===" (_:nextTerm:[penultimateTerm])) lastTerm =
  let fstTerm = transEqns nextTerm penultimateTerm 
  in LH.Eqn fstTerm [] lastTerm
transEqns (LH.Evaluate qm@(LH.QMark (LH.Term (LH.LHApp "===" _)) _)) lastTerm =
  let 
    (hints, LH.Term (LH.LHApp "===" (_:nextTerm:[penultimateTerm]))) = flattenQmarks qm
    fstTerm = transEqns nextTerm penultimateTerm 
  in LH.Eqn fstTerm hints lastTerm
transEqns (LH.Evaluate qm@(LH.QMark _ _)) lastTerm = 
  let (hints, firstTerm) = flattenQmarks qm in LH.Eqn firstTerm hints lastTerm
transEqns firstTerm lastTerm = LH.Eqn (LH.Term firstTerm) [] lastTerm