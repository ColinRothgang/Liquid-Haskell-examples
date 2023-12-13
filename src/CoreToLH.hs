{-# LANGUAGE StandaloneDeriving #-}

module CoreToLH where

import Prelude
import GHC.Core
import qualified Liquid.GHC.Interface() -- show instances for some GHC things.
import GHC.Types.Literal
import GHC.Utils.Outputable
import Data.Bifunctor as B
import qualified Data.HashMap.Strict as M

import qualified LH
import Util


import Debug.Trace
import Data.Data

-- Top level binds.
transBind :: Data b => Show b => Bind b -> LH.Def
transBind  (NonRec b e) =
  LH.Def (fixIllegalName $ showStripped b) `uncurry` flattenFun e
transBind  (Rec ((b,e): _)) =
  LH.Def (fixIllegalName $ showStripped b) `uncurry` flattenFun e

-- Expressions.
trans :: Data b => Show b => Expr b -> LH.Expr
trans (Var id)  
  | name == "()" = LH.Unit
  | otherwise = LH.Term $ LH.LHVar name
  where name = fixIllegalName $ showStripped id
                
trans app@App{}
  | name == "***" && qed == LH.LHVar "QED" && typ == typ2 = transEqns firstTerm lastTerm
  | name == "?" = LH.QMark first second
  | name == "patError" = LH.Unit -- patError parts replaced by trivial.
  | name == "()" = LH.Unit
  | name `elem` ["I#", "I"] = singleArg
  | not (null brel) = LH.Term $ LH.Brel (fromJust brel) (LH.evaluate first) (LH.evaluate second)
  | not (null bop) = LH.Term $ LH.Bop (fromJust bop) (LH.evaluate first) (LH.evaluate second)

  | otherwise   = LH.Term $ LH.LHApp name (map LH.evaluate args)
  where (name, args)     = flattenApp app
        [typ, eqChain, qed] = map LH.evaluate args
        (LH.LHApp "===" (typ2:firstTerm:[lastTerm])) = eqChain
        (_:_:first:second:_) = args
        [singleArg] = args
        brel = M.lookup name brels
        bop = M.lookup name bops
        
trans l@Lam{}            = error "lambda expression not supported."
trans (Case e b t alts)  = LH.Case (trans  e) (fixIllegalName $ showStripped b) (map altToClause alts)
trans c@Cast{}           = error $ "cast expression not supported:"++toStr c
trans (Tick tick e)      = trans e -- ignore ticks
trans typ@(Type t)       = LH.Term $ LH.LHVar typRep where
    typRep = (show . constrRep . toConstr) t
trans c@Coercion{}       = error $ "coercion expression not supported: "++toStr c
trans (Let bind e) = 
    case e' of
      Lit{} -> trans e  -- ignore let lit (part of patError)
      _     -> LH.Let (fixIllegalName $ show x) (trans e') (trans e)
  where
    (x, e') = deconstructBind bind
trans (Lit lit) = transLit lit
-- Deconstruct binds.

transLit :: Literal -> LH.Expr
transLit (LitNumber _ n)  = LH.Term (LH.LHIntLit n)
transLit (LitString s)    = LH.Term (LH.LHStringLit $ show s)
transLit (LitFloat x)     = LH.Term (LH.LHFloatLit $ fromRational x)
transLit( LitDouble x)    = LH.Term (LH.LHFloatLit $ fromRational x)

deconstructBind :: Bind b -> (b, Expr b)
deconstructBind (Rec ((b,e):_) ) = (b, e)
deconstructBind (NonRec b e)     = (b, e)

-- case-of branches.
altToClause :: Show b => Data b => Alt b -> (LH.Pat, LH.Expr)
altToClause (Alt con bs e) = (LH.Pat (go con) (map (fixIllegalName . showStripped) bs), trans e)
  where go :: AltCon -> String
        go (DataAlt dc) = fixIllegalName $ showStripped dc
        go (LitAlt lit) = show (transLit lit)
        go DEFAULT      = "_"

flattenFun :: Show b => Data b => Expr b -> ([Id], LH.Expr)
flattenFun (Lam b e) = B.first ((fixIllegalName . showStripped) b:) $ flattenFun e
flattenFun e         = ([], trans e)

flattenApp :: Show b => Data b => Expr b -> (Id, [LH.Expr])
flattenApp (App f x) = (++ [trans x]) `B.second` flattenApp f
flattenApp (Var name) = (fixIllegalName $ showStripped name, [])
flattenApp t          = ("_", [trans t])-- error "cannot flatten expr."

flattenQmarks :: LH.Expr -> ([LH.LHExpr], LH.Expr)
flattenQmarks (LH.QMark tm hint) = 
  let (hints, expr) = flattenQmarks tm
  in (LH.evaluate hint:hints, tm)
flattenQmarks expr@LH.Term{} = ([], expr)

toStr :: Data a => Expr a -> String
toStr x = showConstr (Data.Data.toConstr x)



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





{- The following is based on codeliquidhaskell-boot Transforms/CoreToLogic -}
brels :: M.HashMap String LH.Brel
brels = M.fromList [ ("==", LH.Eq)
                   , ("/=", LH.Neq)
                   , (">=", LH.Geq)
                   , (">" , LH.Gt)
                   , ("<=", LH.Leq)
                   , ("<" , LH.Lt)
                   ]

bops :: M.HashMap String LH.Bop
bops = M.fromList [ ("+", LH.Plus)
                  , ("-", LH.Minus)
                  , ("*", LH.Times)
                  , ("/", LH.Div)
                  , ("/", LH.Div)
                  , ("%", LH.Mod)
                  ]

buildins :: M.HashMap String LH.BuildInTps
buildins = M.fromList[ ("Integer", LH.Integer)
                  , ("Int", LH.Integer)
                  , ("Bool", LH.Boolean)
                  , ("Float", LH.Double)
                  ]

removeIllegalCharacters :: Id -> Id
removeIllegalCharacters = filter (not . (`elem` illegalChars))

illegalChars :: [Char]
illegalChars = ['$','#']

fixIllegalName :: Id -> Id
fixIllegalName n = fromMaybe (removeIllegalCharacters n) (M.lookup n illegalNamesMap)

illegalNamesMap :: M.HashMap String String
illegalNamesMap = M.fromList [
  ("Z", "ZeroN"),
  ("N", "Natural")
  ]