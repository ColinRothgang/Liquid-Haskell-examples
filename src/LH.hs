{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
module LH where

import Prelude
import qualified Coq as C

import qualified Data.Map as M
import Control.Monad.Reader
import Data.List(findIndex)
import Util
import qualified Data.Bifunctor as B

data Proof = Proof Def Signature deriving Show
data Def = Def {defName :: Id, defArgs:: [Id], defBody :: Expr} deriving Show
data Expr = App Id [Expr]
          | Var Id
          | QMark Expr Expr
          | Unit
          | Case Expr Id [(Pat, Expr)]
          | Let Id Expr Expr
          | Sym String
          deriving Show
instance Eq Expr where 
  (==) expr expr2 = show expr == show expr2

data Type = TVar Id | TDat Id [Type] deriving Show

isProof :: Signature -> Bool
isProof = (== "()") . typeName . lhArgType . sigRes
  where
    typeName :: Type -> String
    typeName (TVar n) = n
    typeName (TDat n _) = n

data Pat = Pat {patCon :: Id, patArgs :: [Id]} deriving Show

data LHExpr = And [LHExpr]
            | LHImpl LHExpr LHExpr
            | LHNeg LHExpr
            | Brel Brel LHExpr LHExpr
            | LHApp Id [LHExpr]
            | LHVar Id
            | LHSym String
            deriving Show
instance Eq LHExpr where 
  (==) expr expr2 = show expr == show expr2

data Brel = Eq deriving Show

data LHArg = LHArg { lhArgName :: Id, lhArgType :: Type, lhArgReft :: LHExpr} deriving Show
data Signature = Signature {sigArgs :: [LHArg], sigRes :: LHArg} deriving Show

renameSigArgs :: [Id] -> Signature -> Signature
renameSigArgs args (Signature sArgs res) =
    Signature (map runRename sArgs) (runRename res)
  where
    renames = M.fromList $ zip (map lhArgName sArgs) args
    runRename = flip runReader renames . renameArg


renameArg :: LHArg -> Reader Renames LHArg
renameArg (LHArg name t reft) = LHArg <$> rename name <*> pure t <*> renameReft reft


type Renames = M.Map Id Id

renameReft :: LHExpr -> Reader Renames LHExpr
renameReft (And es)       = And     <$> mapM renameReft es
renameReft (Brel b e1 e2) = Brel b  <$> renameReft e1 <*> renameReft e2
renameReft (LHApp id es)  = LHApp   <$> rename id <*> mapM renameReft es
renameReft (LHVar id)     = LHVar   <$> rename id

renamePat :: Pat -> Reader Renames Pat
renamePat (Pat patCon patArgs) = Pat <$> rename patCon <*> mapM rename patArgs

renameExpr :: Expr -> Reader Renames Expr
renameExpr (App id exprs)       = App   <$> rename id <*> mapM renameExpr exprs
renameExpr (Var id)             = Var   <$> rename id
renameExpr (QMark expr expr2)   = QMark <$> renameExpr expr <*> renameExpr expr2
renameExpr Unit                 = pure Unit
renameExpr (Case expr id branches)  = Case <$> renameExpr expr <*> rename id <*> mapM (\(pat, expr) -> (\x y -> (x,y)) <$> renamePat pat <*> renameExpr expr) branches
renameExpr (Let id expr expr2)  = Let   <$> rename id <*> renameExpr expr <*> renameExpr expr2
renameExpr (Sym s)              = pure $ Sym s

rename :: Id -> Reader Renames Id
rename name = ask <&> (fromMaybe name . M.lookup name)


transLH :: Proof -> C.Theorem
transLH (Proof def@(Def name dArgs body) sig) =
    C.Theorem name args (transResLHArg res) (transformTop def)
  where
    Signature sigArgs res = renameSigArgs dArgs sig
    args = map transLHArg sigArgs

transLHArg :: LHArg -> C.CoqArg
transLHArg (LHArg name ty reft) = (name, C.TExpr $ transType ty, transProp reft)

transResLHArg :: LHArg -> C.Prop
transResLHArg (LHArg _ _ reft) = transProp reft

transType :: Type -> C.Expr
transType (TVar tv) = C.Var tv
transType (TDat con tys) = C.App con $ map transType tys

transPat :: Pat -> C.Pat
transPat (Pat con args) = C.Pat con args

transExpr :: Expr -> C.Expr
transExpr (App f es) = C.App f $ map transExpr es
transExpr (Var x)    = C.Var $ handleId x
  where
    handleId = \case
      "True"  -> "True"
      "False" -> "False"
      other   -> other
transExpr (Let id e1 e2)  = C.Let id (transExpr e1) (transExpr e2)
-- only add match pattern "as b" if match branches use b
transExpr (Case e b bs) | any (\(_, x) -> x `dependsOn` b) bs = C.Match (transExpr e) b $ map (B.bimap transPat transExpr) bs
transExpr (Case e _ bs) = C.MatchSimple (transExpr e) $ map (B.bimap transPat transExpr) bs
transExpr Unit            = C.Var "()"
transExpr (QMark e1 e2)   = C.App "(?)" $ map transExpr [e1,e2]
transExpr (Sym s)         = C.Sym s

transProof :: Expr -> [C.Tactic]
transProof (Var x) = [C.Apply (C.Var x)]
transProof (App f es) = C.Apply (C.App f (map transExpr es')): concatMap transProof ps
    where
      (es', ps) = B.second catMaybes . unzip $ map getQMark es
      getQMark :: Expr -> (Expr, Maybe Expr)
      getQMark (QMark e1 e2) = (e1, Just e2)
      getQMark e             = (e,Nothing)

transProof (QMark e1 e2) = concatMap transProof [e1,e2]
transProof Unit = [C.Trivial]
transProof (Let id e1 e2) = [C.LetTac id (head $ transProof e1) (head $ transProof e2)]
transProof (Case e _ bs) =
    [C.Destruct (transExpr e) (map patArgs pats) (map transProof es)]
  where
    (pats, es) = unzip bs


transBrel :: Brel -> C.Brel
transBrel Eq = C.Eq

transLHExpr :: LHExpr -> C.Expr
transLHExpr (LHApp f es)  = C.App f $ map transLHExpr es
transLHExpr (LHVar x)     = C.Var x
transLHExpr (LHSym s)     = C.Sym s
transLHExpr e             = error "not an expression."

transProp :: LHExpr -> C.Prop
transProp (Brel brel e1 e2)     = C.Brel (transBrel brel) (transLHExpr e1) (transLHExpr e2)
transProp (LHNeg form)          = C.Neg $ transProp form
transProp (And es)              = C.And $ map transProp es
transProp (LHApp f es)          = C.PExpr $ C.App f $ map transLHExpr es
transProp (LHVar x)             = C.PExpr $ C.Var x
transProp (LHImpl ante concl)   = C.Impl (transProp ante) $ transProp concl

data Environment =  Env
  { envName :: Id
  , envArgs :: M.Map Id Int
  , envIndVars :: M.Map Id Int
  } deriving Show

addInd :: Id -> Int -> Environment -> Environment
addInd ind argPos env = env {envIndVars = M.insert ind argPos (envIndVars env)}

askIds :: Reader Environment (M.Map Id Int)
askIds = asks envArgs

checkInductiveCall :: M.Map Id Int -> [(Expr, Int)] -> Maybe Arg
checkInductiveCall _ [] = Nothing
checkInductiveCall indVars allArgs@((Var arg,pos):args) =
  case M.lookup arg indVars of
    Just x | x == pos -> Just (pos,arg)
    _                 -> checkInductiveCall indVars args
checkInductiveCall indVars (_:args) = checkInductiveCall indVars args

transformTop :: Def -> [C.Tactic]
transformTop def@(Def name args e) =
    case runReader (transformInductive e) env of
      Nothing        -> transBranch e
      Just (arg, e') -> transIndDef (Def name args e') arg
  where
    env = Env name (M.fromList $ zip args [0..]) M.empty

type Arg = (Int,Id)
transformInductive :: Expr -> Reader Environment (Maybe (Arg,Expr))
transformInductive (Let x e1 e2) = do
    ind1 <- transformInductive e1
    ind2 <- transformInductive e2
    return $ case ind1 of
                Nothing       -> fmap (Let x e1) <$> ind2
                Just (ind, e) -> Just (ind, Let x e e2)
transformInductive (Case (Var matchId) ident branches) = do
    Env{envName=name, envArgs=args} <- ask
    let n = fromMaybe (error $ "Non-existent id: "++matchId++" in "++intercalate "|" (map (\(id, n) -> id ++ " -> "++ show n) $ M.toList args)) (M.lookup matchId args)
    mInds <- forM branches $ \(Pat con args, e) ->
                case args of
                  []    -> return Nothing
                  {- here we assume that induction happens on the
                  first argument of the constructor. -}
                  (x:_) -> local (addInd x n) (transformInductive e)
    let
      mIdx                = findIndex isJust mInds
      (mIndArg, mIndExpr) = unzipMaybe $ fromJust . (mInds !!) <$> mIdx
      mBranches           = modifyAt branches <$> mIdx <*>
          pure (replaceExprWith (fromJust mIndExpr))
    return $ (,) <$> mIndArg <*> (Case (Var matchId) ident <$> mBranches)
  where
    replaceExprWith :: Expr -> (Pat, Expr) -> (Pat,Expr)
    replaceExprWith e' (pat,e) = (pat,e')
transformInductive app@(App f args) = do
    Env{envName=name, envIndVars=indVars} <- ask
    indFromArgs <- mapM transformInductive args
    let indFromApp = checkInductiveCall indVars (zip args [0..])
    return $
      if f == name then
        fmap (\arg@(pos,_) -> (arg, App f (deleteAt args pos))) indFromApp
      else
        let modifyArg ix = B.second (setAt args ix) . fromJust $ indFromArgs!!ix
        in  fmap (App f) . modifyArg <$> findIndex isJust indFromArgs
transformInductive (QMark e1 e2) = do
    mInd1 <- transformInductive e1
    case mInd1 of
      Just (arg, e1') -> return $ Just (arg, QMark e1' e2)
      Nothing -> do
        mInd2 <- transformInductive e2
        return $ (\ (arg, e2') -> Just (arg, QMark e1 e2')) =<< mInd2
transformInductive _ = return Nothing

transIndDef :: Def -> Arg -> [C.Tactic]
transIndDef (Def name args (Case (Var ind) _ [(_,e1), (_,e2)])) (pos, var) =
    revertArgs ?: [induction [intros ?: transBranch e1, intros ?: transBranch e2]]
  where
    notNullApply :: ([a] -> b) -> [a] -> Maybe b
    notNullApply f args = toMaybe (notNull args) (f args)
    [intros, revertArgs] =
        zipWith notNullApply [C.Intros, C.Revert, C.Revert] [allArgs, nonIndArgs]
    allArgs = nonIndArgs
    nonIndArgs = deleteAt args pos
    induction = C.Induction (args !! pos) var name
transIndDef def _ = error $ "unhandled proof case of " ++ show def

transBranch :: Expr -> [C.Tactic]
transBranch = updateLast C.toSolve . transProof

-- TODO: translate to two definitions in Coq one without refinements and one with that is 
-- specified with refinement and defined (in proof mode) as the one without
transDef :: Either Def (Def, Signature) -> C.Def
transDef (Left (Def name args body)) = C.Def name args (transExpr body)
transDef (Right (Def name args body, Signature sigArgs sigRet)) = C.RefDef name coqArgs coqRet (transExpr body) where
  coqArgs = map transLHArg sigArgs
  coqRet = transLHArg sigRet

class Dependencies a where
  dependsOn:: a -> Id -> Bool

instance Dependencies Type where
  dependsOn (TVar typ) name = typ == name
  dependsOn (TDat typ typArgs) name = (typ == name) || any (`dependsOn` name) typArgs

instance Dependencies LHExpr where
  dependsOn (And exprs) name = any (`dependsOn` name) exprs
  dependsOn (LHImpl expr expr2) name = dependsOn expr name || dependsOn expr2 name
  dependsOn (LHNeg expr) name = dependsOn expr name
  dependsOn (Brel _ expr expr2) name = dependsOn expr name || dependsOn expr2 name
  dependsOn (LHApp id exprs) name = id == name || any (`dependsOn` name) exprs
  dependsOn (LHVar id) name = id == name
  dependsOn (LHSym s) name = False

instance Dependencies Expr where
  dependsOn (App id exprs) name = id == name || any (`dependsOn` name) exprs
  dependsOn (Var id) name = id == name
  dependsOn (QMark expr expr2) name = dependsOn expr name || dependsOn expr2 name
  dependsOn Unit name = False
  dependsOn (Case expr pat branches) name = dependsOn expr name || any (\((Pat patCon patArgs), expr) -> dependsOn expr name || patCon == name || elem name patArgs) branches
  dependsOn (Let id expr expr2) name = dependsOn expr name || dependsOn expr2 name
  dependsOn (Sym s) name = False

instance Dependencies LHArg where
  dependsOn (LHArg id t reft) name = dependsOn t name || dependsOn reft name


{-
data LHProofHint = ProofHint LHExpr
  | Equaltion LHExpr [(Maybe LHProof, LHExpr)]
translateProofHint :: LHProofHint -> [C.Tactic]
translateProofHint (ProofHint LHExpr) = transProof

data SimpleLHProof = Trivial | FurtherHint LHProofHint LHProof
translateProofHints :: SimpleLHProof -> [C.Tactic]
translateProofHints Trivial = [C.Trivial]
translateProofHints (FurtherHint hint prf) = translateProofHint hint ++ translateProofHints prf

data LHProof = SimpleProof SimpleLHProof | InductiveProof Id [(Expr, LHProof)]
translateProofSteps :: LHProof -> [C.Tactic]
translateProofSteps (SimpleProof p) = translateProofHints p
translateProofSteps = undefined

translateTheorem :: Id -> [LHArg] -> LHExpr -> LHProof -> C.Theorem
translateTheorem n args claim p = C.Theorem n (map transLHArg args) (transProp claim) $ translateProofSteps p
-}

class Binder a where
  name :: a -> Id

data SourceContent = Import Id                        -- imported modules
  | Alias Id Expr                                     -- name and definien
  | Data Id (Maybe Id) [(Id, [Type])]                 -- name, (optional) measure, branches (constructor name, argument types)
  | Type Id Type                                      -- name, type it abbreviates
  | Definition Id [LHArg] LHArg Expr                  -- name, arguments (with types), return type, body
  | Theorem Id [LHArg] LHExpr Expr                    -- name, arguments, claim, proof (currently stupid placeholder)
  deriving Show

instance Binder SourceContent where
  name (Import id) = id
  name (Alias id _) = id
  name (Data id _ _) = id
  name (Type id _) = id
  name (Definition id _ _ _) = id
  name (Theorem id _ _ _) = id

instance Eq SourceContent where 
  (==) expr expr2 = name expr == name expr2

instance Dependencies SourceContent where
  dependsOn (Import _) _ = False
  dependsOn (Alias _ expr) name = dependsOn expr name
  dependsOn (Data _ idO constrs) name = idO == Just name || any (\(_, typs) -> any (`dependsOn` name) typs) constrs
  dependsOn (Type _ typ) name = dependsOn typ name
  dependsOn (Definition _ args ret expr) name = any (`dependsOn` name) args || dependsOn ret name || dependsOn expr name
  dependsOn (Theorem _ args ret expr) name = any (`dependsOn` name) args || dependsOn ret name || dependsOn expr name

-- order imports alphabetically, order everything else in dependency order or else in order of given Id list (order in source document), defaulting to LT
orderSourceContent :: [Id] -> SourceContent -> SourceContent -> Ordering
orderSourceContent _ (Import id) (Import id2) = compare id id2
orderSourceContent _ (Import _) _  = LT
orderSourceContent _ srcCont srcCont2 | srcCont == srcCont2 = EQ
orderSourceContent _ srcCont srcCont2 | dependsOn srcCont2 (name srcCont) = LT
orderSourceContent _ srcCont srcCont2 | dependsOn srcCont (name srcCont2) = GT
orderSourceContent idList srcCont srcCont2 = appearsNoLater (name srcCont) (name srcCont2) idList where
    appearsNoLater id id2 [] = LT
    appearsNoLater id id2 (x:xs) | x == id = LT
    appearsNoLater id id2 (x:xs) | x == id2 = GT
    appearsNoLater id id2 (x:xs) = appearsNoLater id id2 xs
