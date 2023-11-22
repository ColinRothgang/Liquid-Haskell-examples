{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

module LH where

import Prelude
import qualified Coq as C

import qualified Data.Map as M
import Control.Monad.Reader
import Data.List(findIndex,find, stripPrefix)
import Util
import qualified Data.Bifunctor as B
import Debug.Trace

data Proof = Proof Def Signature deriving Show
data Def = Def {defName :: Id, defArgs:: [Id], defBody :: Expr} deriving Show
data Expr = Term LHExpr
          | QMark Expr Expr
          | Eqn Expr [LHExpr] LHExpr
          | Unit
          | Case Expr Id [(Pat, Expr)]
          | Let Id Expr Expr
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
            | Evaluate Expr
            | LHTrue
            deriving Show
instance Eq LHExpr where 
  (==) expr expr2 = show expr == show expr2

evaluate :: Expr -> LHExpr
evaluate (Term t) = t
evaluate expr = Evaluate expr

unevaluate :: LHExpr -> Expr
unevaluate (Evaluate expr) = expr
unevaluate tm = Term tm 

data Brel = Eq deriving Show

data LHArg = LHArg { lhArgName :: Id, lhArgType :: Type, lhArgReft :: LHExpr} deriving Show
data Signature = Signature {sigArgs :: [LHArg], sigRes :: LHArg} deriving Show

data TranslationMode = DefinitionMode | ProofMode | DefProofMode deriving (Eq, Show)
data InternalState = State {defSpecs:: [(Id, [C.CoqArg], C.CoqArg)], thmSpecs:: [(Id, [C.CoqArg], C.Prop)], datatypeMeasures:: [(Id, Id)], warnings :: [String], mode :: TranslationMode} deriving Show
emptyState :: InternalState
emptyState = State [] [] [] [] DefinitionMode

concatState :: InternalState -> InternalState -> InternalState
concatState (State dsp1 tsp1 m1 w1 _) (State dsp2 tsp2 m2 w2 f)= State (dsp1 ++ dsp2) (tsp1 ++ tsp2) (m1 ++ m2) (w1 ++ w2) f

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
registerDefSpecs name args ret = Result (State [(name, args, ret)] [] [] [] DefinitionMode, ())

registerThmSpecs :: Id -> [C.CoqArg] -> C.Prop -> StateResult ()
registerThmSpecs name args claim = Result (State [] [(name, args, claim)] [] [] ProofMode, ())

definitionModeState = State [] [] [] [] DefinitionMode
registerDefinitionMode = Result (definitionModeState, ())
registerProofMode = Result (State [] [] [] [] ProofMode, ())
registerDefProofMode = Result (State [] [] [] [] DefProofMode, ())

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
renameReft (Evaluate expr)= Evaluate<$> renameExpr expr 
renameReft (LHImpl e1 e2) = LHImpl  <$> renameReft e1 <*> renameReft e2
renameReft (LHNeg e)      = LHNeg   <$> renameReft e
renameReft (LHSym s)      = pure $ LHSym s
renameReft LHTrue         = pure LHTrue

renamePat :: Pat -> Reader Renames Pat
renamePat (Pat patCon patArgs) = Pat <$> rename patCon <*> mapM rename patArgs

renameExpr :: Expr -> Reader Renames Expr
renameExpr (Term lhExpr)        = Term  <$> renameReft lhExpr
renameExpr (Eqn expr hintO tm)  = Eqn   <$> renameExpr expr <*> mapM renameReft hintO <*> renameReft tm
renameExpr (QMark expr expr2)   = QMark <$> renameExpr expr <*> renameExpr expr2
renameExpr Unit                 = pure Unit
renameExpr (Case expr id branches)  = Case <$> renameExpr expr <*> rename id <*> mapM (\(pat, expr) -> (,) <$> renamePat pat <*> renameExpr expr) branches
renameExpr (Let id expr expr2)  = Let   <$> rename id <*> renameExpr expr <*> renameExpr expr2

rename :: Id -> Reader Renames Id
rename name = asks (fromMaybe name . M.lookup name)

refineApplyWrapper :: Show a => (a-> C.Expr) -> (InternalState -> Id -> a -> Bool) -> InternalState -> Id -> [a] -> C.Expr
refineApplyWrapper transTm isSubsetTerm s = C.refineApplyGeneric (allSpecs s) transTm isSubsetTm where
  allSpecs s = map (\(x,y,_) -> (x,y)) (defSpecs s) ++ map (\(x,y,_) -> (x,y)) (thmSpecs s)
  isSubsetTm _ = isSubsetTerm s

-- TODO: improve treatment of nested Subset types
isSubsetTermExpr :: InternalState -> Id -> C.Expr -> Bool
isSubsetTermExpr s id (C.Inject (C.RExpr _ _ C.TT) x _) = isSubsetTermExpr s id x
isSubsetTermExpr s id (C.Project (C.Inject typ x prf)) = isSubsetTermExpr s id x
isSubsetTermExpr _ _ C.Inject {} = True
isSubsetTermExpr s _ exp@(C.App n exprs) | not $ null (find (\(x, _, _) -> x == n && n /= "") $ defSpecs s) = 
  let
    funSpec = fromJust $ find (\(x,_, _) -> x == n && n /= "") (defSpecs s)
    (_, _, (_, _, prop)) = funSpec
  in {-trace ("the refinement of "++show exp ++ " is: "++ show prop) $-} prop /= C.TT
isSubsetTermExpr s _  _| mode s == ProofMode = False
isSubsetTermExpr s _  _| mode s == DefProofMode = False
isSubsetTermExpr s id exp@(C.Var n) = 
  let
    funcSpec = snd <$> find (\(x,_) -> x == id && id /= "") (map (\(x,y,_) -> (x,y)) (defSpecs s) ++ map (\(x,y,_) -> (x,y)) (thmSpecs s))
    argSpec = find (\(x,_,_) -> x == n) =<< funcSpec
  in not (null argSpec) && C.isSubsetTermCoqArg (fromJust argSpec)
isSubsetTermExpr _ _ _ = False

refineApplyArg :: InternalState -> Id -> [C.CoqArg] -> C.Expr
refineApplyArg = refineApplyWrapper transTm (\_ _ -> C.isSubsetTermCoqArg) where
  transTm :: C.CoqArg -> C.Expr
  transTm (n, typ, ref) = C.Var n

refineApply :: InternalState -> Id -> [C.Expr] -> C.Expr
refineApply = refineApplyWrapper id isSubsetTermExpr

refineApplyLH :: InternalState -> Id -> [LHExpr] -> C.Expr
refineApplyLH s id args = refineApply s id $ map (transLHExpr s) args

transLH :: InternalState -> Proof -> C.Theorem
transLH s (Proof def@(Def name dArgs body) sig) =
    C.Theorem name args (transResLHArg s res) (transformTop s def)
  where
    Signature sigArgs res = renameSigArgs dArgs sig
    args = map (transLHArg s) sigArgs

transLHArg :: InternalState -> LHArg -> C.CoqArg
transLHArg s (LHArg name ty reft) = (name, C.TExpr $ transType s ty, transProp s reft)

transResLHArg :: InternalState -> LHArg -> C.Prop
transResLHArg s (LHArg _ _ reft) = transProp s reft

transType :: InternalState -> Type -> C.Expr
transType _ (TVar tv) = C.Var tv
transType s (TDat con tys) = C.App con $ map (transType s) tys

transFuncType :: InternalState -> [C.CoqArg] -> C.Type -> C.Type
transFuncType s argTps ret = foldl C.TFun dom codom where
    args = map (\(n, typ, ref) -> C.RExpr n typ ref) argTps
    dom:codom = args ++ [ret]

transPat :: Pat -> C.Pat
transPat (Pat con args) = C.Pat con args

transExpr :: InternalState -> Expr -> C.Expr
transExpr s (Term x)   = transLHExpr s x
transExpr s (Let id e1 e2)  = C.Let id (transExpr s e1) (transExpr s e2)
-- only add match pattern "as b" if match branches use b
transExpr s (Case e b bs) | any (\(_, x) -> x `dependsOn` b) bs = C.Match (transExpr s e) b $ map (B.bimap transPat $ transExpr s) bs
transExpr s (Case e _ bs) = C.MatchSimple (transExpr s e) $ map (B.bimap transPat $ transExpr s) bs
transExpr _ Unit            = C.Var "()"
transExpr s (QMark e1 e2)   = C.App "(?)" $ map (transExpr s) [e1,e2]

transProof :: InternalState -> Expr -> [C.Tactic]
transProof s (Term t) | mode s == DefProofMode = 
  let
    tm = transLHExpr s t
    isSubsetTerm = isSubsetTermExpr s "" tm -- not argument to function application, so giving id that won't match any function
    expectedTyp = let (_, _, spec) = last (defSpecs s) in spec
    castTerm = {-trace ("Casting term "++ show tm ++ " which "++if isSubsetTerm then "is" else "isn't"++ " of subset type into type " ++ C.showArgUnnamed expectedTyp) $-} C.castInto tm isSubsetTerm expectedTyp
  in [C.Exact $ show castTerm]
transProof s (Term (LHVar "trivial")) = transProof s Unit
transProof s (Term (LHApp f es)) = C.Apply (refineApply s f (map (transExpr s) es')): concatMap (transProof s) ps
    where
      (es', ps) = B.second catMaybes . unzip $ map (getQMark . Term) es
      getQMark :: Expr -> (Expr, Maybe Expr)
      getQMark (QMark e1 e2) = (e1, Just e2)
      getQMark e             = (e,Nothing)
transProof s (Term t) = [C.Apply (transLHExpr s t)]
transProof s (Eqn expr hints tm) = translateEqn s expr hints tm

transProof s (QMark e1 e2) = concatMap (transProof s) [e1,e2]
transProof _ Unit = [C.Trivial]
transProof s (Let id e1 e2) = [C.LetTac id (head $ transProof s e1) (head $ transProof s e2)]
transProof s (Case e _ bs) =
    [C.Destruct (transExpr s e) (map patArgs pats) (map (transProof s) es)]
  where
    (pats, es) = unzip bs

flattenEqns :: Expr -> [LHExpr] -> LHExpr -> [(LHExpr, LHExpr, [LHExpr])]
flattenEqns (Term tm) hints lstTm = [(tm, lstTm, hints)]
flattenEqns (Eqn expr fstHints penultimateTm) hints lstTm =
  let eqns = flattenEqns expr fstHints penultimateTm
  in eqns++[(penultimateTm, lstTm, hints)]


translateEqn :: InternalState -> Expr -> [LHExpr] -> LHExpr -> [C.Tactic]
translateEqn s expr hints tm = 
  let 
    eqns = flattenEqns expr hints tm
  in map (\(x, y, hints) -> C.Assert "lem" (transEq s x y) (concatMap (transProof s . Term) hints)) eqns


transBrel :: Brel -> C.Brel
transBrel Eq = C.Eq

transLHExpr :: InternalState -> LHExpr -> C.Expr
transLHExpr s (LHApp f es)  = refineApplyLH s f es
transLHExpr s (LHVar x)     = C.Var x
transLHExpr _ (LHSym s)     = C.Sym s
transLHExpr s (Evaluate t)  = transExpr s t
transLHExpr s e             = error "not an expression."


projectIfNeeded s tm = if isSubsetTermExpr s "" tm then projectIfNeeded s (C.Project tm) else {- trace ("term "++show tm++" isn't of subset type, state:="++show s) -} tm

transEq :: InternalState -> LHExpr -> LHExpr -> C.Prop
transEq s t u = 
  let 
    [coqT, coqU] = map (transLHExpr s) [t, u]
    [pt, pu] = map (projectIfNeeded s) [coqT, coqU]
  in {- trace ("cast equality "++show coqT ++ " = "++show coqU++"to "++show pt ++ " = "++show pu) $ -} C.Brel C.Eq pt pu

transProp :: InternalState -> LHExpr -> C.Prop
transProp s (Brel Eq e1 e2)       = transEq s e1 e2
-- transProp s (Brel brel e1 e2)     = C.Brel (transBrel brel) (transLHExpr s e1) (transLHExpr s e2)
transProp s (LHNeg form)          = C.Neg $ transProp s form
transProp s (And es)              = C.And $ map (transProp s) es
transProp s (LHApp f es)          = C.PExpr $ refineApply s f $ map (transLHExpr s) es
transProp s (LHVar x)             = C.PExpr $ C.Var x
transProp s (LHImpl ante concl)   = C.Impl (transProp s ante) $ transProp s concl
transProp s LHTrue                = C.TT


-- Top level translation

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
checkInductiveCall indVars allArgs@((Term (LHVar arg),pos):args) =
  case M.lookup arg indVars of
    Just x | x == pos -> Just (pos,arg)
    _                 -> checkInductiveCall indVars args
checkInductiveCall indVars (_:args) = checkInductiveCall indVars args

transformTop :: InternalState -> Def -> [C.Tactic]
transformTop s def@(Def name args e) =
    case runReader (transformInductive s e) env of
      Nothing        -> transBranch s e
      Just (arg, e') -> transIndDef s (Def name args e') arg
  where
    env = Env name (M.fromList $ zip args [0..]) M.empty

type Arg = (Int,Id)
transformInductive :: InternalState -> Expr -> Reader Environment (Maybe (Arg,Expr))
transformInductive s (Let x e1 e2) = do
    ind1 <- transformInductive s e1
    ind2 <- transformInductive s e2
    return $ case ind1 of
                Nothing       -> fmap (Let x e1) <$> ind2
                Just (ind, e) -> Just (ind, Let x e e2)
transformInductive s (Case (Term (LHVar matchId)) ident branches) = {-trace ("Calling transformInductive on Case "++matchId ++ " of "++ident++" with branches: \n  "++intercalate ",\n  " (map show branches)) $-} do
    Env{envName=name, envArgs=args} <- ask
    let n = fromMaybe (error $ "Non-existent id: "++matchId++" in "++intercalate "|" (map (\(id, n) -> id ++ " -> "++ show n) $ M.toList args)) (M.lookup matchId args)
    mInds <- forM branches $ \(Pat con args, e) ->
                case args of
                  []    -> return Nothing
                  {- here we assume that induction happens on the
                  first argument of the constructor. -}
                  (x:_) -> {-trace ("Calling transformInductive on inductive branch "++show con ++ show args ++ " -> "++ show e) $-} local (addInd x n) (transformInductive s e)
    let
      mIdx                = {-trace ("mInds:="++show mInds) $-} findIndex isJust mInds
      (mIndArg, mIndExpr) = unzipMaybe $ fromJust . (mInds !!) <$> mIdx
      mBranches           = {-trace ("mIdx:="++show (fromJust mIdx)++", IndArg:="++show mIndArg ++ ", mIndExpr:="++show mIndExpr) $-} modifyAt branches <$> mIdx <*>
          pure (replaceExprWith (fromJust mIndExpr))
    return $ (,) <$> mIndArg <*> (Case (Term (LHVar matchId)) ident <$> mBranches)
  where
    replaceExprWith :: Expr -> (Pat, Expr) -> (Pat,Expr)
    replaceExprWith e' (pat,e) = (pat,e')
transformInductive s app@(Term (LHApp f lhArgs)) = 
  let args = map unevaluate lhArgs in
  {-trace ("Checking if "++show app++" is recursive call.\n") $-} do
    Env{envName=name, envIndVars=indVars} <- ask
    indFromArgs <- mapM (transformInductive s) args
    let 
      indFromApp = checkInductiveCall indVars (zip args [0..])
    return $
      if f == name then
        fmap (\arg@(pos,argName) -> (arg, Term $ LHVar ("IH"++argName))) indFromApp
      else
        let modifyArg ix = B.second (setAt lhArgs ix . evaluate) . fromJust $ indFromArgs!!ix
        in  fmap (Term . LHApp f) . modifyArg <$> findIndex isJust indFromArgs
transformInductive s (QMark e1 e2) = do
    mInd1 <- transformInductive s e1
    case mInd1 of
      Just (arg, e1') -> return $ Just (arg, QMark e1' e2)
      Nothing -> do
        mInd2 <- transformInductive s e2
        return $ (\ (arg, e2') -> Just (arg, QMark e1 e2')) =<< mInd2
transformInductive s eqn@(Eqn expr lstHints lstTm) = 
  let 
    hints = map unevaluate lstHints 
    lstExpr = unevaluate lstTm in
  {- trace ("calling transformInductive on equation:\n  "++intercalate "\n  " (map show (flattenEqns expr lstHints lstTm))) $-} do
    mIndInit <- transformInductive s expr
    case mIndInit of
      Just (arg, e') -> return $ Just (arg, Eqn e' lstHints lstTm)
      Nothing -> do
        mIndLst <- transformInductive s lstExpr
        case mIndLst of
          Just (arg, e') -> return $ Just (arg, Eqn expr lstHints (evaluate e'))
          Nothing -> do
            Env{envName=name, envIndVars=indVars} <- ask
            indFromArgs <- mapM (transformInductive s) hints
            let 
              isIndCall var = not (null $ M.lookup (fromJust $ stripPrefix "IH" var) indVars)
              indIdx = findIndex (\x -> case x of (Just (_, Term (LHVar arg))) -> isIndCall arg; _ -> False) indFromArgs
              indFromHints = (=<<) (\x -> fmap fst $ indFromArgs!!x) indIdx

              {-indexedHints = trace ("indFromArgs: "++show indFromArgs++", indCallIdx: "++show indIdx++", indFromHintsSimpl: "++show indFromHintsSimpl) $ zip hints [0..]
              indFromHints = trace ("indexedHints: "++show indexedHints++", indVars: "++show indVars) $ checkInductiveCall indVars indexedHints -}
              transformedHints = zipWith (\x y -> case x of Just (_, x) -> x; Nothing -> y) indFromArgs hints
              transformedEqn = trace("transformedHints: "++show transformedHints) $ Eqn expr (map evaluate transformedHints) lstTm 
            return $ fmap (,transformedEqn) indFromHints
transformInductive _ _ = return Nothing

transIndDef :: InternalState -> Def -> Arg -> [C.Tactic]
transIndDef s (Def name args (Case (Term (LHVar ind)) _ [(_,e1), (_,e2)])) (pos, var) =
    [induction [transBranch s e1, transBranch s e2]]
  where
    allArgs = nonIndArgs
    nonIndArgs = deleteAt args pos
    induction = C.Induction (args !! pos) var ("IH"++var)
transIndDef _ def _ = error $ "unhandled proof case of " ++ show def

transBranch :: InternalState -> Expr -> [C.Tactic]
transBranch s = updateLast C.toSolve . transProof s


-- intermediate representation of LH source

class Dependencies a where
  dependsOn:: a -> Id -> Bool

instance Dependencies Type where
  dependsOn (TVar typ) name = typ == name
  dependsOn (TDat typ typArgs) name = (typ == name) || any (`dependsOn` name) typArgs

instance Dependencies LHExpr where
  dependsOn (And exprs) name = any (`dependsOn` name) exprs
  dependsOn (LHImpl expr expr2) name  = dependsOn expr name || dependsOn expr2 name
  dependsOn (LHNeg expr) name         = dependsOn expr name
  dependsOn (Brel _ expr expr2) name  = dependsOn expr name || dependsOn expr2 name
  dependsOn (LHApp id exprs) name     = id == name || any (`dependsOn` name) exprs
  dependsOn (LHVar id) name           = id == name
  dependsOn LHSym{} _               = False
  dependsOn (Evaluate expr) name      = expr `dependsOn` name
  dependsOn LHTrue _                  = False

instance Dependencies Expr where
  dependsOn (Term t) name                   = t `dependsOn` name
  dependsOn (Eqn expr hintO tm) name        = expr `dependsOn` name || any (`dependsOn` name) hintO || tm `dependsOn` name
  dependsOn (QMark expr expr2) name         = dependsOn expr name || dependsOn expr2 name
  dependsOn Unit name                       = False
  dependsOn (Case expr pat branches) name   = dependsOn expr name || any (\(Pat patCon patArgs, expr) -> dependsOn expr name || patCon == name || elem name patArgs) branches
  dependsOn (Let id expr expr2) name        = dependsOn expr name || dependsOn expr2 name

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

appearsNoLater :: Id -> Id -> [Id] -> Ordering
appearsNoLater id id2 [] = LT
appearsNoLater id id2 (x:xs) | x == id = LT
appearsNoLater id id2 (x:xs) | x == id2 = GT
appearsNoLater id id2 (x:xs) = appearsNoLater id id2 xs 

-- order imports alphabetically, order everything else in dependency order or else in order of given Id list (e.g. order in source document), defaulting to LT
orderSourceContent :: [Id] -> SourceContent -> SourceContent -> Ordering
orderSourceContent _ (Import id) (Import id2)                 = compare id id2
orderSourceContent _ (Import _) _                             = LT
orderSourceContent _ _ (Import _)                             = GT
orderSourceContent _ srcCont srcCont2 | srcCont == srcCont2   = EQ
orderSourceContent _ srcCont srcCont2 | dependsOn srcCont2 (name srcCont) = LT
orderSourceContent _ srcCont srcCont2 | dependsOn srcCont (name srcCont2) = GT
orderSourceContent idList (Alias n _) (Alias m _)             = appearsNoLater n m idList
orderSourceContent _ Alias{} _ = LT
orderSourceContent _ _ Alias{} = GT
orderSourceContent idList sC sC2 = appearsNoLater (name sC) (name sC2) idList
