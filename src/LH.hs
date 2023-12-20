{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

module LH where

import Prelude
import qualified Coq as C

import qualified Data.Map as M
import Control.Monad.Reader
import Data.List(findIndex,find, stripPrefix)
import Data.Either.Combinators
import Data.Tuple.Extra
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

data Type = TVar Id | TDat Id [Type] | Buildin BuildInTps deriving Show

isProof :: Signature -> Bool
isProof = (== "()") . typeName . lhArgType . sigRes
  where
    typeName :: Type -> String
    typeName (TVar n) = n
    typeName (Buildin b) = show b
    typeName (TDat n _) = n

data Pat = Pat {patCon :: Id, patArgs :: [Id]} deriving Show

data LHExpr = And [LHExpr]
            | Or [LHExpr]
            | LHImpl LHExpr LHExpr
            | LHNeg LHExpr
            | LHIte LHExpr LHExpr LHExpr
            | Brel Brel LHExpr LHExpr
            | Bop Bop LHExpr LHExpr
            | LHApp Id [LHExpr]
            | LHVar Id
            | LHSym String
            | LHStringLit String
            | LHIntLit Integer
            | LHFloatLit Float
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

data Brel = Eq | Neq | Leq | Geq | Lt | Gt deriving Show
data Bop = Plus | Minus | Times | Div | Mod deriving Show
data BuildInTps = Integer | Boolean | Double deriving Show

data LHArg = LHArg { lhArgName :: Id, lhArgType :: Type, lhArgReft :: LHExpr} deriving Show
data Signature = Signature {sigArgs :: [LHArg], sigRes :: LHArg} deriving Show

-- the default state, SpecMode is used during translation of specs (when (refined) variables to the definition/theorem aren't yet destructed),
-- the optional argument is set during translation of the refinement of an argument (which within this translation is thus not yet refined
-- ProofMode is used during proofs of theorems
-- DefProofMode is used in translation of definiens of "_unrefined" declarations, yields different proof translation in leafs of proof tree, 
--   as we are constructing term not discharging (Prop kinded) proof obligation, so we use translate to smt_now refine ... instead of smt_now smt_app ...
data TranslationMode = 
    SpecMode [C.CoqArg] (Maybe (C.CoqArg, (Id, Id)))
  | ProofMode [C.CoqArg] [(C.CoqArg, (Id, Id))]
  | DefProofMode [C.CoqArg] [(C.CoqArg, (Id, Id))] deriving (Eq, Show)

-- used outside of proofs, when no arguments are translated yet
defaultMode = SpecMode [] Nothing

getBoundVarRefs :: TranslationMode -> ([C.CoqArg], [(C.CoqArg, (Id, Id))])
getBoundVarRefs (ProofMode undestrArgs destrArgs) = (undestrArgs, [])
getBoundVarRefs (DefProofMode undestrArgs destrArgs) = (undestrArgs, [])
getBoundVarRefs (SpecMode undestrArgs destrArgsO) = (undestrArgs, maybeToList destrArgsO)

appendRefArgs :: TranslationMode -> [C.CoqArg] -> TranslationMode
appendRefArgs (SpecMode args arg) moreArgs = SpecMode (args ++ moreArgs) arg 
appendRefArgs (ProofMode args destrArgs) moreArgs = ProofMode (args ++ moreArgs) destrArgs 
appendRefArgs (DefProofMode args destrArgs) moreArgs = DefProofMode (args ++ moreArgs) destrArgs

removeArgM :: TranslationMode -> Id -> TranslationMode
removeArgM m n = 
  case m of
    (SpecMode args arg) -> SpecMode (filter toKeepArgs args) ((\x -> if toKeepDestrArg x then Just x else Nothing) =<< arg)
    (ProofMode args destrArgs) -> ProofMode (filter toKeepArgs args) (filter toKeepDestrArg destrArgs)
    (DefProofMode args destrArgs) -> DefProofMode (filter toKeepArgs args) (filter toKeepDestrArg destrArgs)
    where
      toKeepArgs = (/=) n . fst3
      toKeepDestrArg ((m, _, _), (o, _)) = n /= m && n /= o

data InternalState = State {specs:: [(Id, [C.CoqArg], Either C.CoqArg C.Prop)], datatypeConstrs :: [Id], datatypeMeasures:: [(Id, Id)], warnings :: [String], mode :: TranslationMode} deriving Show
defSpecs :: InternalState -> [(Id, [C.CoqArg], C.CoqArg)]
defSpecs (State specs _ _ _ _) = mapMaybe (\(x, y, e) -> (x,y,) <$> leftToMaybe e) specs
thmSpecs :: InternalState -> [(Id, [C.CoqArg], C.Prop)]
thmSpecs (State specs _ _ _ _) = mapMaybe (\(x, y, e) -> (x,y,) <$> rightToMaybe e) specs
emptyState :: InternalState
emptyState = State [] [] [] [] defaultMode
changeMode :: InternalState -> TranslationMode -> InternalState
changeMode s = State (specs s) (datatypeConstrs s) (datatypeMeasures s) (warnings s)

removeArg :: InternalState -> Id -> InternalState
removeArg s n = changeMode s (removeArgM (mode s) n)

toLookupState :: InternalState -> C.LookupState
toLookupState s = C.State (specs s) (datatypeConstrs s) (isDefnMode (mode s)) undestrArgs destrArgs where
  isDefnMode (ProofMode _ _) = False
  isDefnMode (DefProofMode _ _) = False
  isDefnMode _ = True
  (undestrArgs, destrArgs) = getBoundVarRefs (mode s)

concatState :: InternalState -> InternalState -> InternalState
concatState (State sps cs m1 w1 _) (State sps2 cs2 m2 w2 f)= State (sps ++ sps2) (cs ++ cs2) (m1 ++ m2) (w1 ++ w2) f

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

registerDataDefSpecs :: Id -> [C.CoqArg] -> C.CoqArg -> StateResult ()
registerDataDefSpecs name args ret = Result (State [(name, args, Left ret)] [name] [] [] defaultMode, ())

specModeState = State [] [] [] [] defaultMode

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
renameReft (And es)       = And       <$> mapM renameReft es
renameReft (Brel b e1 e2) = Brel b    <$> renameReft e1 <*> renameReft e2
renameReft (Bop b e1 e2)  = Bop b     <$> renameReft e1 <*> renameReft e2
renameReft (LHApp id es)  = LHApp     <$> rename id <*> mapM renameReft es
renameReft (LHVar id)     = LHVar     <$> rename id
renameReft (Evaluate expr)= Evaluate  <$> renameExpr expr 
renameReft (LHImpl e1 e2) = LHImpl    <$> renameReft e1 <*> renameReft e2
renameReft (LHIte c e e2) = LHIte     <$> renameReft c <*> renameReft e <*> renameReft e2
renameReft (LHNeg e)      = LHNeg     <$> renameReft e
renameReft (LHSym s)      = pure $ LHSym s
renameReft LHTrue         = pure LHTrue
renameReft (LHIntLit i)   = pure $ LHIntLit i
renameReft (LHStringLit s)= pure $ LHStringLit s
renameReft (LHFloatLit f) = pure $ LHFloatLit f

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

refineApplyWrapper :: Show a => (a-> C.Expr) -> (C.LookupState -> Id -> a -> [(Id, C.Prop)]) -> InternalState -> Id -> [a] -> C.Expr
refineApplyWrapper transTm getRefinements s = C.refineApplyGeneric (toLookupState s) transTm getRefinements

refineApplyArg :: InternalState -> Id -> [C.CoqArg] -> C.Expr
refineApplyArg = refineApplyWrapper transTm (\_ _ -> C.getRefinementsCoqArg) where
  transTm :: C.CoqArg -> C.Expr
  transTm (n, typ, ref) = C.Var n

refineApply :: InternalState -> Id -> [C.Expr] -> C.Expr
refineApply = refineApplyWrapper id C.getRefinementsExpr

refineApplyLH :: InternalState -> Id -> [LHExpr] -> C.Expr
refineApplyLH s id args = refineApply s id $ map (transLHExpr s) args

transLH :: InternalState -> Proof -> C.Theorem
transLH s (Proof def@(Def name dArgs body) sig) =
    C.Theorem name (transLHArgs s sigArgs) (transResLHArg s res) (transformTop s def)
  where
    Signature sigArgs res = renameSigArgs dArgs sig


transLHArgStateless :: InternalState -> LHArg -> C.CoqArg
transLHArgStateless s (LHArg name ty reft) = (name, C.TExpr $ transType s ty, transProp s reft)

transLHArg :: InternalState -> LHArg -> StateResult C.CoqArg
transLHArg s (LHArg name ty reft) = Result (newState, (name, tpT, refT)) where
  tpT = C.TExpr $ transType s ty
  (previousArgs, _) = getBoundVarRefs (mode s)
  destrIds = (name, C.refWitnessName name)
  -- used only for translating the refinement itself
  -- as this translation is independent of the refinement of the current arg using tempState is OK there
  tempState = changeMode s $ SpecMode previousArgs (Just ((name, tpT, C.TT), destrIds))
  refT = transProp tempState reft
  newState = changeMode s $ SpecMode previousArgs (Just ((name, tpT, refT), destrIds))

transLHArgs :: InternalState -> [LHArg] -> [C.CoqArg]
transLHArgs s args = coqArgs where
    scanner :: StateResult [C.CoqArg] -> LHArg -> StateResult [C.CoqArg]
    scanner acc@(Result (s, previousArgs)) arg = acc >>= \prev -> (++) prev . (: []) <$> transLHArg s arg
    Result (_, coqArgs) = foldl scanner (Result (s, [])) args

transResLHArg :: InternalState -> LHArg -> C.Prop
transResLHArg s (LHArg _ _ reft) = transProp s reft

transType :: InternalState -> Type -> C.Expr
transType _ (TVar tv) = C.Var tv
transType s (TDat con []) = C.App con []
transType s (TDat con tys) = trace ("Calling transType on application of parametric type "++con++" to the type arguments: "++unwords (map show tys)) C.App con $ map (transType s) tys
transType s (Buildin b) = C.Buildin $ transBuildin b

transFuncType :: InternalState -> [C.Type] -> C.Type -> C.Type
transFuncType s args ret = foldl C.TFun dom codom where
    dom:codom = args ++ [ret]

transPat :: Pat -> C.Pat
transPat (Pat con args) = C.Pat con args

transExpr :: InternalState -> Expr -> C.Expr
transExpr s (Term x)   = transLHExpr s x
transExpr s (Let id e1 e2)  = C.Let id (transExpr s e1) (transExpr s e2)
-- only add match pattern "as b" if match branches use b
transExpr s (Case e b  bs) = if any (\(_, x) -> x `dependsOn` b) bs then match (Just b) else match Nothing where
    -- vO = case e of (Term (LHVar v)) -> Just v; _ -> Nothing
    -- subst = M.fromList [(b, b++"_remembered")| b <- []] -- maybeToList vO]
    bsT = map (B.bimap transPat $ transExpr s) bs -- map (B.bimap transPat (transExpr s. (flip runReader subst . renameExpr))) bs
    match bO = C.Match (transExpr s e) bO bsT

transExpr _ Unit            = C.Var "()"
transExpr s (QMark e1 e2)   = undefined -- C.App "(?)" $ map (transExpr s) [e1,e2]

transProof :: InternalState -> Expr -> [C.Tactic]
transProof s (Term t) | case mode s of DefProofMode _ _ -> True; _ -> False = 
  let
    tm = transLHExpr s t
    ls = toLookupState s
    trans = C.transForAppl ls tm
    transRef = mapSnd (C.substituteInProp Nothing trans)
    refinements = transRef $ C.getRefinementsExpr ls "" tm -- not argument to function application, so giving "" meaning id of current definition/thm
    expectedTyp = (thd3 . last) (defSpecs s)
    castTerm = C.castInto ls tm refinements $ Left expectedTyp
  in [C.Refine castTerm]
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
transBrel Neq = C.Neq
transBrel Geq = C.Geq
transBrel Leq = C.Leq
transBrel Gt = C.Gt
transBrel Lt = C.Lt

transBop :: Bop -> C.Bop
transBop Plus = C.Plus
transBop Minus = C.Minus
transBop Times = C.Times
transBop Div = C.Div
transBop Mod = C.Mod

transBuildin :: BuildInTps -> C.BuildInTps
transBuildin Integer = C.Integer
transBuildin Boolean = C.Boolean
transBuildin Double = C.Double

transOp :: InternalState -> Bop -> LHExpr -> LHExpr -> C.Expr
transOp s bop t u =
  let
    [coqT, coqU] = map (transLHExpr s) [t, u]
    [pt, pu] = map (projectIfNeeded s) [coqT, coqU]
  in C.Bop (transBop bop) pt pu

transLHExpr :: InternalState -> LHExpr -> C.Expr
transLHExpr s (LHApp f es)  = refineApplyLH s f es
transLHExpr s (LHIte c e e2)= C.Ite (transProp s c) (transLHExpr s e) (transLHExpr s e2)
transLHExpr s (LHVar x)     = C.Var x
transLHExpr _ (LHSym s)     = C.Sym s
transLHExpr s (Evaluate t)  = transExpr s t
transLHExpr s (Brel rel t u)= C.EProp $ transRel s rel t u
transLHExpr s (Bop bop t u) = transOp s bop t u
transLHExpr _ (LHIntLit i)  = C.IntLiteral i
transLHExpr _ (LHStringLit s)= C.StringLiteral s
transLHExpr _ (LHFloatLit f)= C.FloatLiteral f
transLHExpr s (LHNeg f) = C.EProp (C.Neg $ transProp s f)
transLHExpr s (And fs) = C.EProp (C.And $ map (transProp s) fs)
transLHExpr s (Or fs) = C.EProp (C.Or $ map (transProp s) fs)
transLHExpr s (LHImpl f g) = C.EProp (C.Impl (transProp s f) (transProp s g))
transLHExpr s LHTrue = C.EProp C.TT

projectIfNeeded s = C.projectIfNeededGeneric (toLookupState s)
transRel :: InternalState -> Brel -> LHExpr -> LHExpr -> C.Prop
transRel s rel t u = 
  let 
    [coqT, coqU] = map (transLHExpr s) [t, u]
    [pt, pu] = map (projectIfNeeded s) [coqT, coqU]
  in C.Brel (transBrel rel) pt pu

transEq :: InternalState -> LHExpr -> LHExpr -> C.Prop
transEq s = transRel s Eq

transProp :: InternalState -> LHExpr -> C.Prop
transProp s (Brel rel e1 e2)      = transRel s rel e1 e2
transProp s (LHNeg form)          = C.Neg $ transProp s form
transProp s (And es)              = C.And $ map (transProp s) es
transProp s (Or es)               = C.Or $ map (transProp s) es
transProp s (LHIte c e e2)        = C.PExpr (C.Ite (transProp s c) (transLHExpr s e) (transLHExpr s e2))
transProp s (LHApp f es)          = C.PExpr $ projectIfNeeded s (refineApply s f (map (transLHExpr s) es))
transProp s (LHVar x)             = C.PExpr $ projectIfNeeded s (C.Var x)
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
      Nothing        -> transBranch s Nothing (Nothing, e)
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
transformInductive s (Term(Bop bop e1 e2)) = do
    mInd1 <- transformInductive s (unevaluate e1)
    case mInd1 of
      Just (arg, e1') -> return $ Just (arg, Term $ Bop bop (evaluate e1') e2)
      Nothing -> do
        mInd2 <- transformInductive s (unevaluate e2)
        return $ (\ (arg, e2') -> Just (arg, Term $ Bop bop e1 (evaluate e2'))) =<< mInd2
transformInductive s (Term(Brel brel e1 e2)) = do
    mInd1 <- transformInductive s (unevaluate e1)
    case mInd1 of
      Just (arg, e1') -> return $ Just (arg, Term $ Brel brel (evaluate e1') e2)
      Nothing -> do
        mInd2 <- transformInductive s (unevaluate e2)
        return $ (\ (arg, e2') -> Just (arg, Term $ Brel brel e1 (evaluate e2'))) =<< mInd2
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
              transformedEqn = {-trace("transformedHints: "++show transformedHints) $-} Eqn expr (map evaluate transformedHints) lstTm 
            return $ fmap (,transformedEqn) indFromHints
transformInductive _ _ = return Nothing

transIndDef :: InternalState -> Def -> Arg -> [C.Tactic]
transIndDef s (Def name args (Case (Term (LHVar ind)) _ branches)) (pos, indVar) =
    [induction (map (transBranch s (Just ind)) (map (\(x,y) -> (Just x, y)) branches))]
  where
    -- subst = M.fromList [(indArg, indArg++"_rememberedI")]
    -- [e1T, e2T] = map (flip runReader subst . renameExpr) [e1, e2]
    allArgs = nonIndArgs
    nonIndArgs = deleteAt args pos
    indArg = args !! pos
    indHyp = "IH"++indVar
    induction = C.simplInduction indArg indVar indHyp
transIndDef _ def _ = error $ "unhandled proof case of " ++ show def

transBranch :: InternalState -> Maybe Id -> (Maybe Pat, Expr) -> [C.Tactic]
transBranch s (Just indVar) (Just (Pat con args), e) = [C.Subgoal (updateLast C.toSolve (transProof (changeMode s newMode) e))] where
  keepIndVar = indVar `elem` con:args
  oldMode = mode s
  newMode = if keepIndVar then oldMode else removeArgM oldMode indVar
transBranch s _ (_, e) = [C.Subgoal (updateLast C.toSolve (transProof s e))]

-- intermediate representation of LH source

class Dependencies a where
  dependsOn:: a -> Id -> Bool

instance Dependencies Type where
  dependsOn (TVar typ) name = typ == name
  dependsOn (TDat typ typArgs) name = (typ == name) || any (`dependsOn` name) typArgs
  dependsOn (Buildin b) _ = False

instance Dependencies LHExpr where
  dependsOn (And exprs) name = any (`dependsOn` name) exprs
  dependsOn (Or exprs) name = any (`dependsOn` name) exprs
  dependsOn (LHImpl expr expr2) name  = dependsOn expr name || dependsOn expr2 name
  dependsOn (LHNeg expr) name         = dependsOn expr name
  dependsOn (Brel _ expr expr2) name  = dependsOn expr name || dependsOn expr2 name
  dependsOn (Bop _ expr expr2) name   = dependsOn expr name || dependsOn expr2 name
  dependsOn (LHApp id exprs) name     = id == name || any (`dependsOn` name) exprs
  dependsOn (LHVar id) name           = id == name
  dependsOn LHSym{} _               = False
  dependsOn (Evaluate expr) name      = expr `dependsOn` name
  dependsOn LHTrue _                  = False
  dependsOn _ _                       = False

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
  name (Import n) = n
  name (Alias n _) = n
  name (Data n _ _) = n
  name (Type n _) = n
  name (Definition n _ _ _) = n
  name (Theorem n _ _ _) = n

instance Eq SourceContent where 
  (==) expr expr2 = name expr == name expr2

instance Dependencies SourceContent where
  dependsOn (Import _) _ = False
  dependsOn (Alias _ expr) name = expr `dependsOn` name
  dependsOn (Data _ idO constrs) name = idO == Just name || any (\(_, typs) -> any (`dependsOn` name) typs) constrs
  dependsOn (Type _ typ) name = typ `dependsOn` name
  dependsOn (Definition _ args ret expr) name = any (`dependsOn` name) args || ret `dependsOn` name || expr `dependsOn` name
  dependsOn (Theorem _ args ret expr) name = any (`dependsOn` name) args || ret `dependsOn` name || expr `dependsOn` name

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
orderSourceContent _ srcCont srcCont2 | srcCont2 `dependsOn` name srcCont = LT
orderSourceContent _ srcCont srcCont2 | srcCont `dependsOn` name srcCont2 = GT
orderSourceContent idList (Alias n _) (Alias m _)             = appearsNoLater n m idList
orderSourceContent _ Alias{} _ = LT
orderSourceContent _ _ Alias{} = GT
orderSourceContent idList (Definition n _ _ _) (Definition m _ _ _) = appearsNoLater n m idList
orderSourceContent idList (Definition n _ _ _) _ = LT
orderSourceContent idList _ (Definition n _ _ _) = GT
orderSourceContent idList sC sC2 = appearsNoLater (name sC) (name sC2) idList
