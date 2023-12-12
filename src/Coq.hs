{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TupleSections #-}
{-#LANGUAGE LambdaCase #-}

module Coq where
import Util
import Prelude

import Data.List (find)
import Data.Char (isSpace)
import Data.Data
import Data.Either.Combinators
import Data.Align
import Data.Tuple.Extra
import Data.Bifunctor
import Numeric.Natural
import qualified Data.HashMap.Strict as M

import Debug.Trace

type CoqArg = (Id, Type, Prop)
triviallyRefinedArg :: Id -> Type -> CoqArg
triviallyRefinedArg n typ = (n, typ, TT)

data Theorem = Theorem {cpName :: Id, cpArgs :: [CoqArg], cpType :: Prop, cpbody :: [Tactic]}
instance Show Theorem where
  show (Theorem name args ty bod) =
    "Definition "++ name ++"_spec: Prop. \nProof. "
    ++ "now "++dropWhile isSpace (show (Exact (Forall (map (\(n,t,r) -> (n,Just (RExpr n t r))) args) ty)))
    ++ ".\nDefined.\n"
    ++ "Theorem " ++ name ++ ": " ++ name++"_spec" ++ ".\n"
    ++ "Proof.\n  "
    ++ introsArgs args
    ++ destructArgs args
    ++ intercalate "" (map show bod) ++ "\n"
    ++ "Qed.\n"
    where 
      introsArgs :: [(Id, b, c)] -> String
      introsArgs args = intercalate "" $ map (((show . Intros) . flip (:) []). fst3) args
      destructArgs args = 
        let destructs = unwords (map destructSubsetArgIfNeeded args) in
        if all isSpace destructs then "" else destructs ++ "\n  "

-- data Proof = IndProof {bod :: ProofBod  , proofIndArg :: (Id,Int)} | NIndProof {bod :: PrBod}
showArg :: CoqArg -> String
showArg (arg, t, prop) | not $ printRef prop = addParens $ arg ++ ": " ++ show t
showArg (arg, t, p) = addParens (arg ++ ": { "++arg++" : " ++ show t ++ " | " ++ show p ++ " }")

showArgUnnamed :: CoqArg -> String
showArgUnnamed (arg, t, prop) | not $ printRef prop = show t
showArgUnnamed (arg, t , p) = "{ "++arg++" : " ++ show t ++ " | " ++ show p ++ " }"

showArgId :: CoqArg -> String
showArgId (n, _, _) = n

unrefinedName :: Id -> Id
unrefinedName s = s ++ "_unrefined"

injectIntoSubset :: Id -> String
injectIntoSubset t = addParens $ "# "++ t

injectUnrefAppl :: Expr -> String
injectUnrefAppl tm = addParens $ "exist "++addParens (show tm)++" " ++ "eq_refl"

projectFromSubset :: CoqArg -> String
projectFromSubset (n, _, _) = addParens $ "` "++ n

isTrivial :: Prop -> Bool
isTrivial = (==) TT

printTrivial = True

printRef :: Prop-> Bool
printRef p = printTrivial || not (isTrivial p) 

data LookupState = State {specs :: [(Id, [CoqArg], Either CoqArg Prop)], datatypeConstrs :: [Id], isDefnMode:: Bool, isDefnSpecMode:: Bool}
defSpecs :: LookupState -> [(Id, [CoqArg], CoqArg)]
defSpecs s = mapMaybe (\(x, y, e) -> (x,y,) <$> leftToMaybe e) $ specs s

fromSpecs :: [(Id, [CoqArg], Either CoqArg Prop)] -> LookupState
fromSpecs specs = State specs [] False False

getRefinementsLastSpec :: LookupState -> [(Id, Prop)]
getRefinementsLastSpec s = maybe [] getRefinementsCoqArg (leftToMaybe r) where
    (_, _, r) = last (specs s)

getRefinementsExpr :: LookupState -> Id -> Expr -> [(Id, Prop)]
getRefinementsExpr _ _ (StringLiteral _) = []
getRefinementsExpr _ _ (IntLiteral _) = []
getRefinementsExpr _ _ (FloatLiteral _) = []
getRefinementsExpr _ _ (Sym _) = []
getRefinementsExpr _ _ (Bop _ _ _) = []
getRefinementsExpr _ _ (EProp (Brel _ _ _)) = []
getRefinementsExpr s n (Inject (RExpr _ _ prop) x _) | not (printRef prop) = getRefinementsExpr s n x
getRefinementsExpr s n (Project (Inject typ x prf)) = getRefinementsExpr s n x
getRefinementsExpr s n (Project tm) = tail $ getRefinementsExpr s n tm
getRefinementsExpr s n (Inject (RExpr v _ prop) tm _) = (v, prop):getRefinementsExpr s n tm
-- constructors of data types return (unrefined) elements of that data type
getRefinementsExpr s _ exp@(App n _) | n `elem` datatypeConstrs s = []
-- induction hypotheses are refined if their function's/theorem's return type is
getRefinementsExpr s _ exp@(App n@('I':'H':_) exprs) = getRefinementsLastSpec s
getRefinementsExpr s _ exp@(App n exprs) | isJust (find ((== n) . fst3) $ defSpecs s) = 
  let
    funSpec = fromJust $ find ((== n) . fst3) (defSpecs s)
    (_, _, coqArg) = funSpec
  in getRefinementsCoqArg coqArg
getRefinementsExpr s _ exp@(Var v) | v `elem` datatypeConstrs s = []
getRefinementsExpr s _ exp@(Var v@('I':'H':_)) = getRefinementsLastSpec s
getRefinementsExpr s "" exp@Var{} = getRefinementsExpr s (fst3 $ (last . specs) s) exp
getRefinementsExpr s n exp@(Var v) = 
  let
    funcSpec = snd3 <$> find ((== n) . fst3) (specs s)
    argSpec = find ((== v) . fst3) =<< funcSpec
  in 
    case argSpec of
    -- a hypothesis or result of destructing terms in the proof state
    Nothing -> trace (show v++" is not an argument to function "++n++" with funcSpec "++show funcSpec) []
    -- if in proof mode, we know that any subset typed argument has long been destructed by now
    Just arg -> 
      if isDefnMode s then {-trace ("fetching refinements for arg: "++showArg arg++" of "++n)-} getRefinementsCoqArg arg else []
getRefinementsExpr s n e = case e of
  Ite _ expr _ -> getRefinementsExpr s n expr
  MatchSimple _ patExprs -> getRefinementsExpr s n $ (snd . head) patExprs
  Match _ _ patExprs -> getRefinementsExpr s n $ (snd . head) patExprs
  _ -> trace ("Term "++show e++" is assumed (by default) to have a single trivial refinement.") [("_", TT) | printTrivial] -- error ("Cannot determine if "++show e++" is a subset term. ")

getRefinementsCoqArg :: CoqArg -> [(Id, Prop)]
getRefinementsCoqArg (_, typ, ref) | not $ printRef ref = getRefinements typ
-- getRefinementsCoqArg (n, typ, ref)  | isTrivial ref = (n, TT):getRefinements typ
getRefinementsCoqArg (n, typ, ref) = {-trace ("called getRefinementsCoqArg for "++showArg (n, typ, ref)++".") $-} (n, ref):getRefinements typ

isSubsetTermCoqArg arg = not $ null (getRefinementsCoqArg arg)

-- ret (nested) refinements of (refinement) type
getRefinements :: Type -> [(Id, Prop)]
getRefinements (RExpr _ typ ref) | not $ printRef ref = getRefinements typ
getRefinements (RExpr n typ ref) | isTrivial ref = (n, TT):getRefinements typ
getRefinements (RExpr n typ ref) = (n, ref):getRefinements typ
getRefinements _ = []

projectIfNeededGeneric :: LookupState -> Expr -> Expr
projectIfNeededGeneric s tm = let
    refs = getRefinementsExpr s "" tm
  in foldr (\_ x -> Project x) tm (getRefinementsExpr s "" tm)

equivReqs :: (Id, Prop) -> (Id, Prop) -> Bool
equivReqs need have = snd need == snd have 

subsumptionCasts :: LookupState -> [(((Id, Prop), (Id, Prop)), Type)] -> [Expr -> Expr]
subsumptionCasts _ [] = []
subsumptionCasts _ reqs | all (uncurry equivReqs . fst) reqs = []
-- subsumptionCasts [((need, have), typ)] | isTrivial need = [\tm -> Inject (RExpr "" typ need) (Project tm) (ProofTerm "I")]
subsumptionCasts s [((need, have), typ)] = [subsumptionCast s typ need have]
subsumptionCasts s reqs | all (uncurry equivReqs . fst) reqsTl = [subsumptionCast s typ need have] where ((need, have), typ):reqsTl = reqs
subsumptionCasts _ required = error ("Found more than one subsumption cast: "++show required++" This is unsupported. ")

substituteInType :: Maybe (Id, Natural) -> ((Id, Natural) -> Id -> Expr) -> Type -> Type
substituteInType nO f typ = case typ of
  TExpr expr -> TExpr $ subst expr
  TProp prop -> TProp $ trans prop
  RExpr n typ ref -> RExpr n (transTp typ) (trans ref)
  TFun a b -> TFun (transTp a) (transTp b)
  Hole -> Hole
  where
    subst = substituteInTerm nO f
    trans = substituteInProp nO f
    transTp = substituteInType nO f

substituteInProp :: Maybe (Id, Natural) -> ((Id, Natural) -> Id -> Expr) -> Prop -> Prop
substituteInProp nO f p = case p of
  Brel rel left right -> Brel rel (subst left) (subst right)
  And conjs -> And (map trans conjs)
  Or disjs -> Or (map trans disjs)
  Impl ante concl -> Impl (trans ante) (trans concl)
  Neg form -> Neg (trans form)
  TT -> TT
  FF -> FF
  where
    subst = substituteInTerm nO f
    trans = substituteInProp nO f

substituteInTerm :: Maybe (Id, Natural) -> ((Id, Natural) -> Id -> Expr) -> Expr -> Expr
substituteInTerm nO f expr = case expr of
  (Var n) -> maybe (Var n) (`f` n) nO
  (App n xs) -> trace("substituting in application of "++rename n) App (rename n) (zipWith (\i -> substituteInTerm (Just (n,i)) f) [0..] xs)
  (Bop op left right) -> Bop op (subst left) (subst right)
  (Match e n branches) -> Match (subst e) n (mapBranches branches)
  (MatchSimple e branches) -> MatchSimple (subst e) (mapBranches branches)
  (Ite cond thenE elseE) -> Ite (trans cond) (subst thenE) (subst elseE)
  (Let n defn body) -> Let n (subst defn) (subst body)
  (Inject typ expr prf) -> Inject (transTp typ) (subst expr) (subst <$> prf)
  (Project tm) -> Project (subst tm)
  (SubCast typ (n, need) (m, have) tm prfO) -> SubCast (transTp typ) (n, trans need) (m, trans have) (subst tm) (fmap subst prfO)
  (EProp p) -> EProp (trans p)
  (TypArg typ) -> TypArg (transTp typ)
  (Lambda n typ body) -> Lambda n (transTp typ) (subst body)
  tm -> tm
  where
    subst = substituteInTerm nO f
    trans = substituteInProp nO f
    transTp = substituteInType nO f
    mapBranches = mapSnd subst
    rename n = case nO of Just bind -> (case f bind n of Var m -> m; _ -> n); Nothing -> n

substForAppl :: LookupState -> Expr -> M.HashMap Id Expr
substForAppl s tm = M.fromList $ case tm of
    App n args -> maybe [] (zipWith (\arg spec -> (fst3 spec, stripCasts arg)) args) (funcSpec n)
    _ -> []
    where
      stripCasts (Project tm) = tm
      stripCasts (Inject _ tm _) = tm
      stripCasts (SubCast _ _ _ tm _) = tm
      stripCasts tm = tm
      funcSpec n = snd <$> find (\(x,_) -> x == n) (map (\(x,y,_) -> (x,y)) (specs s))

transForAppl :: LookupState -> Expr -> ((Id, Natural) -> Id -> Expr)
transForAppl s tm = const (\v -> fromMaybe (Var v) (M.lookup v (substForAppl s tm)))

-- unfortunately free variables in terms in specs of previous definitions/theorems 
-- may have different refinements in current context, requiring recasting them
-- additionally, we need to substitute current values for dependent variables in the sepcs
reprocessRef :: LookupState -> Maybe Expr -> Prop -> Prop
reprocessRef s tm ref = trans ref where
  funcSpec n = snd <$> find (\(x,_) -> x == n) (map (\(x,y,_) -> (x,y)) (specs s))
  argSpecO n v = find ((== v) . fst3) =<< funcSpec n
  f (n,_) v = case argSpecO n v of 
    Just expCArg -> 
      let
        tmRefs = getRefinementsExpr s n (Var v)
        tmRefsSubst = mapSnd (substituteInProp Nothing (maybe (\_ v -> Var v) (transForAppl s) tm)) tmRefs
        castVar = castInto s (Var v) tmRefsSubst (Left expCArg)
      in trace ("Cast in reprocessRef (for ref "++ show ref++") for variable "++v++" with refs "++show tmRefsSubst++" to type "++showArg expCArg++" yielding "++show castVar) castVar
    Nothing -> Var v
  trans = substituteInProp Nothing f

castInto :: LookupState -> Expr -> [(Id, Prop)] -> Either CoqArg Type -> Expr
castInto s tm refinements expectedTyp = 
  let 
    typ = either id id $ mapLeft snd3 expectedTyp
    expectedRefinements = either (mapSnd (reprocessRef s (Just tm)). getRefinementsCoqArg) (const []) expectedTyp
    refinementsSubstRev = reverse (mapSnd (reprocessRef s Nothing) refinements)
    zippedRefs = padZip (reverse expectedRefinements) refinementsSubstRev
    -- drop matching innermost refinements
    zippedRefsStripped = dropWhile (uncurry (==)) zippedRefs
    expectedTyps = scanr (\(n,r) t -> RExpr n t r) typ expectedRefinements
    -- drop the accompanying base (expected) types
    expectedTypsStripped = drop (length zippedRefs - length zippedRefsStripped) expectedTyps
    (subsumptionRefs, projInjRefs) = break (\(x,y) -> isNothing x || isNothing y) zippedRefsStripped
    inject (Just (n, ref), Nothing) typ tm = Inject (RExpr n typ ref) tm (if isDefnSpecMode s && ref == TT then Just (ProofTerm "I") else Nothing)
    injectionsRev = zipWith inject projInjRefs expectedTypsStripped
    (projections, injections) = if isNothing (fst =<< safeHead projInjRefs) then (map (const Project) projInjRefs, []) else ([], reverse injectionsRev)
    subsumptions = subsumptionCasts s (reverse $ zip (map (bimap fromJust fromJust) subsumptionRefs) (take (length subsumptionRefs) expectedTypsStripped))
    castOperators :: [Expr -> Expr]
    castOperators = injections ++ subsumptions ++ projections
  in foldr (\f x -> f x) tm castOperators

refineApplyGeneric :: Show a => LookupState -> (a -> Expr) -> (LookupState -> Id -> a -> [(Id, Prop)]) -> Id -> [a] -> Expr
refineApplyGeneric s transTm getRefs n args = {- trace ("Calling refineApplyGeneric with specs "++ show allSpecs ++ " on: " ++ show (App n (map transTm args))) $ -} App n (zipWith cast args [0..]) where
  allSpecs = specs s
  lookupArgTyp :: Maybe [CoqArg]
  lookupArgTyp = snd3 <$> find ((== n) . fst3) (specs s)

  hasSpec i = case lookupArgTyp of 
    Just argTps -> 
      (length argTps >= i + 1) || error ("looked up specification of function " ++ n ++ " has only "++ show (length argTps) ++" arguments but is applied to at least "++ show (i + 1) ++ " arguments. ")
    _ -> False

  cast t i | hasSpec i =
    let
      funSpec = fromJust lookupArgTyp
      tm = transTm t
      expectedSpec = funSpec!!i
      (_, typ, ref) = expectedSpec
      dataArg = n `elem` datatypeConstrs s
      dataArgTyp = (either snd3 (error "Found proposition as return type of data constructor.")  . thd3 <$> find ((== n) . fst3) (specs s))
      dataRes = Just typ == (either snd3 (error "Found proposition as return type of data constructor.")  . thd3 <$> find ((== n) . fst3) (specs s))
      triviallyRefined = isTrivial ref
      expected = if dataArg && dataRes && isTrivial ref then Right typ else Left expectedSpec
    in
    castInto s tm (getRefs s (fst3 $ last allSpecs) t) expected
  cast t i | not (hasSpec i) = error $ "No specs found for "++n -- if getRefs allSpecs n t then Project (transTm t) else transTm t

data Def = Def {defName :: Id, defArgs:: [Id], defBody :: Expr} | SpecDef {sdefNAme :: Id, sdefArgs :: [CoqArg], sdefRet :: CoqArg, sdefBody :: [Tactic]} | RefDef {name :: Id, args:: [CoqArg], ret:: CoqArg, state :: LookupState}
instance Show Def where
  show (Def name args body) =
    "Fixpoint " ++ name ++ " " ++ unwords args ++ " :=\n"
    ++ "  " ++ show body ++ ".\n"
  show (SpecDef name args retft tacs) = 
    "Definition " ++ name ++ " " ++ unwords (map showArg args) ++ ": " ++ showArgUnnamed retft ++ ". \n"++ "Proof.\n  "
    ++ destructArgs args
    ++ intercalate "" (map show tacs) ++ "\n"
    ++ "Defined.\n"
    where 
      destructArgs args = 
        let destructs = unwords (map destructSubsetArgIfNeeded args) in
        if all isSpace destructs then "" else destructs ++ "\n  "
  show (RefDef name args retft state) = 
    let
      unrefName = unrefinedName name
      getRefinementsDestructedArgs coqArg@(n, _, _) = if any ((== n) . fst3) args then [] else getRefinementsCoqArg coqArg
      unrefinedApply = refineApplyGeneric state (Var . fst3) (\_ _ -> getRefinementsDestructedArgs) unrefName args
      unrefRet = case thd3 <$> find ((== unrefName) . fst3)  (specs state) of
        Just (Left coqArg) -> coqArg
        _ -> error ("No type spec found for "++unrefName++".")
      unrefApplSubsetTp = isSubsetTermCoqArg unrefRet
      unrefRetft = let (n, typ, _) = retft in (n, typ, TT)
      unrefApplCast = if unrefApplSubsetTp then Project unrefinedApply else unrefinedApply
      destructs = unwords (map destructSubsetArgIfNeeded args)
      retTp = uncurry3 RExpr retft 
      refinedDefinien = "Proof.\n  " ++ (if all isSpace destructs then "" else destructs ++ "\n  ") ++ "exact " ++ addParens (injectUnrefAppl unrefApplCast) ++". \n" ++ "Defined.\n"
      refinedDef = "Definition " ++ name ++ " " ++ unwords (map showArg args) ++ ": " ++ showArgUnnamed retft ++ " .\n" ++ refinedDefinien
    in refinedDef


data Constant = Const {constId :: Id, body :: Expr}
instance Show Constant where
  show (Const name body) = "Definition " ++ name ++ " := "++ show body ++ ". "

newtype Load = Load {moduleName :: Id}
instance Show Load where
  show (Load name) = "Load " ++ name ++ ". "

data NewType = NewType {typeName :: Id, defin :: Type}
instance Show NewType where
  show (NewType name def) = "Notation " ++ name ++ ":= " ++ show def ++ ". "

data Inductive = Inductive {typeId :: Id, constructors :: [(Id, Type)]}
instance Show Inductive where
  show (Inductive typeId constrs) = inductiveDecl where
    showBranch (n, typ) = n ++ ": " ++ show typ
    inductiveDecl = "Inductive " ++ typeId ++ ": Set := " ++ intercalate " | " (map showBranch constrs) ++ ". "

data CoqContent = LoadDeclaration Load 
                | ConstantDeclaration Constant
                | TypeDeclaration NewType
                | InductiveDeclaration Inductive
                | DefinitionDeclaration Def
                | TheoremDeclaration Theorem
instance Show CoqContent where
  show (LoadDeclaration l)        = show l
  show (ConstantDeclaration c)    = show c
  show (TypeDeclaration t)        = show t
  show (InductiveDeclaration ind) = show ind
  show (DefinitionDeclaration d)  = show d
  show (TheoremDeclaration thm)   = show thm


data Pat = Pat {patCon :: Id, patArgs :: [Id]} deriving Data

instance Show Pat where
  show (Pat c args) = c ++ " " ++ unwords (map filterWeird args)

data Expr = App Id [Expr]
          | Bop Bop Expr Expr
          | Var Id
          | Match Expr Id [(Pat, Expr)]
          | MatchSimple Expr [(Pat, Expr)]
          | Ite Prop Expr Expr
          | Let Id Expr Expr
          | Sym String
          | StringLiteral String
          | IntLiteral Integer
          | FloatLiteral Float
          | Inject Type Expr (Maybe Expr)
          | Project Expr
          | SubCast Type (Id, Prop) (Id, Prop) Expr (Maybe Expr)
          | ProofTerm String
          | TrivialProof
          | EProp Prop
          | Buildin BuildInTps
          | TypArg Type
          | Lambda Id Type Expr
          | Forall [(Id, Maybe Type)] Prop deriving Data

injectTrivially :: Expr -> Expr
injectTrivially expr = Inject Hole expr $ Just (ProofTerm "I")

injectArgument :: CoqArg -> Expr
injectArgument (name, typ, reft) = Inject typ (Var name) Nothing

subsumptionCast :: LookupState -> Type  -> (Id, Prop) -> (Id, Prop) -> Expr -> Expr
subsumptionCast s typ need@(_, needRef) have tm = SubCast typ need have tm (if isDefnSpecMode s && isTrivial needRef then Just $ ProofTerm "I" else Nothing)

instance Show Expr where
  show (Sym s)        = s
  show (App f [])     = filterWeird f
  show (App f es)     = f ++ " " ++ unwords (map showAppArg es)
  show (Bop bop e1 e2)    = show e1 ++ show bop ++ show e2
  show (Var v)       = filterWeird v
  show (Let n b e)   = "let " ++ filterWeird n ++ " := " ++ show b ++ " in " ++ show e
  show (Match e n branches) =
      "match " ++ show e ++ " as " ++ filterWeird n ++ " with "
      ++ unwords (map showBranch branches) ++ " end"
    where
      showBranch (p, e) = "| " ++ show p ++ " => " ++ show e
  show (MatchSimple e branches) =
      "match " ++ show e ++ " with "
      ++ unwords (map showBranch branches) ++ " end"
    where
      showBranch (p, e) = "| " ++ show p ++ " => " ++ show e
  show (Ite cond thenE elseE) = "if "++ addParens (show cond) ++ " then "++addParens (show thenE)++" else "++addParens (show elseE)
  show (Inject (RExpr n (RExpr _ typ _) ref) x p) = show (Inject (RExpr n typ ref) x p)
  -- show (Inject refTp@(RExpr n typ TT) tm Nothing) = show (Inject refTp tm (Just $ ProofTerm "I")) -- ++". try "++show (Exact (Lambda n typ (ProofTerm "I")))
  -- show (Inject refTp@(RExpr n typ TT) tm Nothing) = injectIntoSubset $ addParens (show tm) -- addParens $ unwords ("injectionCast":[show typ, addParens $ show (Lambda n typ (EProp TT)), (show . Lambda n typ) (ProofTerm "I"), addParens $ show tm])
  show (Inject refTp@(RExpr n typ ref) tm p) =  
    addParens $ unwords ("injectionCast":[show typ, addParens $ show (Lambda n typ (EProp ref)), addParens $ show tm, maybe "_" show p])
  show (Project expr@Var{})   = addParens $ "` " ++ addParens (show expr)
  show (Project expr)   = addParens $ "` " ++ addParens (show expr)
  show (SubCast (RExpr _ typ ref) (n,need) (m,have) tm prfO) = show $ SubCast typ (n, need) (m, have) tm prfO
  show (SubCast typ (n, need) (m, have) tm prfO) = 
    addParens $ unwords ("subsumptionCast":[show typ, addParens $ show (Lambda m typ (EProp have)), addParens $ show (Lambda n typ (EProp need)), maybe "_" show prfO, addParens $ show tm]) --show tm ++ " ↠ " ++ show need
  show (ProofTerm prf)  = prf
  show TrivialProof = show Trivial
  show (EProp p) = show p
  show (Buildin b) = show b
  show (StringLiteral s) = "\"" ++ s ++ "\""
  show (FloatLiteral f) = show f
  show (IntLiteral i) = show i-- "Z_as_Int._"++ show i
  show (TypArg t) = show t
  show (Lambda n typ body) = addParens $ "fun "++n++": "++show typ++" => "++show body
  show (Forall args body) = addParens $ "forall "++unwords (map (\(n, typ)->addParens $ n ++ maybe "" ((++) ":" . show) typ) args)++", "++show body

instance Eq Expr where
  (==) x y = show x == show y

showAppArg :: Expr -> String
showAppArg app@(App _ (_:_)) = addParens $ show app
showAppArg e = show e

destructSubsetArg :: CoqArg -> Tactic
destructSubsetArg (name, ty, refts) = Destruct (Var name) [[name, name++"p"]] []

destructSubsetArgIfNeeded :: CoqArg -> String
destructSubsetArgIfNeeded (n, ty, ref) | not $ printRef ref = ""
destructSubsetArgIfNeeded coqArg = show . destructSubsetArg $ coqArg

data Type = TExpr Expr | TProp Prop | RExpr Id Type Prop | TFun Type Type | Hole deriving (Eq, Data)
instance Show Type where
  show (TExpr e) = show e
  show (TProp p) = show p
  show (RExpr _ typ refts) | not $ printRef refts = show typ
  show (RExpr n typ refts) = "{"++ n ++ ": " ++ show typ ++ "| " ++ show refts ++"}"
  show (TFun dom codom) = addParens $ show dom ++ " -> " ++ show codom
  show Hole = "_" 

data Prop = PExpr Expr
          | Brel Brel Expr Expr
          | And [Prop]
          | Or [Prop]
          | Impl Prop Prop
          | Neg Prop
          | TT
          | FF deriving (Data, Eq)

instance Show Prop where
  show (PExpr e) = show e
  show (Brel rel e1 e2)   = show e1 ++ show rel ++ show e2
  show (And ps)           = intercalate " /\\ " $ map show ps
  show (Or ps)            = intercalate " \\/ " $ map show ps
  show (Impl ante concl)  = show ante ++ "->" ++ show concl
  show (Neg form)         = "not" ++ addParens (show form)
  show TT                 = "True"
  show FF                 = "False"

data Brel = Eq | Neq | Leq | Geq | Lt | Gt deriving (Data, Eq)
instance Show Brel where 
  show Eq = "="
  show Neq = "<>"
  show Leq = "<="
  show Geq = ">="
  show Lt = "<"
  show Gt = ">"

data Bop = Plus | Minus | Times | Div | Mod deriving (Data, Eq)
instance Show Bop where 
  show Plus = "+"
  show Minus = "-"
  show Times = "*"
  show Div = "/"
  show Mod = undefined

data BuildInTps = Integer | Boolean | Double deriving (Data, Eq)
-- CoqInt and CoqFloat are defined in LHTactics file to avoid nameclashes with names from translated LH
instance Show BuildInTps where
  show Integer = "BinNums.Z"
  show Boolean = "Prop"
  show Double = "CoqFloat"

trivial = "smt_trivial"

ple = "ple"

apply = "smt_app"

solve = apply

data Tactic = Trivial
            | Ple
            | Try Tactic
            | Apply Expr
            | Destruct {destrExpr :: Expr, destrBinds :: [[Id]], destrBranches :: [[Tactic]]}
            | Induction {indArg :: Id, indVar :: Id, indHyp :: Id, introPat:: [Id], indBranches :: [[Tactic]]}
            | Assert {hypName:: Id, claim:: Prop, prf:: [Tactic]}
            | LetTac Id Tactic Tactic
            | Intros [Id]
            | Revert [Id]
            | Now Tactic
            | Solve Expr
            -- only for more nicely structured output
            | Subgoal [Tactic]
            | Exact Expr deriving Data

simplInduction arg var hyp = Induction arg var hyp [var, hyp]


toSolve :: Tactic -> Tactic
toSolve (Apply e) = Solve e
toSolve d@Destruct{} = d{destrBranches = map (updateLast toSolve) (destrBranches d)}
toSolve i@Induction{} = i{indBranches  = map (updateLast toSolve) (destrBranches i)}
toSolve t = Now t

instance Show Tactic where
  show Trivial = "smt_trivial"++". "
  show Ple = ple++". "
  show (Try t) = "try "++show t 
  show (Apply TrivialProof) = show TrivialProof++". "
  show (Apply e) = apply ++ " " ++ showAppArg e++". "
  show (Solve TrivialProof) = show TrivialProof++". "
  show (Solve e) = solve ++ " " ++ showAppArg e++". "
  -- TODO generalize destruct
  show (Destruct (Var n) binds branches) =
      "destruct " ++ n ++ " as [" ++ intercalate " | " (map unwords binds) ++ " ]. "
      ++ showBranches branches
  show (Destruct e binds branches) = 
      "destruct " ++ show e ++ " as [" ++ intercalate " | " (map unwords binds) ++ " ]. "
      ++ showBranches branches
  show (Induction arg var hyp introPats branches) =
      "induction " ++ arg ++ " as [| " ++ unwords introPats ++ " ]. "
      ++ showBranches branches
  show (Assert hypName claim prf) = "\n  assertFresh " ++ addParens (show claim) ++ " as "++ hypName ++ " using "  ++ proof++". " where
    proof = if not (null prf) then addParens (intercalate "; " (map show prf)) else show Trivial
  show (LetTac n t1 t2) = "let " ++ filterWeird n ++ " := " ++ addParens (showNoDot t1) ++ " in " ++ show t2
  show (Intros ns) = "intros " ++ unwords ns++". "
  show (Revert ns) = "revert " ++ unwords ns++". "
  show (Now t) = "now " ++ show t -- for better debugging: show t++show (Try Trivial)
  show (Exact x) = "unshelve refine "++ addParens (show x)++". "
  show (Subgoal tacs) = "\n    { "++intercalate "" (map show tacs)++"}"

showNoDot :: Tactic -> String
showNoDot t = (init . init) (show t)

showBranches :: [[Tactic]] -> String
showBranches = intercalate "" . map showBranch
  where showBranch   = intercalate "" . map show

filterWeird :: String -> String
filterWeird = filter (not . flip elem "$#")