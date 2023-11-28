{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TupleSections #-}

module Coq where
import Util
import Prelude

import Data.List (find)
import Data.Char (isSpace)
import Data.Data
import Data.Either.Combinators
import Data.Align
import Data.Tuple.Extra

import Debug.Trace

type CoqArg = (Id, Type, Prop)
triviallyRefinedArg :: Id -> Type -> CoqArg
triviallyRefinedArg id typ = (id, typ, TT)

data Theorem = Theorem {cpName :: Id, cpArgs :: [CoqArg], cpType :: Prop, cpbody :: [Tactic]}
instance Show Theorem where
  show (Theorem name args ty bod) =
    "Theorem " ++ name ++ " " ++ unwords (map showArg args) ++ ": " ++ show ty ++ ".\n"
    ++ "Proof.\n  "
    ++ destructArgs args
    ++ intercalate ". " (map show bod) ++ ".\n"
    ++ "Qed.\n"
    where 
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
showArgId (id, _, _) = id

unrefinedName :: Id -> Id
unrefinedName s = s ++ "_unrefined"

injectIntoSubset :: Id -> String
injectIntoSubset t = addParens $ "# "++ t

injectUnrefAppl :: Expr -> String
injectUnrefAppl tm = addParens $ "exist "++addParens (show tm)++" " ++ "eq_refl"

projectFromSubset :: CoqArg -> String
projectFromSubset (id, _, _) = addParens $ "` "++ id

isTrivial :: Prop -> Bool
isTrivial = (==) TT

printTrivial = False

printRef :: Prop-> Bool
printRef p = printTrivial || not (isTrivial p) 

data LookupState = State {specs :: [(Id, [CoqArg], Either CoqArg Prop)], datatypeConstrs :: [Id], isDefnMode:: Bool}
defSpecs :: LookupState -> [(Id, [CoqArg], CoqArg)]
defSpecs s = mapMaybe (\(x, y, e) -> (x,y,) <$> leftToMaybe e) $ specs s

fromSpecs :: [(Id, [CoqArg], Either CoqArg Prop)] -> LookupState
fromSpecs specs = State specs [] False

getRefinementsLastSpec :: LookupState -> [Prop]
getRefinementsLastSpec s = maybe [] getRefinementsCoqArg (leftToMaybe r) where
    (_, _, r) = last $ specs s

-- TODO: improve treatment of nested Subset types and induction hypothesis
getRefinementsExpr :: LookupState -> Id -> Expr -> [Prop]
getRefinementsExpr s id (Inject (RExpr _ _ prop) x _) | not (printRef prop) = getRefinementsExpr s id x
getRefinementsExpr s id (Project (Inject typ x prf)) = getRefinementsExpr s id x
getRefinementsExpr s id (Project tm) = tail $ getRefinementsExpr s id tm
getRefinementsExpr s id (Inject (RExpr _ _ prop) tm _) = prop:getRefinementsExpr s id tm
-- constructors of data types return (unrefined) elements of that data type
getRefinementsExpr s _ exp@(App n _) | n `elem` datatypeConstrs s = []
-- induction hypotheses are refined if their function's/theorem's return type is
getRefinementsExpr s _ exp@(App n@('I':'H':_) exprs) = getRefinementsLastSpec s
getRefinementsExpr s _ exp@(App n exprs) | not $ null (find ((== n) . fst3) $ defSpecs s) = 
  let
    funSpec = fromJust $ find ((== n) . fst3) (defSpecs s)
    (_, _, coqArg) = funSpec
  in getRefinementsCoqArg coqArg
getRefinementsExpr s _ exp@(Var n) | n `elem` datatypeConstrs s = []
getRefinementsExpr s _ exp@(Var n@('I':'H':_)) = getRefinementsLastSpec s
getRefinementsExpr s "" exp@Var{} = getRefinementsExpr s (fst3 $ (last . specs) s) exp
getRefinementsExpr s id exp@(Var n) = 
  let
    funcSpec = snd <$> find (\(x,_) -> x == id) (map (\(x,y,_) -> (x,y)) (specs s))
    argSpec = find ((== n) . fst3) =<< funcSpec
  in 
    case argSpec of
    -- a hypothesis or result of destructing terms in the proof state
    Nothing -> trace (show n++" is not an argument to function "++id++". ") []
    -- if in proof mode, we know that any subset typed argument has long been destructed by now
    Just arg -> if isDefnMode s then getRefinementsCoqArg arg else []
getRefinementsExpr s id e = case e of
  Ite _ expr _ -> getRefinementsExpr s id expr
  MatchSimple _ patExprs -> getRefinementsExpr s id $ (snd . head) patExprs
  Match _ _ patExprs -> getRefinementsExpr s id $ (snd . head) patExprs
  _ -> [TT | printTrivial] -- error ("Cannot determine if "++show e++" is a subset term. ")

getRefinementsCoqArg :: CoqArg -> [Prop]
getRefinementsCoqArg (_, typ, ref) | not $ printRef ref = getRefinements typ
getRefinementsCoqArg (n, typ, ref)  | isTrivial ref = TT:getRefinements typ
getRefinementsCoqArg (n, typ, ref) = ref:getRefinements typ

isSubsetTermCoqArg arg = not $ null (getRefinementsCoqArg arg)

-- ret (nested) refinements of (refinement) type
getRefinements :: Type -> [Prop]
getRefinements (RExpr _ typ ref) | not $ printRef ref = getRefinements typ
getRefinements (RExpr _ typ ref) | isTrivial ref = TT:getRefinements typ
getRefinements (RExpr _ typ ref) = ref:getRefinements typ
getRefinements _ = []

projectIfNeededGeneric :: LookupState -> Expr -> Expr
projectIfNeededGeneric s tm = foldr (\_ x -> Project x) tm (getRefinementsExpr s "" tm)

simpleCastInto :: Type -> (Maybe Prop, Maybe Prop) -> Expr -> Expr
simpleCastInto _ (Nothing, Nothing) tm = tm
simpleCastInto typ (Just ref, Nothing) tm = Inject (RExpr "" typ ref) tm (ProofTerm "I")
simpleCastInto _ (Nothing, Just _) tm = Project tm
simpleCastInto typ (Just need, Just have) tm | need == have = tm
simpleCastInto typ (Just need, Just have) tm | isTrivial need && not (isTrivial have) = Inject (RExpr "" typ need) (Project tm) (ProofTerm "I")
simpleCastInto typ (Just need, Just have) tm = tm -- error ("Need to prove subsumption judgement for "++show need ++ " <: "++ show have". ")

castInto :: Expr -> [Prop] -> CoqArg -> Expr
castInto tm refinements expectedTyp = 
  let 
    (_, typ, _) = expectedTyp
    expectedRefinements = getRefinementsCoqArg expectedTyp
    zippedRefs = padZip expectedRefinements refinements
  in foldr (simpleCastInto typ) tm zippedRefs

refineApplyGeneric :: Show a => LookupState -> (a -> Expr) -> (LookupState -> Id -> a -> [Prop]) -> Id -> [a] -> Expr
refineApplyGeneric s transTm isSubsetTm n args = {- trace ("Calling refineApplyGeneric with specs "++ show allSpecs ++ " on: " ++ show (App n (map transTm args))) $ -} App n (zipWith (cast allSpecs n) args [0..]) where
  allSpecs = specs s
  lookupArgTyp :: [(Id, [CoqArg], Either CoqArg Prop)] -> Id -> Maybe [CoqArg]
  lookupArgTyp allSpecs id = 
    let
      spec = snd3 <$> find ((== id) . fst3) allSpecs
    in spec

  hasSpec allSpecs id i = case lookupArgTyp allSpecs id of 
    Just argTps -> 
      (length argTps >= i + 1) || error ("looked up specification of function " ++ id ++ " has only "++ show (length argTps) ++" arguments but is applied to at least "++ show (i + 1) ++ " arguments. ")
    _ -> False

  cast allSpecs id t i | hasSpec allSpecs id i =
    let
      funSpec = fromJust $ lookupArgTyp allSpecs id
      (n, typ, prop) = funSpec!!i
      needSubsetTerm = printRef prop
      tm = transTm t
    in
    castInto tm (isSubsetTm s (fst3 $ last allSpecs) t) (funSpec!!i)
  cast allSpecs id t i | not (hasSpec allSpecs id i) = undefined -- if isSubsetTm allSpecs id t then Project (transTm t) else transTm t

data Def = Def {defName :: Id, defArgs:: [Id], defBody :: Expr} | SpecDef {sdefNAme :: Id, sdefArgs :: [CoqArg], sdefRet :: CoqArg, sdefBody :: [Tactic]} | RefDef {name :: Id, args:: [CoqArg], ret:: CoqArg, state :: LookupState}
instance Show Def where
  show (Def name args body) =
    "Fixpoint " ++ name ++ " " ++ unwords args ++ " :=\n"
    ++ "  " ++ show body ++ ".\n"
  show (SpecDef name args retft tacs) = 
    "Definition " ++ name ++ " " ++ unwords (map showArg args) ++ ": " ++ showArgUnnamed retft ++ ". \n"++ "Proof.\n  "
    ++ destructArgs args
    ++ intercalate ". " (map show tacs) ++ ".\n"
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


data Constant = Const {id :: Id, body :: Expr}
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
    showBranch (id, typ) = id ++ ": " ++ show typ
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
          | Var Id
          | Match Expr Id [(Pat, Expr)]
          | MatchSimple Expr [(Pat, Expr)]
          | Ite Prop Expr Expr
          | Let Id Expr Expr
          | Sym String
          | StringLiteral String
          | IntLiteral Integer
          | FloatLiteral Float
          | Inject Type Expr Expr
          | Project Expr
          | ProofTerm String
          | TrivialProof
          | EProp Prop
          | Buildin BuildInTps deriving Data

injectTrivially :: Expr -> Expr
injectTrivially expr = Inject Hole expr $ ProofTerm "I"

injectArgument :: CoqArg -> Expr
injectArgument (name, typ, reft) = Inject typ (Var name) $ ProofTerm "I"

instance Show Expr where
  show (Sym s)        = s
  show (App f [])     = filterWeird f
  show (App f es)     = f ++ " " ++ unwords (map showAppArg es)
  show (Var id)       = filterWeird id
  show (Let id b e)   = "let " ++ filterWeird id ++ " := " ++ show b ++ " in " ++ show e
  show (Match e id branches) =
      "match " ++ show e ++ " as " ++ filterWeird id ++ " with "
      ++ unwords (map showBranch branches) ++ " end"
    where
      showBranch (p, e) = "| " ++ show p ++ " => " ++ show e
  show (MatchSimple e branches) =
      "match " ++ show e ++ " with "
      ++ unwords (map showBranch branches) ++ " end"
    where
      showBranch (p, e) = "| " ++ show p ++ " => " ++ show e
  show (Ite cond thenE elseE) = "if "++ addParens (show cond) ++ " then "++addParens (show thenE)++" else "++addParens (show elseE)
  show (Inject (RExpr id typ ref) x p) =  injectIntoSubset $ addParens (show x) -- addParens $ "inject_into_subset_type " ++ show typ ++ " " ++ show x ++ " " ++ show ref ++ " " ++ show p
  show (Project expr@Var{})   = addParens $ "` " ++ addParens (show expr)
  show (Project expr)   = addParens $ "` " ++ addParens (show expr)
  show (ProofTerm prf)  = prf
  show TrivialProof = show Trivial
  show (EProp p) = show p
  show (Buildin b) = show b
  show (StringLiteral s) = "\"" ++ s ++ "\""
  show (FloatLiteral f) = show f
  show (IntLiteral i) = show i-- "Z_as_Int._"++ show i

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

data Type = TExpr Expr | TProp Prop | RExpr Id Type Prop | TFun Type Type | Hole deriving Data
instance Show Type where
  show (TExpr e) = show e
  show (TProp p) = show p
  show (RExpr id typ refts) | not $ printRef refts = show typ
  show (RExpr id typ refts) = "{"++ id ++ ": " ++ show typ ++ "| " ++ show refts ++"}"
  show (TFun dom codom) = addParens $ show dom ++ " -> " ++ show codom
  show Hole = "_" 

data Prop = PExpr Expr
          | Brel Brel Expr Expr
          | Bop Bop Expr Expr
          | And [Prop]
          | Or [Prop]
          | Impl Prop Prop
          | Neg Prop
          | TT
          | FF deriving (Data, Eq)

instance Show Prop where
  show (PExpr e) = show e
  show (Brel rel e1 e2)   = show e1 ++ show rel ++ show e2
  show (Bop bop e1 e2)    = show e1 ++ show bop ++ show e2
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
            | Apply Expr
            | Destruct {destrExpr :: Expr, destrBinds :: [[Id]], destrBranches :: [[Tactic]]}
            | Induction {indArg :: Id, indVar :: Id, indHyp :: Id, introPat:: [Id], indBranches :: [[Tactic]]}
            | Assert {hypName:: Id, claim:: Prop, prf:: [Tactic]}
            | LetTac Id Tactic Tactic
            | Intros [Id]
            | Revert [Id]
            | Now Tactic
            | Solve Expr
            | Exact Expr

simplInduction arg var hyp = Induction arg var hyp [var, hyp]


toSolve :: Tactic -> Tactic
toSolve (Apply e) = Solve e
toSolve d@Destruct{} = d{destrBranches = map (updateLast toSolve) (destrBranches d)}
toSolve i@Induction{} = i{indBranches  = map (updateLast toSolve) (destrBranches i)}
toSolve t = Now t

instance Show Tactic where
  show Trivial = trivial
  show Ple = ple
  show (Apply TrivialProof) = show TrivialProof
  show (Apply e) = apply ++ " " ++ showAppArg e
  show (Solve TrivialProof) = show TrivialProof
  show (Solve e) = solve ++ " " ++ showAppArg e
  -- TODO generalize destruct
  show (Destruct (Var n) binds branches) =
      "destruct " ++ n ++ " as [" ++ intercalate " | " (map unwords binds) ++ " ]. "
      ++ showBranches branches
  show (Induction arg var hyp introPats branches) =
      "induction " ++ arg ++ " as [| " ++ unwords introPats ++ " ]. "
      ++ showBranches branches
  show (Assert hypName claim prf) = "\n  assertFresh " ++ addParens (show claim) ++ " as "++ hypName ++ " using "  ++ proof where
    proof = if not (null prf) then addParens (intercalate "; " (map show prf)) else show Trivial
  show (LetTac id t1 t2) = "let " ++ filterWeird id ++ " := " ++ addParens (show t1) ++ " in " ++ show t2
  show (Intros ids) = "intros " ++ unwords ids
  show (Revert ids) = "revert " ++ unwords ids
  show (Now t) = "now " ++ show t
  show (Exact x) = "exact "++ addParens (show x)

showBranches :: [[Tactic]] -> String
showBranches = intercalate ". " . map showBranch
  where showBranch   = intercalate ". " . map show

filterWeird :: String -> String
filterWeird = filter (not . flip elem "$#")