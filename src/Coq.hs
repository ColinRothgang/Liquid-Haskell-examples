{-# LANGUAGE DeriveDataTypeable #-}

module Coq where
import Util
import Prelude

import Data.List (find)
import Data.Char (isSpace)
import Data.Data

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

projectFromSubset :: CoqArg -> String
projectFromSubset (id, _, _) = addParens $ "` "++ id

isTrivial :: Prop -> Bool
isTrivial = (==) TT

printTrivial = False

printRef :: Prop-> Bool
printRef p = not (isTrivial p) || printTrivial 

isSubsetTermCoqArg :: CoqArg -> Bool
isSubsetTermCoqArg (_, _, ref) | printRef ref = True
isSubsetTermCoqArg (n, RExpr _ _ ref, _)  | printRef ref = True
isSubsetTermCoqArg (n, RExpr _ typ _, r) = isSubsetTermCoqArg (n, typ, r)
isSubsetTermCoqArg _ = False

castInto :: Expr -> Bool -> CoqArg -> Expr
castInto tm isSubsetTerm expectedTyp = 
  let 
    (n, typ, prop) = expectedTyp
    needSubsetTerm = {-trace ("Calling cast on expr "++ show tm ++ " which " ++ (if isSubsetTerm then "is" else "isn't") ++" of subset type into type "++show expectedTyp ++ ", which "++(if isTrivial prop then "isn't" else "is")++". \n") $-} printRef prop
  in
  case (needSubsetTerm, isSubsetTerm) of
    (True, True) -> tm
    (True, False) -> Inject (RExpr n typ prop) tm (ProofTerm "I")
    (False, False) -> tm
    (False, True) -> Project tm

refineApplyGeneric :: Show a => [(Id, [CoqArg])] -> (a -> Expr) -> ([(Id, [CoqArg])] -> Id -> a -> Bool) -> Id -> [a] -> Expr
refineApplyGeneric allSpecs transTm isSubsetTm n args = {- trace ("Calling refineApplyGeneric with specs "++ show allSpecs ++ " on: " ++ show (App n (map transTm args))) $ -} App n (zipWith (cast allSpecs n) args [0..]) where
  lookupArgTyp :: [(Id, [CoqArg])] -> Id -> Maybe [CoqArg]
  lookupArgTyp allSpecs id = 
    let
      spec = snd <$> find (\(x,_) -> x == id) allSpecs
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
    castInto tm (isSubsetTm allSpecs id t) (funSpec!!i)
  cast allSpecs id t i | not (hasSpec allSpecs id i) = if isSubsetTm allSpecs id t then Project (transTm t) else transTm t

data Def = Def {defName :: Id, defArgs:: [Id], defBody :: Expr} | SpecDef {sdefNAme :: Id, sdefArgs :: [CoqArg], sdefRet :: CoqArg, sdefBody :: [Tactic]} | RefDef {name :: Id, args:: [CoqArg], ret:: CoqArg, state :: [(Id, [CoqArg])]}
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
  show (RefDef name args retft specs) = 
    let
      unrefName = unrefinedName name
      destructedArgs = map (\(x, typ, ref) -> (x, typ, TT)) args
      unrefinedApply = refineApplyGeneric specs (\(x, _, _) -> Var x) (\_ _ -> isSubsetTermCoqArg) unrefName
      destructs = unwords (map destructSubsetArgIfNeeded args)
      refinedDefinien = "Proof.\n  " ++ (if all isSpace destructs then "" else destructs ++ "\n  ") ++ show (Exact $ SimpleInject (unrefinedApply destructedArgs) (ProofTerm "eq_refl")) ++". \n" ++ "Defined.\n"
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
          | SimpleInject Expr Expr
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
  show (Ite cond thenE elseE) = "if "++ show cond ++ " then "++show thenE++" else "++show elseE
  show (SimpleInject x (ProofTerm s)) = addParens $ "exist "++addParens (show x)++" " ++ s
  show (Inject (RExpr id typ ref) x p) =  injectIntoSubset $ show x -- addParens $ "inject_into_subset_type " ++ show typ ++ " " ++ show x ++ " " ++ show ref ++ " " ++ show p
  show (Project expr@Var{})   = addParens $ "` " ++ show expr
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
            | Induction {indArg :: Id, indVar :: Id, indHyp :: Id, indBranches :: [[Tactic]]}
            | Assert {hypName:: Id, claim:: Prop, prf:: [Tactic]}
            | LetTac Id Tactic Tactic
            | Intros [Id]
            | Revert [Id]
            | Now Tactic
            | Solve Expr
            | Exact Expr

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
  show (Induction arg var hyp branches) =
      "induction " ++ arg ++ " as [| " ++ unwords [var,hyp] ++ " ]. "
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