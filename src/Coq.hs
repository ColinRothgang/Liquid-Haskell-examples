module Coq where
import Util
import Prelude

type CoqArg = (Id, Type, Prop)
triviallyRefinedArg :: Id -> Type -> CoqArg
triviallyRefinedArg id typ = (id, typ, TT)

data Theorem = Theorem {cpName :: Id, cpArgs :: [CoqArg], cpType :: Prop, cpbody :: [Tactic]}
instance Show Theorem where
  show (Theorem name args ty bod) =
    "Theorem " ++ name ++ " " ++ unwords (map showArg args) ++ ": " ++ show ty ++ ".\n"
    ++ "Proof.\n"
    ++ unwords (map (show . destructSubsetArg) args)
    ++ intercalate ". " (map show bod) ++ ".\n"
    ++ "Qed.\n"
-- data Proof = IndProof {bod :: ProofBod  , proofIndArg :: (Id,Int)} | NIndProof {bod :: PrBod}
showArg :: CoqArg -> String
showArg (arg, t, p) = addParens $ (arg ++ ": { v : " ++ show t ++ " | " ++ show p ++ " }")

unrefinedName :: Id -> Id
unrefinedName s = s ++ "_unrefined"

injectIntoSubset :: Id -> String
injectIntoSubset t = addParens $ "# "++ t

projectFromSubset :: CoqArg -> String
projectFromSubset (id, _, _) = addParens $ "` "++ id

data Def = Def {defName :: Id, defArgs:: [Id], defBody :: Expr} | RefDef {name :: Id, args:: [CoqArg], ret:: CoqArg, defBody :: Expr}
instance Show Def where
  show (Def name args body) =
    "Fixpoint " ++ name ++ " " ++ unwords args ++ " :=\n"
    ++ "  " ++ show body ++ ".\n"
  show (RefDef name args (resId, ret, post) body) = refinedDef where
      unrefName = unrefinedName name
      argsList = unwords (map showArg args)
      retWithRefts refts = " {"++ resId ++ ":" ++ show ret ++ " | " ++ refts ++ " }"
      refinedDefinien = "Proof.\n  " ++ unwords (map (show . destructSubsetArg) args) ++ "\n" ++ "  exact (exist (" ++ unrefinedApply ++ ") eq_refl). \n" ++ "Defined.\n"
      refinedDef = "Fixpoint " ++ name ++ " " ++ argsList ++ ": " ++ retWithRefts ("v = " ++ unrefinedApply) ++ " .\n" ++ refinedDefinien
      unrefinedApply = unrefName ++ " " ++ unwords (map projectFromSubset args)


data Constant = Const {id :: Id, body :: Expr}
instance Show Constant where
  show (Const name body) = "Definition " ++ name ++ " := "++ show body ++ ". "

newtype Load = Load {moduleName :: Id}
instance Show Load where
  show (Load name) = "Load " ++ name ++ ".v. "

data NewType = NewType {typeName :: Id, defin :: Type}
instance Show NewType where
  show (NewType name def) = "Notation " ++ name ++ ":= " ++ show def ++ ". "

data Inductive = Inductive {typeId :: Id, constructors :: [(Id, Type)]}
instance Show Inductive where
  show (Inductive typeId constrs) = "Inductive " ++ typeId ++ ": Set := " ++ intercalate " | " (map showBranch constrs) ++ ". " where
    showBranch (id, typ) = id ++ ": " ++ show typ

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


data Pat = Pat {patCon :: Id, patArgs :: [Id]}

instance Show Pat where
  show (Pat c args) = c ++ " " ++ unwords (map filterWeird args)

data Expr = App Id [Expr]
          | Var Id
          | Match Expr Id [(Pat, Expr)]
          | MatchSimple Expr [(Pat, Expr)]
          | Let Id Expr Expr
          | Sym String

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

showAppArg :: Expr -> String
showAppArg app@(App _ (_:_)) = addParens $ show app
showAppArg e = show e

destructSubsetArg :: CoqArg -> Tactic
destructSubsetArg (name, ty, refts) = Destruct (Var name) [[name, name++"p"]] []

data Type = TExpr Expr | TProp Prop | RExpr Id Expr Prop | TFun Type Type
instance Show Type where
  show (TExpr e) = show e
  show (TProp p) = show p
  show (RExpr id typ refts) = "{"++ id ++ ": " ++ show typ ++ "| " ++ show refts ++"}"
  show (TFun dom codom) = addParens $ show dom ++ " -> " ++ show codom

data Prop = PExpr Expr
          | Brel Brel Expr Expr
          | And [Prop]
          | Impl Prop Prop
          | Neg Prop
          | TT
          | FF

instance Show Prop where
  show (PExpr e) = show e
  show (Brel brel e1 e2)  = show e1 ++ " = " ++ show e2
  show (And ps)           = intercalate " /\\ " $ map show ps
  show (Impl ante concl)  = show ante ++ "->" ++ show concl
  show (Neg form)         = "not" ++ addParens (show form)
  show TT                 = "True"
  show FF                 = "False"

data Brel = Eq
instance Show Brel where show Eq = "="

-- Expressions in result of proof should be compared to true.
proofExpr :: Expr -> Prop
proofExpr e = Brel Eq e (Var "true")

trivial = "smt_trivial"

ple = "ple"

apply = "smt_app"

solve = apply

data Tactic = Trivial
            | Ple
            | Apply Expr
            | Destruct {destrExpr :: Expr, destrBinds :: [[Id]], destrBranches :: [[Tactic]]}
            | Induction {indArg :: Id, indVar :: Id, indHyp :: Id, indBranches :: [[Tactic]]}
            | LetTac Id Tactic Tactic
            | Intros [Id]
            | Revert [Id]
            | Now Tactic
            | Solve Expr

toSolve :: Tactic -> Tactic
toSolve (Apply e) = Solve e
toSolve d@Destruct{} = d{destrBranches = map (updateLast toSolve) (destrBranches d)}
toSolve i@Induction{} = i{indBranches  = map (updateLast toSolve) (destrBranches i)}
toSolve t = Now t

instance Show Tactic where
  show Trivial = trivial
  show Ple = ple
  show (Apply e) = apply ++ " " ++ showAppArg e
  show (Solve e) = solve ++ " " ++ showAppArg e
  -- TODO generalize destruct
  show (Destruct (Var n) binds branches) =
      "destruct " ++ n ++ " as [" ++ intercalate " | " (map unwords binds) ++ " ]. "
      ++ showBranches branches
  show (Induction arg var hyp branches) =
      "induction " ++ arg ++ " as [| " ++ unwords [var,hyp] ++ " ]. "
      ++ showBranches branches
  show (LetTac id t1 t2) = "let " ++ filterWeird id ++ " := " ++ addParens (show t1) ++ " in " ++ show t2
  show (Intros ids) = "intros " ++ unwords ids
  show (Revert ids) = "revert " ++ unwords ids
  show (Now t) = "now " ++ show t

showBranches :: [[Tactic]] -> String
showBranches = intercalate ". " . map showBranch
  where showBranch   = intercalate "; " . map show

filterWeird :: String -> String
filterWeird = filter (not . flip elem "$#")