module Preamble(lhPreamble, preamble) where

import LH
import Prelude
import CoreToLH

lhPreamble :: [SourceContent]
lhPreamble = [natDecl] where
  -- loadTactics = LH.Import "LHCoqTactics"
  [nat, zero, suc] = map CoreToLH.fixIllegalName ["N", "Z","Suc"]
  natDecl = LH.Data nat Nothing [(zero, []), (suc, [LH.TDat nat []])]

preamble :: [String]
preamble = [load_tactics, zscope, intscope]
  where
    load_tactics    = "Add LoadPath \"out\" as Project. \nLoad LHCoqTactics." -- \nNotation \"x ↠ H p\" := (subCast _ _ H x p) (at level 60).\nNotation \"x ↠ H\" := (subCast _ _ H x _) (at level 60)." --"Require LHCoqTactics."
    zscope = "Open Scope Z_scope."
    intscope = "Open Scope Int_scope."
    ltacs = [ple, smtTrivial, smtApp, smtSolve]
    natDecl    = "Inductive N:Set := Z : N | Suc: N -> N. "
                ++ "\nNotation \"@ x\" := (inject_into_trivial_subset_type N x) (at level 60). "
    ple        = "Ltac ple := simpl."
    smtTrivial = "Ltac smt_trivial := simpl; first [ assumption | intuition discriminate | easy]."
    smtApp     = "Ltac smt_app th := first "   ++ appTacList ++ "; try smt_trivial."
    smtSolve   = "Ltac smt_solve th := solve [ now rewrite th | now ple; rewrite th | now apply th | now ple; apply th]."
    appTacList = "[ rewrite th | ple; rewrite th | apply th | ple; apply th]"
