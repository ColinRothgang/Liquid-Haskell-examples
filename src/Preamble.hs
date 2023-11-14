module Preamble(lhPreamble) where

import LH
import Prelude

lhPreamble :: [SourceContent]
lhPreamble = [loadTactics, natDecl] where
  loadTactics = LH.Import "LHCoqTactics"
  natDecl = LH.Data "N" Nothing [("Z", []), ("Suc", [LH.TDat "N" []])]

{-
preamble :: [String]
preamble = [load_tactics, natDecl]
  where
    load_tactics    = "Load LHCoqTactics."
    ltacs = [ple, smtTrivial, smtApp, smtSolve]
    natDecl    = "Inductive N:Set := Z : N | Suc: N -> N. "
                ++ "\nNotation \"@ x\" := (inject_into_trivial_subset_type N x) (at level 60). "
    ple        = "Ltac ple := simpl."
    smtTrivial = "Ltac smt_trivial := simpl; first [ assumption | intuition discriminate | easy]."
    smtApp     = "Ltac smt_app th := first "   ++ appTacList ++ "; try smt_trivial."
    smtSolve   = "Ltac smt_solve th := solve [ now rewrite th | now ple; rewrite th | now apply th | now ple; apply th]."
    appTacList = "[ rewrite th | ple; rewrite th | apply th | ple; apply th]"
-}