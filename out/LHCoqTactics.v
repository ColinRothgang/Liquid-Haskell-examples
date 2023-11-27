Require Import Notations.
Require Import Logic.
Require Import Specif.

(** to enable rewriting using other relations not just = *)
Require Import Setoid.
(** to rewrite using <-> *)
Require Import Classes.Morphisms_Prop.

Require Export Logic.ProofIrrelevanceFacts.
Require Export Program.Subset.
Require Export Init.Tactics.

Require Import Arith.
Require Import Program.
Require Import omega.OmegaLemmas.
From Equations Require Import Equations.

Require Import Lia.

(** Require Init.Peano.
Require Arith.PeanoNat.*)
Require Classes.RelationClasses.

Require Export ZArith Int.
Open Scope Z_scope.
Open Scope Int_scope.
Require Export Floats.

Load LibTactics.


(** The first two tactics are taken from https://gitlab.mpi-sws.org/iris/stdpp/-/blob/df33944852793fd7a93368b6b0251e9f29a3c4dd/stdpp/tactics.v#L45-78 (they are BSD licensed).*)

Ltac fast_done :=
  solve
    [ eassumption
    | symmetry; eassumption
    | reflexivity ].

Tactic Notation "fast_by" tactic(tac) := tac; fast_done.
(** mimicks Haskell's $ operator in Coq *)
Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

Ltac f_equal_ind :=
  match goal with
  | [ |- ?G ] =>
    tryif
      (tryif assert (~ G); [ injection |]
       then fail else idtac)
    then
      fail "Not an inductive constructor"
    else
      f_equal
  end.

Tactic Notation "if_not_done" tactic(tac) := tryif simpl then tac else idtac.

Ltac simpl_loop :=
  repeat first
    [ fast_done
    | solve [trivial]
    | f_equal_ind
    | progress intros
    | solve [symmetry; trivial]
    | discriminate
    | contradiction
    | intuition discriminate
    | congruence
    | exfalso
    | intros; exfalso
    | split].

Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.

Import BVList.BITVECTOR_LIST.
From Sniper Require Import Sniper. 

Ltac injectivity_in H := injection H; clear H; intros H.
  
Ltac ple := simpl; first [ intuition discriminate | try congruence | simpl_loop (*| eauto*) ]; try f_equal_ind.
Local Ltac split_ple := ple; first [split; split_ple | ple]. (* ple; tryif split then split; split_ple else idtac.*)
Local Ltac intros_ple :=
  let H' := fresh "H" in
  split_ple; intros H'; try injectivity_in H'; simpl in H'.

Ltac smt_trivial := simpl; first [ assumption | intuition discriminate | easy ].


Tactic Notation "smt_ple_tac" tactic(tac) :=
  first [ tac | ple; tac | split_ple; tac (* | intros_ple; tac*) ].
Tactic Notation "smt_ple_simpl_tac" tactic(tac) constr(th) :=
  first [tac| ple; tac | split_ple; tac | simpl in th; simpl; tac | simpl in th; split_ple; tac].

Local Tactic Notation "rewrites" constr(H) :=
  first [smt_ple_tac (rewrite H) | smt_ple_tac (rewrite <- H)].
  
Local Tactic Notation "simpl_rewrite" constr(Happ) :=
  let claim := type of Happ in
  let L' := fresh "L" in
  assert (L': claim); [apply Happ|];
  try first [rewrites L' | simpl in L'; rewrites L'].

Local Tactic Notation "simpl_apply" constr(Happ) :=
  let claim := type of Happ in
  let L' := fresh "L" in
  assert (L': claim); [apply Happ|];
  try first [apply L' | simpl in L'; smt_ple_tac (apply L')].

Local Ltac smt_ap_with th arg := smt_ple_simpl_tac (apply th with arg) th.
Local Ltac smt_ap_with2 th arg arg2 := smt_ple_simpl_tac (apply th with arg arg2) th.
Local Ltac smt_ap_with3 th arg arg2 arg3 := smt_ple_simpl_tac (apply th with arg arg2 arg3) th.

Local Ltac smt_rw_with th arg := smt_ple_simpl_tac (rewrite th with arg) th.
Local Ltac smt_rw_with2 th arg arg2 := smt_ple_simpl_tac (rewrite th with arg arg2) th.
Local Ltac smt_rw_with3 th arg arg2 arg3 := smt_ple_simpl_tac (rewrite th with arg arg2 arg3) th.

Local Ltac smt_rwr_with th arg := smt_ple_simpl_tac (rewrite <- th with arg) th.
Local Ltac smt_rwr_with2 th arg arg2 := smt_ple_simpl_tac (rewrite <- th with arg arg2) th.
Local Ltac smt_rwr_with3 th arg arg2 arg3 := smt_ple_simpl_tac (rewrite <- th with arg arg2 arg3) th.

Tactic Notation "smt_use_rw_rwr_ap" tactic(appl_tac) tactic(rw_tac) tactic(rwr_tac) :=
  first [progress rw_tac | progress rwr_tac | appl_tac].

Ltac smt_use th := first [progress simpl_rewrite th | simpl_apply th].
Ltac smt_use_with th arg := smt_use_rw_rwr_ap (smt_ap_with th arg) (smt_rw_with th arg) (smt_rwr_with th arg).
Ltac smt_use_with2 th arg arg2 := smt_use_rw_rwr_ap (smt_ap_with2 th arg arg2) (smt_rw_with2 th arg arg2) (smt_rwr_with2 th arg arg2).
Ltac smt_use_with3 th arg arg2 arg3:= smt_use_rw_rwr_ap (smt_ap_with3 th arg arg2 arg3) (smt_rw_with3 th arg arg2 arg3) (smt_rwr_with3 th arg arg2 arg3).

Tactic Notation "assertFresh" constr(claim) "as" ident(lem) "using" tactic(tac) :=
  let H := fresh lem in
  assert (H: claim); [try tac|];
  try smt_use H.

Ltac smt_app th :=
  (** first [ rewrite th | ple; rewrite th | split_ple; rewrite th | rewrite <- th | ple; rewrite <- th | split_ple; rewrite <- th| apply th | ple; apply th | split_ple; apply th]; try smt_trivial.*)
  smt_use th; if_not_done (try smt_trivial).
Tactic Notation "smt_app_with" constr(th) constr(arg) := (**first [ rewrite th with arg | ple; rewrite th with arg | split_ple; rewrite th with arg | rewrite <- th with arg | ple; rewrite <- th with arg | split_ple; rewrite <- th with arg | apply th with arg | ple; apply th with arg | split_ple; apply th with arg]; try smt_trivial.*)
  smt_use_with th arg; if_not_done (try smt_trivial).
Tactic Notation "smt_app_with2" constr(th) constr(arg) constr(arg2) :=
  (**try first [ rewrite th with arg arg2 | ple; rewrite th with arg arg2 | split_ple; rewrite th with arg arg2 | rewrite <- th with arg arg2 | ple; rewrite <- th with arg arg2 | split_ple; rewrite <- th with arg arg2 | apply th with arg arg2 | ple; apply th with arg arg2 | split_ple; apply th with arg arg2]; try smt_trivial.*)
  smt_use_with2 th arg arg2; if_not_done (try smt_trivial).
Tactic Notation "smt_app_with3" constr(th) constr(arg) constr(arg2) constr(arg3) :=
  (**try first [ rewrite th with arg arg2 arg3 | ple; rewrite th with arg arg2 arg3 | split_ple; rewrite th with arg arg2 arg3 | rewrite <- th with arg arg2 arg3 | ple; rewrite <- th with arg arg2 arg3 | split_ple; rewrite <- th with arg arg2 arg3 | apply th with arg arg2 arg3 | ple; apply th with arg arg2 arg3 | split_ple; apply th with arg arg2 arg3]; try smt_trivial.*)
  smt_use_with3 th arg arg2 arg3; if_not_done (try smt_trivial).


(** For some reason the below tactic doesn't actually work,
   instead producing "variable m unbound" errors when used *)
(* Tactic Notation "induction_on2" constr(m) constr(n) :=
  generalize dependent n; generalize dependent m;
  induction m; induction n; try first [smt_trivial | destruct m; smt_trivial].*)

(* Ltac induction_on2 m n := generalize dependent n; generalize dependent m; induction m; induction n; try smt_trivial.*)

Ltac repeat_until_done tac :=
  tryif tac; tac then tac; repeat_until_done tac else tac.

Ltac smt_app_ih IH :=
  if_not_done (split_ple; first [smt_app IH; smt_app_ih IH | intros_ple; smt_app_ih IH]).
  (** split_ple; match goal with
  | [ |- _ = _ -> _] =>
      let H' := fresh "H" in
      intros H'; try injectivity_in H'; simpl in H'; (*destruct H' as [->];*) smt_app_ih IH
  | [ |- ?F -> ?G ] =>
      let H' := fresh "H" in
      intros H'; try injectivity_in H'; simpl in H'; smt_app_ih IH
  | [ |- _ ] => smt_app IH
  end.*)

Ltac smt_done := if_not_done (try ple); if_not_done (try smt_trivial); if_not_done (try snipe).

(* equality on subset types with proof irrelevance *)
Notation "x `= y" := (@eq _ (`x) (`y)) (at level 70).

Definition inject_into_subset_type (A:Type) (x:A) (H:Prop) (p:H): {x:A | H} := (exist x p).
Definition inject_into_trivial_subset_type (A:Type) (x:A) : {v:A | True} := (exist x I).
Notation "# x" := (exist x I) (at level 60).


Definition CoqInt := Z.
Definition CoqFloat := float.
