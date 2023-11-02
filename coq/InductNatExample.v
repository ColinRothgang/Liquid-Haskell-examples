Load LHCoqTactics.
Require Init.Peano.
Require Arith.PeanoNat.
Require Classes.RelationClasses.

Inductive N:Set := Z : N | Suc: N -> N.

Fixpoint toInt (n:N) :=
  match n with
  | Z => 0
  | Suc n => S (toInt n)
  end.

Fixpoint add m n :=
  match m with 
  | Z  => n 
  | Suc m => Suc (add m n) end.

(** Section Addition definition lemmas: *)
Theorem add_zero_l (n: N): add Z n = n.
Proof.
  induction n.
  - smt_trivial.
  - smt_trivial.
Qed.

Theorem add_suc_l (m:N) (n: N): Suc (add m n) = add (Suc m) n.
Proof. 
  induction n.
  - smt_trivial.
  - smt_trivial.
Qed.

(** Addition with right zero *)
Theorem add_zero_r (n: N): add n Z = n.
Proof.
  induction n.
  - smt_trivial.
  - smt_app IHn.
Qed.

(** Addition with right sucessor *)
Theorem add_suc_r (m: N) (n: N): Suc (add m n) = add m (Suc n).
Proof.
  induction m as [|m IHm].
  - smt_trivial.
  - smt_app IHm.
Qed.

(** Addition commutes *)
Theorem add_comm (m:N) (n:N): add m n = add n m.
Proof.
  induction m as [|m IHm].
  - smt_app add_zero_r.
  - smt_app IHm. smt_app add_suc_r.
Qed.

(* Addition  is associative *)
Theorem add_assoc (m:N) (n:N) (o:N): add m (add n o) = add (add m n) o.
Proof.
  induction m as [|m IHm].
  - smt_trivial.
  - smt_app IHm.
Qed.


(** Multiplication of natural numbers *)
Fixpoint mult m n :=
  match m with
  | Z => Z
  | Suc m => add n (mult m n)
end.

(** Multiplication definition lemmas: *)
Theorem mult_zero_l (n:N): mult Z n = Z.
Proof.
  induction n as [|n IHn].
  - smt_trivial.
  - smt_app IHn.
Qed.

Theorem mult_suc_l (m:N) (n:N): mult (Suc m) n = add n (mult m n).
Proof.
  induction m as [|m IHm].
  - smt_trivial.
  - smt_trivial.
Qed.

(** Multiplication with right zero *)
Theorem mult_zero_r (n:N): mult n Z = Z.
Proof.
  induction n as [|n IHn].
  - smt_trivial.
  - smt_app IHn.
Qed.

(** Multiplication with right sucessor *)
Theorem mult_suc_r (n:N) (m:N): mult n (Suc m) = add n (mult n m).
Proof.
  induction n as [|n IHn].
  - smt_trivial.
  - smt_app IHn. 
    
    (** Obvious translation, nor working:
    smt_app add_assoc.
    smt_app add_comm. 
    smt_app add_assoc.
    *)
    smt_app_with3 add_assoc (m) (n) (mult n m).
    smt_app_with3 add_assoc n m (mult n m).
    smt_app_with2 add_comm m n. 
Qed.

Definition one := Suc Z.
Definition two := Suc one.

(** Multiplication with right 1 *)
Theorem mult_one_r (n:N): mult n one = n.
Proof.
  induction n as [|n IHn].
  - smt_trivial.
  - smt_app IHn. 
Qed.

(** Multiplication with left 1 *)
Theorem mult_one_l (n:N): mult one n = n.
Proof.
  induction n as [|n IHn].
  - smt_trivial.
  - smt_app add_zero_r.
Qed.

(** Addition distributes over right multiplication *)
Theorem add_dist_rmult (m:N) (n:N) (o:N): mult (add m n) o = add (mult m o) (mult n o).
Proof.
  induction m as [|m IHm].
  - smt_trivial.
  - smt_app IHm. 
    (** rewrite <- add_assoc with o (mult m o) (mult n o).*)
    smt_app_with3 add_assoc o (mult m o) (mult n o).
Qed.

(** Addition distributes over left multiplication *)
Theorem add_dist_lmult (m:N) (n:N) (o:N): mult m (add n o) = add (mult m n) (mult m o).
Proof.
  induction n as [|n IHn].
  - smt_app_with mult_zero_r m.
  - smt_app_with2 mult_suc_r m (add n o).
    smt_app IHn.
    smt_app_with3 add_assoc m (mult m n) (mult m o).
    smt_app_with2 mult_suc_r m n.
Qed.

(** Here we encounter the issue that the Coq tactics solve the goal earlier than expected *)
Theorem mult_assoc (m:N) (n:N) (o:N): mult (mult m n) o = mult m (mult n o).
Proof.
  induction m as [|m IHm].
  - smt_trivial.
  - smt_app_with3 add_dist_rmult n (mult m n) o. 
    (* smt_app IHm.*)
Qed.

Fixpoint eqN m n :=
  match (m, n) with
  | (Z, Z) => True
  | (Suc m, Suc n) => eqN m n
  | _ => False
end.

(* Since LH is much better at inferring postconditions automagically we don't annotate them
(in this case by adding return {p:Prop | p <-> (toInt m >= toInt n)} in the match)
but instead proof them as a seperate theorem *)
Fixpoint geqN m n :=
  match (m, n) with
  | (Z, Z) => True
  | (Suc m, Z) => True
  | (Z, Suc n) => False
  | (Suc m, Suc n) => geqN m n
  end.

(** Theorem stating postcondition automagically proven by LH.
Proof is default proof for any such property
See comment for Theorem eq_equal for explanation why this the the default shape of simple proofs by induction on two variables.
 *)
Theorem geqN_def (m:N) (n:N): geqN m n <-> (toInt m >= toInt n).
Proof.
  generalize dependent n. generalize dependent m.
  induction m; induction n; try first [smt_trivial | destruct m'; smt_trivial].
  smt_app_ih IHm.
Qed.

Definition leqN m n := geqN n m.

Fixpoint geN m n :=
  match (m, n) with
  | (Z, _) => False
  | (Suc _, Z) => True
  | (Suc m, Suc n) => geN m n
  end.

(** Default proof again *)
Theorem geN_def (m:N) (n: N): geN m n <-> (toInt m > toInt n).
Proof.
  generalize dependent n; generalize dependent m;
  induction m; induction n; try first [smt_trivial | destruct m'; smt_trivial].
  smt_app_ih IHm.
Qed.

Definition leN m n := geN n m.

Theorem ge_measure (m:N) (n:N): geN m n <-> (toInt m > toInt n).
Proof.
  generalize dependent n. generalize dependent m.
  induction m as [|m IHm]; induction n as [|n IHn];  try first [smt_trivial | destruct m'; smt_trivial].
  smt_app_ih IHm.
Qed.

(* Here we have to explicitely destruct m in the case m:= Suc m', n:= Z for smt_trivial to succeed.
 Still the "default proof" works here. *)
Theorem ge_geq_suc (m:N) (n:N): geN m n <-> geqN m (Suc n).
Proof.
  generalize dependent n. generalize dependent m.
  induction m as [|m' IHm]; induction n as [|n' IHn].
  - smt_trivial.
  - smt_trivial.
  - destruct m'; smt_trivial.
  - smt_app_ih IHm.
Qed.

Theorem ge_zero (n:N): (geqN n Z /\ n <> Z) -> geN n Z.
Proof.
  induction n as [|n IHn];  try smt_trivial.
  (*smt_app_ih IHn.*)
Qed.

(** Two issues are demonstrated in the subsequent lemma:
In the first inductive case (base case) we need to explicitely destruct n, for the proof to succeed
In the second case, the (necessary) simplification following first tactic already
solves the proof goal, so the second argument must *not* be translated from LH to Coq
*)

Theorem add_mono_r (m:N) (n:N): ((geqN (add m n) m) /\ (geN n Z -> geN (add m n) m)).
Proof.
  induction m as [|m IHm].
  - destruct n; ple.
  - smt_app_with2 add_suc_r m n. 
Qed.

Theorem add_mono_l (m:N) (n:N): geqN (add m n) n /\ (geN m Z -> geN (add m n) n).
Proof.
  smt_app_with2 add_comm m n.
  smt_app add_mono_r.
(**
  For reasons I don't understand, the below tactic doesn't succeed (using apply with directly gives error:
  not the right number of missing arguments (expected 0),
  so it looks as though apply doesn't accept argument for the theorem that does take arguments):
  smt_app_with2 add_mono_r n m.*)
Qed.

(** The following theorem is rather hard to translate:
   For start we need to do induction on both m and n,
   so we reintroduce them as universally quantified variables with generalize dependent (in order opposite to the order in which we do induction),
   then we do induction on first m then n, immediately finishing the trivial cases (they are all trivial in LH, so it is clear in translation which cases still need to be treated)
   Then, we need to split the goal (done by split_ple the firststep in smt_app_ih).
   Finally we move the antecedent into the context as a hypothesis, simplify it (using injection_in)
   and finish the proof with an invocation of smt_app IHm, the first and (due to the generalize dependents) stronger induction principle
*)
Theorem eq_equal (m:N) (n:N): eqN m n <-> m = n.
Proof.
  generalize dependent n. generalize dependent m.
  induction m as [|m IHm]; induction n as [|n IHn]; try smt_trivial.
  smt_app_ih IHm.
Qed.

(** Here for some reason the smt_app_with2 tactics don't work, maybe because the rewrite default to a setoid_rewrite and those don't support the withs *)
Theorem eq_sym (m:N) (n:N): eqN m n <-> eqN n m.
Proof.
  split.
  - smt_app eq_equal. smt_app eq_equal.
  - smt_app eq_equal. smt_app eq_equal.
Qed.  

Theorem eq_geq (m:N) (n:N): eqN m n -> geqN m n.
Proof.
  generalize dependent n. generalize dependent m.
  induction m as [|m IHm]; induction n as [|n IHn]; try first [smt_trivial | destruct m'; smt_trivial].
  (* smt_app_ih IHm. *)
Qed.

Theorem geq_refl (n:N): geqN n n.
Proof.
  induction n as [|n IHn].
  - smt_trivial.
  - smt_app_ih IHn.
Qed.

Theorem geq_trans (m:N) (n:N) (o:N): (geqN m n /\ geqN n o) -> geqN n o.
  generalize dependent o. generalize dependent n. generalize dependent m.
  induction m; induction n; induction o; first [ smt_trivial | destruct m'; smt_trivial | destruct m'; destruct n'; smt_trivial].
  (* smt_app_ih IHm *)
Qed.

Theorem le_geq (m:N) (n:N): geqN m n <-> not (leN m n).
Proof.
  generalize dependent n. generalize dependent m.
  induction m; induction n; try first [ smt_trivial | destruct m'; smt_trivial].
Qed. 

Theorem ge_geq (m:N) (n:N): geN m n -> geqN m n.
Proof.
  generalize dependent n. generalize dependent m.
  induction m; induction n; try first [ smt_trivial | destruct m'; smt_trivial].
Qed.

Theorem ge_anti_comm (m:N) (n:N): geN m n -> not (geN n m).
Proof.
  generalize dependent n. generalize dependent m.
  induction m; induction n; try first [ smt_trivial | destruct m'; smt_trivial].
  (* smt_app_ih IHm. *)
Qed.

Theorem ge_irreflexive (m:N) (n:N): geN m n -> not (eqN m n).
Proof.
  generalize dependent n. generalize dependent m.
  induction m; induction n; try first [ smt_trivial | destruct m'; smt_trivial].
Qed.

Theorem ge_trans (m:N) (n:N) (o:N): geN m n /\ geN n o -> geN m o.
Proof.
  generalize dependent o. generalize dependent n. generalize dependent m.
  induction m; induction n; induction o; try first [ smt_trivial | destruct m'; smt_trivial | destruct m'; destruct n'; smt_trivial].
  (* smt_app_ih IHm. *)
Qed.

Theorem ge_eq_trans (m:N) (n:N) (o:N): geN m n /\ eqN n o -> geN m o.
Proof.
  generalize dependent o. generalize dependent n. generalize dependent m.
  induction m; induction n; induction o; try first [ smt_trivial | destruct m'; smt_trivial | destruct m'; destruct n'; smt_trivial].
  (* smt_app_ih IHm. *)
Qed.

Theorem geq_suc_l (m:N) (n: {v:N | geqN m v}): geqN (Suc m) (proj1_sig n).
Proof.
  destruct n as [n H].
  generalize dependent n. generalize dependent m.
  induction m; induction n; try first [smt_trivial | destruct m'; smt_trivial].
  - smt_app_ih IHm. 
Qed.

Theorem geq_ge_eq (m:N) (n:N): geqN m n <-> (geN m n \/ eqN m n).
Proof.
  generalize dependent n. generalize dependent m.
  induction m; induction n; try first [smt_trivial | destruct m'; smt_trivial].
  (* smt_app_ih IHm *)
Qed.

Theorem geq_not_le (m:N) (n:N): geqN m n <-> not (leN m n).
Proof.
  generalize dependent n. generalize dependent m.
  induction m; induction n; try first [smt_trivial | destruct m'; smt_trivial].
  (* smt_app_ih IHm *)
Qed.

Theorem ge_eq_le_exhausitve (m:N) (n:N): geN m n \/ eqN m n \/ leN m n.
Proof.
  generalize dependent n. generalize dependent m.
  induction m; induction n; try first [smt_trivial | destruct m'; smt_trivial].
  (* smt_app_ih IHm *)
Qed.

(** This theorem cannot be translated so easily *)
Theorem mult_zero (m:N) (n:N): (m <> Z /\ n <> Z) -> geqN (mult m n) n.
Proof.
  induction m as [|m IHm].
  - smt_trivial.
  - intros [H H'].
    (* Can replace the following 3 lines by just smt_app_with2 add_comm n (mult m n). *)
    assert (E: mult (Suc m) n = add (mult m n) n).
    { smt_app_with2 add_comm n (mult m n). }
    smt_app E.
    (* smt_app_with ge_zero n. *)
    smt_app add_mono_l.
    (* smt_app_with2 add_mono_l (mult m n) n.
    smt_app_with2 ge_geq (add (mult m n) n) n.*)
Qed.

Theorem subt_def_suc_suc_lemma (m': N) (n':N): geqN (Suc m') (Suc n') -> geqN m' n'.
Proof.
  simpl. intros_ple.
Qed.

(* This somewhat unorthodox way of defining subt lets us do reasoning inside the very definition *)
Fixpoint subt (m:N) (n: {v:N | geqN m v}) : N.
Proof.
  destruct n as [n H].
  induction n as [|n'].
  - exact m.
  - induction m as [|m'].
    + simpl in H. exfalso. apply H.
    + apply subt_def_suc_suc_lemma in H.
      exact (subt m' (exist n' H)).
Defined.

Theorem subt_def (m:N) (n: {v: N | geqN m v}): (proj1_sig n <> Z) <-> (toInt (subt m n)  < toInt m).
Proof.
  destruct n as [n H].
  generalize dependent n. generalize dependent m.
  induction m as [|m' IHm]; try (destruct n; smt_trivial). simpl in IHm.
  induction n as [|n' IHn]; try smt_trivial.
  intros H. split_ple.
  assert (H': geqN m' n').
  { apply subt_def_suc_suc_lemma in H. smt_app H. }
  intros Q; clear Q.
  assert (IH: (n' <> Z) -> toInt (subt m' (exist n' (subt_def_suc_suc_lemma m' n' H))) < toInt m').
  - smt_app_ih IHm.
  - destruct n' eqn:E.
    + destruct m'; smt_trivial.
    + assert (L: toInt (subt m' (exist (Suc n) (subt_def_suc_suc_lemma m' (Suc n) H))) < toInt m').
      * apply IH. ple.
      * smt_done.
Qed.

(* The problem here is that the induction hypothesis contains a different proof of m >= n, than the one we have in the proof.
 Using the Proof irrelevance lemma for subset types solves that issue. *)
Theorem subt_self (m:N) (n: N) (H: eqN m n): subt m (exist n (eq_geq m n H)) = Z.
Proof.
  generalize dependent n. generalize dependent m.
  induction m; induction n; try first [smt_trivial | destruct m'; smt_trivial].
  intros_ple.
  assert (proof_irrevelance: (exist n (subt_def_suc_suc_lemma m n (eq_geq (Suc m) (Suc n) H))) = (exist n (eq_geq m n H))).
  { apply subset_eq_compat. reflexivity. }
  smt_app proof_irrelevance.
Qed.

Theorem add_subt_wff_lemma (m:N) (n:N): geqN (add m n) n.
Proof.
  smt_app add_mono_l.
Qed.

(* Here we actually have to infer a witness for add m n >= n to even state the theorem *)
Theorem add_subt (m:N) (n:N): subt (add m n) (exist n (add_subt_wff_lemma m n)) = m.
Proof.
  generalize dependent m. generalize dependent n.
  induction n as [|n' IHn]; induction m as [|m' IHm]; try smt_trivial.
  - smt_app_with add_zero_r m'.
  - smt_app_with add_zero_r n'.
    assert (H: eqN (add n' Z) (add n' Z)).
    { simpl. clear IHn. induction n' as [|n'' IHn'']; smt_trivial. }
    replace (exist (add n' Z) (subt_def_suc_suc_lemma (add n' Z) (add n' Z) (add_subt_wff_lemma Z (Suc (add n' Z))))) with (exist (add n' Z) (eq_geq (add n' Z) (add n' Z) H)); [| smt_app subset_eq_compat].
    smt_app subt_self.
  - ple.
    (* Now we cannot replace m' + (Suc n') with (Suc m') + n' (to apply IHn), as then the subset proof for n' no longer applies *)
    (* replace (exist n' (subt_def_suc_suc_lemma (add m' (Suc n')) n' (add_subt_wff_lemma (Suc m') (Suc n'))))
      with  (exist n' (subt_def_suc_suc_lemma (add (Suc m') n') n' (add_subt_wff_lemma (Suc m') (Suc n')))); [| apply subset_eq_compat].
    replace (add m' (Suc n')) with (add (Suc m') n'); [| rewrite <- add_suc_r; rewrite add_suc_l; reflexivity ].*)
    assert (K: geqN (add m' (Suc n')) n').
    { exact ((subt_def_suc_suc_lemma (add m' (Suc n')) n' (add_subt_wff_lemma (Suc m') (Suc n')))). }
    replace (exist n' (subt_def_suc_suc_lemma (add m' (Suc n')) n' (add_subt_wff_lemma (Suc m') (Suc n')))) with (exist n' K); [|apply subset_eq_compat; reflexivity].
    (* We are stuck here again, unfortunately:
    rewrite <- add_suc_r. rewrite add_suc_l.
    rewrite proof_irrelevance. smt_app subt_self.
Qed. *)
Admitted.
