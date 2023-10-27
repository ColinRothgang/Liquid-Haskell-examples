Load LHCoqTactics.

Inductive N:Set := Z : N | Suc: N -> N.

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

Theorem mult_assoc (m:N) (n:N) (o:N): mult (mult m n) o = mult m (mult n o).
Proof.
  induction m as [|m IHm].
  - smt_trivial.
  - smt_app_with3 add_dist_rmult n (mult m n) o. 
    smt_app IHm.
Qed.

Fixpoint eqN m n :=
  match (m, n) with
  | (Z, Z) => True
  | (Suc m, Suc n) => eqN m n
  | _ => False
end.

Fixpoint geqN m n :=
  match (m, n) with
  | (_, Z) => True
  | (Z, Suc n) => False
  | (Suc m, Suc n) => geqN m n
end.

Fixpoint geN m n :=
  match (m, n) with
  | (Z, _) => False
  | (Suc _, Z) => True
  | (Suc m, Suc n) => geN m n
end.


(** Two issues are demonstrated in the subsequent lemma:
In the first inductive case (base case) we need to destruct n, for the proof to succeed
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
  smt_app_with2 add_mono_r (m:=n) (n:=m).*)
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

Theorem mult_zero (m:N) (n:N): m <> Z /\ n <> Z -> geqN (mult m n) n.
Proof.
  induction m as [|m IHm].
  - smt_trivial.
  - smt_app_with2 mult_suc_l m n.
    smt_app_with2 add_comm n (mult m n).
    smt_app_with ge_zero n.
    smt_app_with2 add_mono_l (mult m n) n.
    smt_app_with2 ge_geq (add (mult m n) n) n.
Qed.



