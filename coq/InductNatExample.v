Ltac smt_trivial := simpl; first [ assumption | intuition discriminate | easy].
Ltac by_arg arg := simpl; rewrite arg; trivial.

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
  - by_arg IHn.
Qed.

(** Addition with right sucessor *)
Theorem add_suc_r (m: N) (n: N): Suc (add m n) = add m (Suc n).
Proof.
  induction m as [|m IHm].
  - smt_trivial.
  - by_arg IHm.
Qed.