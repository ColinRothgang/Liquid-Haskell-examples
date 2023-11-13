Load LHCoqTactics.
Inductive N:Set := Z : N | Suc: N -> N. 
Notation "@ x" := (inject_into_trivial_subset_type N x) (at level 60). 


Fixpoint toInt_unrefined n :=
  match n with | Z  => I# 0 | Suc n => + Int fNumInt (I# 1) (toInt_unrefined n) end.

Fixpoint toInt (n: { v : N | True }):  {v:Int | v = toInt_unrefined (` n) } .
Proof.
  destruct n as [n np ]. 
  exact (exist (toInt_unrefined (` n)) eq_refl). 
Defined.

Fixpoint add_unrefined m n :=
  match m with | Z  => n | Suc m => Suc (add_unrefined m n) end.

Fixpoint add (m: { v : N | True }) (n: { v : N | True }):  {v:N | v = add_unrefined (` m) (` n) } .
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  exact (exist (add_unrefined (` m) (` n)) eq_refl). 
Defined.

Fixpoint mult_unrefined m n :=
  match m with | Z  => Z | Suc m => add n (mult_unrefined m n) end.

Fixpoint mult (m: { v : N | True }) (n: { v : N | True }):  {v:N | v = mult_unrefined (` m) (` n) } .
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  exact (exist (mult_unrefined (` m) (` n)) eq_refl). 
Defined.

Theorem add_zero_l (n: { v : N | True }): add Z n = n.
Proof.
destruct n as [n np ]. induction n as [| n add_zero_l ]. smt_app trivial. smt_app add_zero_l.
Qed.

Theorem add_suc_l (m: { v : N | True }) (n: { v : N | True }): Suc (add m n) = add (Suc m) n.
Proof.
destruct m as [m mp ].  destruct n as [n np ]. revert n. induction m as [| m add_suc_l ]. intros n; smt_app trivial. intros n; smt_app (add_suc_l n).
Qed.

Theorem add_zero_r (n: { v : N | True }): add n Z = n.
Proof.
destruct n as [n np ]. induction n as [| n add_zero_r ]. smt_app trivial. smt_app add_zero_r.
Qed.

Theorem add_suc_r (m: { v : N | True }) (n: { v : N | True }): Suc (add m n) = add m (Suc n).
Proof.
destruct m as [m mp ].  destruct n as [n np ]. revert n. induction m as [| m add_suc_r ]. intros n; smt_app trivial. intros n; smt_app (add_suc_r n).
Qed.

Theorem add_comm (m: { v : N | True }) (n: { v : N | True }): add m n = add n m.
Proof.
destruct m as [m mp ].  destruct n as [n np ]. revert n. induction m as [| m add_comm ]. intros n; smt_app (add_zero_r n). intros n; smt_app (add_comm n); smt_app (add_suc_r n m).
Qed.

Theorem add_assoc (m: { v : N | True }) (n: { v : N | True }) (o: { v : N | True }): add m (add n o) = add (add m n) o.
Proof.
destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. revert n o. induction m as [| m add_assoc ]. intros n o; smt_app trivial. intros n o; smt_app (add_assoc n o).
Qed.

Theorem mult_suc_r (n: { v : N | True }) (m: { v : N | True }): mult n (Suc m) = add n (mult n m).
Proof.
destruct n as [n np ].  destruct m as [m mp ]. revert m. induction n as [| n mult_suc_r ]. intros m; smt_app trivial. intros m; smt_app (mult_suc_r m); smt_app (add_assoc m n (mult n m)); smt_app (add_comm m n); smt_app (add_assoc n m (mult n m)).
Qed.

Theorem mult_zero_l (n: { v : N | True }): mult Z n = Z.
Proof.
destruct n as [n np ]. induction n as [| n mult_zero_l ]. smt_app trivial. smt_app mult_zero_l.
Qed.

Theorem mult_suc_l (m: { v : N | True }) (n: { v : N | True }): mult (Suc m) n = add n (mult m n).
Proof.
destruct m as [m mp ].  destruct n as [n np ]. destruct m as [ | m ]. smt_app trivial. smt_app trivial.
Qed.

Theorem mult_zero_r (n: { v : N | True }): mult n Z = Z.
Proof.
destruct n as [n np ]. induction n as [| n mult_zero_r ]. smt_app trivial. smt_app mult_zero_r.
Qed.

Fixpoint one  :=
  Suc Z.

Fixpoint two  :=
  Suc one.

Theorem mult_one_r (n: { v : N | True }): mult n one = n.
Proof.
destruct n as [n np ]. induction n as [| n mult_one_r ]. smt_app trivial. smt_app mult_one_r.
Qed.
