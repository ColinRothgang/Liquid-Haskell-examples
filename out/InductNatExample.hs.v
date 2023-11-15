Load LHCoqTactics. 
Inductive N: Set := Z: N | Suc: (N -> N). 
Load IntNatExample. 
Definition add_unrefined (m: N) (n: N): N. 
Proof.
 revert n. induction m as [| m IHm ]. intros n; now exact (n). intros n; now exact (Suc (IHm n)).
Defined.

Definition add (m: N) (n: N): { v : N | add_unrefined m n = v } .
Proof.
   
  exact (exist (add_unrefined m n) eq_refl). 
Defined.

Definition mult_unrefined (m: N) (n: N): N. 
Proof.
 revert n. induction m as [| m IHm ]. intros n; now exact (Z). intros n; now exact (` (add n (IHm n))).
Defined.

Definition mult (m: N) (n: N): { v : N | mult_unrefined m n = v } .
Proof.
   
  exact (exist (mult_unrefined m n) eq_refl). 
Defined.

Theorem add_zero_l (n: N): (` (add Z n)) = n.
Proof.
induction n as [| n IHn ]. smt_app trivial. smt_app IHn.
Qed.

Theorem add_suc_l (m: N) (n: N): Suc (` (add m n)) = (` (add (Suc m) n)).
Proof.
 revert n. induction m as [| m IHm ]. intros n; smt_app trivial. intros n; smt_app (IHm n).
Qed.

Theorem add_zero_r (n: N): (` (add n Z)) = n.
Proof.
induction n as [| n IHn ]. smt_app trivial. smt_app IHn.
Qed.

Theorem add_suc_r (m: N) (n: N): Suc (` (add m n)) = (` (add m (Suc n))).
Proof.
 revert n. induction m as [| m IHm ]. intros n; smt_app trivial. intros n; smt_app (IHm n).
Qed.

Theorem add_comm (m: N) (n: N): (` (add m n)) = (` (add n m)).
Proof.
 revert n. induction m as [| m IHm ]. intros n; smt_app (add_zero_r n). intros n; smt_app (IHm n); smt_app (add_suc_r n m).
Qed.

Theorem add_assoc (m: N) (n: N) (o: N): (` (add m (` (add n o)))) = (` (add (` (add m n)) o)).
Proof.
  revert n o. induction m as [| m IHm ]. intros n o; smt_app trivial. intros n o; smt_app (IHm n o).
Qed.

Theorem mult_suc_r (n: N) (m: N): (` (mult n (Suc m))) = (` (add n (` (mult n m)))).
Proof.
 revert m. induction n as [| n IHn ]. intros m; smt_app trivial. intros m; smt_app (IHn m); smt_app (add_assoc m n (` (mult n m))); smt_app (add_comm m n); smt_app (add_assoc n m (` (mult n m))).
Qed.

Theorem mult_zero_l (n: N): (` (mult Z n)) = Z.
Proof.
induction n as [| n IHn ]. smt_app trivial. smt_app IHn.
Qed.

Theorem mult_suc_l (m: N) (n: N): (` (mult (Suc m) n)) = (` (add n (` (mult m n)))).
Proof.
 destruct m as [ | m ]. smt_app trivial. smt_app trivial.
Qed.

Theorem mult_zero_r (n: N): (` (mult n Z)) = Z.
Proof.
induction n as [| n IHn ]. smt_app trivial. smt_app IHn.
Qed.

Definition one := Suc Z. 
Definition two := Suc one. 
Theorem mult_one_r (n: N): (` (mult n one)) = n.
Proof.
induction n as [| n IHn ]. smt_app trivial. smt_app IHn.
Qed.
