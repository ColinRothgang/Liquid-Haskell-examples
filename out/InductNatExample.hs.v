Load LHCoqTactics. 
Inductive N: Set := Z: N | Suc: (N -> N). 
Load IntNatExample. 
Definition add_unrefined (m: N) (n: N): N. 
Proof.
  induction m as [| m IHm ]. now exact (n). now exact (Suc IHm).
Defined.

Definition add (m: N) (n: N): { v : N | add_unrefined m n = v } .
Proof.
  exact (exist (add_unrefined m n) eq_refl). 
Defined.

Definition mult_unrefined (m: N) (n: N): N. 
Proof.
  induction m as [| m IHm ]. now exact (Z). now exact (` (add n IHm)).
Defined.

Definition mult (m: N) (n: N): { v : N | mult_unrefined m n = v } .
Proof.
  exact (exist (mult_unrefined m n) eq_refl). 
Defined.

Theorem add_zero_l (n: N): (` (add Z n)) = n.
Proof.
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.

Theorem add_suc_l (m: N) (n: N): Suc (` (add m n)) = (` (add (Suc m) n)).
Proof.
  induction m as [| m IHm ]. now smt_trivial. smt_app IHm.
Qed.

Theorem add_zero_r (n: N): (` (add n Z)) = n.
Proof.
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.

Theorem add_suc_r (m: N) (n: N): Suc (` (add m n)) = (` (add m (Suc n))).
Proof.
  induction m as [| m IHm ]. now smt_trivial. smt_app IHm.
Qed.

Theorem add_comm (m: N) (n: N): (` (add m n)) = (` (add n m)).
Proof.
  induction m as [| m IHm ]. smt_app (add_zero_r n). smt_app IHm. smt_app (add_suc_r n m).
Qed.

Theorem add_assoc (m: N) (n: N) (o: N): (` (add m (` (add n o)))) = (` (add (` (add m n)) o)).
Proof.
  induction m as [| m IHm ]. now smt_trivial. smt_app IHm.
Qed.

Theorem mult_suc_r (n: N) (m: N): (` (mult n (Suc m))) = (` (add n (` (mult n m)))).
Proof.
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn. smt_app (add_assoc m n (` (mult n m))). smt_app (add_comm m n). smt_app (add_assoc n m (` (mult n m))).
Qed.

Theorem mult_zero_l (n: N): (` (mult Z n)) = Z.
Proof.
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.

Theorem mult_suc_l (m: N) (n: N): (` (mult (Suc m) n)) = (` (add n (` (mult m n)))).
Proof.
  destruct m as [ | m ]. now smt_trivial. now smt_trivial.
Qed.

Theorem mult_zero_r (n: N): (` (mult n Z)) = Z.
Proof.
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.

Definition one := Suc Z. 
Definition two := Suc one. 
Theorem mult_one_r (n: N): (` (mult n one)) = n.
Proof.
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.
