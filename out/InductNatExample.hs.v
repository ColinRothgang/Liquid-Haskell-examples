Load LHCoqTactics. 
Inductive N: Set := Z: N | Suc: (N -> N). 
Load IntNatExample. 
Fixpoint add_unrefined (m: N) (n: N): (v: N) .
Proof.
 destruct m as [ | m ]. now exact (exist n eq_refl). now exact (exist Suc (add_unrefined m n) eq_refl).
Qed.

Fixpoint add (m: N) (n: N):  {v:N | v = add_unrefined m (` n) } .
Proof.
   
  exact (exist (add_unrefined (inject_into_subset_type N m True I) n) eq_refl). 
Defined.

Fixpoint mult_unrefined (m: N) (n: N): (v: N) .
Proof.
 destruct m as [ | m ]. now exact (exist Z eq_refl). now exact (exist add (inject_into_subset_type N n True I) (mult_unrefined m n) eq_refl).
Qed.

Fixpoint mult (m: N) (n: N):  {v:N | v = mult_unrefined m (` n) } .
Proof.
   
  exact (exist (mult_unrefined (inject_into_subset_type N m True I) n) eq_refl). 
Defined.

Theorem add_zero_l (n: N): add Z n = n.
Proof.
destruct n as [ | n ]. smt_app trivial. smt_app (add_zero_l n).
Qed.

Theorem add_suc_l (m: N) (n: N): Suc (add m n) = add (Suc m) n.
Proof.
 destruct m as [ | m ]. smt_app trivial. smt_app (add_suc_l m n).
Qed.

Theorem add_zero_r (n: N): add n Z = n.
Proof.
destruct n as [ | n ]. smt_app trivial. smt_app (add_zero_r n).
Qed.

Theorem add_suc_r (m: N) (n: N): Suc (add m n) = add m (Suc n).
Proof.
 destruct m as [ | m ]. smt_app trivial. smt_app (add_suc_r m n).
Qed.

Theorem add_comm (m: N) (n: N): add m n = add n m.
Proof.
 destruct m as [ | m ]. smt_app (add_zero_r n). smt_app (add_comm m n); smt_app (add_suc_r (inject_into_subset_type N n True I) m).
Qed.

Theorem add_assoc (m: N) (n: N) (o: N): add m (add n o) = add (add m n) o.
Proof.
  destruct m as [ | m ]. smt_app trivial. smt_app (add_assoc m n o).
Qed.

Theorem mult_suc_r (n: N) (m: N): mult n (Suc m) = add n (mult n m).
Proof.
 destruct n as [ | n ]. smt_app trivial. smt_app (mult_suc_r n m); smt_app (add_assoc (inject_into_subset_type N m True I) (inject_into_subset_type N n True I) (mult n m)); smt_app (add_comm m n); smt_app (add_assoc (inject_into_subset_type N n True I) (inject_into_subset_type N m True I) (mult n m)).
Qed.

Theorem mult_zero_l (n: N): mult Z n = Z.
Proof.
destruct n as [ | n ]. smt_app trivial. smt_app (mult_zero_l n).
Qed.

Theorem mult_suc_l (m: N) (n: N): mult (Suc m) n = add n (mult m n).
Proof.
 destruct m as [ | m ]. smt_app trivial. smt_app trivial.
Qed.

Theorem mult_zero_r (n: N): mult n Z = Z.
Proof.
destruct n as [ | n ]. smt_app trivial. smt_app (mult_zero_r n).
Qed.

Definition one := Suc Z. 
Definition two := Suc one. 
Theorem mult_one_r (n: N): mult n one = n.
Proof.
destruct n as [ | n ]. smt_app trivial. smt_app (mult_one_r n).
Qed.
