Load LHCoqTactics.
Open Scope Z_scope.
Open Scope Int_scope.
Inductive N: Set := Z: N | Suc: ({x1: N| True} -> N). 
Load IntNatExample. 
Definition one := Suc (# (Z)). 
Definition two := Suc (# (one)). 
Definition add_unrefined (m: { m : N | True }) (n: { n : N | True }): { VV : N | True }. 
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| IHm ]. now exact (# (n)). now exact (# (Suc IHm)).
Defined.

Definition add (m: { m : N | True }) (n: { n : N | True }): { VV : N | (` (add_unrefined m n))=VV } .
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  exact (exist (` (add_unrefined (# (m)) (# (n)))) eq_refl). 
Defined.

Definition mult_unrefined (m: { m : N | True }) (n: { n : N | True }): { VV : N | True }. 
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| IHm ]. now exact (# (Z)). now exact (# (` (add (# (n)) IHm))).
Defined.

Definition mult (m: { m : N | True }) (n: { n : N | True }): { VV : N | (` (mult_unrefined m n))=VV } .
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  exact (exist (` (mult_unrefined (# (m)) (# (n)))) eq_refl). 
Defined.

Theorem add_zero_l (n: { n : N | True }): (` (add (# (Z)) n))=(` (n)).
Proof.
  destruct n as [n np ]. 
  induction n as [| IHn ]. now smt_trivial. smt_app IHn.
Qed.

Theorem add_suc_l (m: { m : N | True }) (n: { n : N | True }): Suc (# (` (add m n)))=(` (add (# (Suc m)) n)).
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| IHm ]. now smt_trivial. smt_app IHm.
Qed.

Theorem add_zero_r (n: { n : N | True }): (` (add n (# (Z))))=(` (n)).
Proof.
  destruct n as [n np ]. 
  induction n as [| IHn ]. now smt_trivial. smt_app IHn.
Qed.

Theorem mult_one_l (n: { n : N | True }): (` (mult (# (one)) n))=(` (n)).
Proof.
  destruct n as [n np ]. 
  smt_app (add_zero_r (# (n))).
Qed.

Theorem add_suc_r (m: { m : N | True }) (n: { n : N | True }): Suc (# (` (add m n)))=(` (add m (# (Suc n)))).
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| IHm ]. now smt_trivial. smt_app IHm.
Qed.

Theorem add_comm (m: { m : N | True }) (n: { n : N | True }): (` (add m n))=(` (add n m)).
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| IHm ]. smt_app (add_zero_r (# (n))). smt_app IHm. smt_app (add_suc_r (# (n)) (# (m))).
Qed.

Theorem add_assoc (m: { m : N | True }) (n: { n : N | True }) (o: { o : N | True }): (` (add m (# (` (add n o)))))=(` (add (# (` (add m n))) o)).
Proof.
  destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| IHm ]. now smt_trivial. smt_app IHm.
Qed.

Theorem mult_suc_r (n: { n : N | True }) (m: { m : N | True }): (` (mult n (# (Suc m))))=(` (add n (# (` (mult n m))))).
Proof.
  destruct n as [n np ].  destruct m as [m mp ]. 
  induction n as [| IHn ]. now smt_trivial. smt_app IHn. smt_app (add_assoc (# (m)) (# (n)) (# (` (mult (# (n)) (# (m)))))). smt_app (add_comm (# (m)) (# (n))). smt_app (add_assoc (# (n)) (# (m)) (# (` (mult (# (n)) (# (m)))))).
Qed.

Theorem add_dist_rmult (m: { m : N | True }) (n: { n : N | True }) (o: { o : N | True }): (` (mult (# (` (add m n))) o))=(` (add (# (` (mult m o))) (# (` (mult n o))))).
Proof.
  destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| IHm ]. now smt_trivial. smt_app IHm. smt_app (add_assoc (# (o)) (# (` (mult (# (m)) (# (o))))) (# (` (mult (# (n)) (# (o)))))).
Qed.

Theorem mult_assoc (m: { m : N | True }) (n: { n : N | True }) (o: { o : N | True }): (` (mult (# (` (mult m n))) o))=(` (mult m (# (` (mult n o))))).
Proof.
  destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| IHm ]. now smt_trivial. 
  assertFresh ((` (mult (# (` (mult (# (Suc (# (m)))) (# (n))))) (# (o))))=(` (mult (# (` (add (# (n)) (# (` (mult (# (m)) (# (n)))))))) (# (o))))) as lem using smt_trivial. 
  assertFresh ((` (mult (# (` (add (# (n)) (# (` (mult (# (m)) (# (n)))))))) (# (o))))=(` (add (# (` (mult (# (n)) (# (o))))) (# (` (mult (# (` (mult (# (m)) (# (n))))) (# (o)))))))) as lem using (smt_app (add_dist_rmult (# (n)) (# (` (mult (# (m)) (# (n))))) (# (o)))). 
  assertFresh ((` (add (# (` (mult (# (n)) (# (o))))) (# (` (mult (# (` (mult (# (m)) (# (n))))) (# (o)))))))=(` (add (# (` (mult (# (n)) (# (o))))) (# (` (mult (# (m)) (# (` (mult (# (n)) (# (o))))))))))) as lem using (smt_app IHm). now 
  assertFresh ((` (add (# (` (mult (# (n)) (# (o))))) (# (` (mult (# (m)) (# (` (mult (# (n)) (# (o))))))))))=(` (mult (# (Suc (# (m)))) (# (` (mult (# (n)) (# (o)))))))) as lem using smt_trivial.
Qed.

Theorem mult_zero_l (n: { n : N | True }): (` (mult (# (Z)) n))=Z.
Proof.
  destruct n as [n np ]. 
  induction n as [| IHn ]. now smt_trivial. smt_app IHn.
Qed.

Theorem mult_suc_l (m: { m : N | True }) (n: { n : N | True }): (` (mult (# (Suc m)) n))=(` (add n (# (` (mult m n))))).
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  destruct m as [ | m ]. now smt_trivial. now smt_trivial.
Qed.

Theorem mult_zero_r (n: { n : N | True }): (` (mult n (# (Z))))=Z.
Proof.
  destruct n as [n np ]. 
  induction n as [| IHn ]. now smt_trivial. smt_app IHn.
Qed.

Theorem add_dist_lmult (m: { m : N | True }) (n: { n : N | True }) (o: { o : N | True }): (` (mult m (# (` (add n o)))))=(` (add (# (` (mult m n))) (# (` (mult m o))))).
Proof.
  destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction n as [| IHn ]. smt_app (mult_zero_r (# (m))). smt_app (mult_suc_r (# (m)) (# (` (add (# (n)) (# (o)))))). smt_app IHn. smt_app (add_assoc (# (m)) (# (` (mult (# (m)) (# (n))))) (# (` (mult (# (m)) (# (o)))))). smt_app (mult_suc_r (# (m)) (# (n))).
Qed.

Theorem mult_one_r (n: { n : N | True }): (` (mult n (# (one))))=(` (n)).
Proof.
  destruct n as [n np ]. 
  induction n as [| IHn ]. now smt_trivial. smt_app IHn.
Qed.
