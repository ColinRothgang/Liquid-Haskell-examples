Add LoadPath "out" as Project. 
Load LHCoqTactics.
Open Scope Z_scope.
Open Scope Int_scope.
Inductive Natural: Set := ZeroN: Natural | Suc: (Natural -> Natural). 
Load IntNatExample. 
Definition one := Suc ZeroN. 
Definition two := Suc one. 
Definition add_unrefined (m: { m : Natural | True }) (n: { n : Natural | True }): { VV : Natural | True }. 
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. now 
 unshelve refine (injectionCast Natural (fun VV: Natural => True) (fun VV: Natural => I) (n)). now 
 unshelve refine (injectionCast Natural (fun VV: Natural => True) (fun VV: Natural => I) (Suc (` (IHm)))).
Defined.

Definition add (m: { m : Natural | True }) (n: { n : Natural | True }): { VV : Natural | (` (add_unrefined m n))=VV } .
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  exact (exist (` (add_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n)))) eq_refl). 
Defined.

Definition mult_unrefined (m: { m : Natural | True }) (n: { n : Natural | True }): { VV : Natural | True }. 
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. now 
 unshelve refine (injectionCast Natural (fun VV: Natural => True) (fun VV: Natural => I) (ZeroN)). now 
 unshelve refine (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n)) IHm))=VV) (fun VV: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) IHm)).
Defined.

Definition mult (m: { m : Natural | True }) (n: { n : Natural | True }): { VV : Natural | (` (mult_unrefined m n))=VV } .
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  exact (exist (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n)))) eq_refl). 
Defined.

Theorem add_zero_l (n: { n : Natural | True }): (` (add (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (ZeroN)) n))=(` (n)).
Proof.
  destruct n as [n np ]. 
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.

Theorem add_suc_l (m: { m : Natural | True }) (n: { n : Natural | True }): Suc (` (add m n))=(` (add (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (Suc (` (m)))) n)).
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. now smt_trivial. smt_app IHm.
Qed.

Theorem add_zero_r (n: { n : Natural | True }): (` (add n (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (ZeroN))))=(` (n)).
Proof.
  destruct n as [n np ]. 
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.

Theorem mult_one_l (n: { n : Natural | True }): (` (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (one)) n))=(` (n)).
Proof.
  destruct n as [n np ]. 
  smt_app (add_zero_r (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))).
Qed.

Theorem add_suc_r (m: { m : Natural | True }) (n: { n : Natural | True }): Suc (` (add m n))=(` (add m (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (Suc (` (n)))))).
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. now smt_trivial. smt_app IHm.
Qed.

Theorem add_comm (m: { m : Natural | True }) (n: { n : Natural | True }): (` (add m n))=(` (add n m)).
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. smt_app (add_zero_r (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))). smt_app IHm. smt_app (add_suc_r (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (m))).
Qed.

Theorem add_assoc (m: { m : Natural | True }) (n: { n : Natural | True }) (o: { o : Natural | True }): (` (add m (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined m n))=VV) (fun n: Natural => True) I (add n o))))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined m n))=VV) (fun m: Natural => True) I (add m n)) o)).
Proof.
  destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. now smt_trivial. smt_app IHm.
Qed.

Theorem mult_suc_r (n: { n : Natural | True }) (m: { m : Natural | True }): (` (mult n (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (Suc (` (m))))))=(` (add n (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) I (mult n m)))).
Proof.
  destruct n as [n np ].  destruct m as [m mp ]. 
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn. smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (m))))). smt_app (add_comm (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))). smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (m)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (m))))).
Qed.

Theorem add_dist_rmult (m: { m : Natural | True }) (n: { n : Natural | True }) (o: { o : Natural | True }): (` (mult (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined m n))=VV) (fun m: Natural => True) I (add m n)) o))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun m: Natural => True) I (mult m o)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) I (mult n o)))).
Proof.
  destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. now smt_trivial. smt_app IHm. smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (o)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o)))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o))))).
Qed.

Theorem mult_assoc (m: { m : Natural | True }) (n: { n : Natural | True }) (o: { o : Natural | True }): (` (mult (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun m: Natural => True) I (mult m n)) o))=(` (mult m (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) I (mult n o)))).
Proof.
  destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. now smt_trivial. 
  assertFresh ((` (mult (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (Suc m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n)))) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o))))=(` (mult (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun m: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n)))))) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o))))) as lem using smt_trivial. 
  assertFresh ((` (mult (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun m: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n)))))) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o))))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o)))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun n: Natural => True) _ (mult (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n)))) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o))))))) as lem using (smt_app (add_dist_rmult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n)))) (injectionCast Natural (fun o: Natural => True) (fun o: Natural => I) (o)))). 
  assertFresh ((` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o)))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun n: Natural => True) _ (mult (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n)))) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o))))))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o)))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o))))))))) as lem using (smt_app IHm). now 
  assertFresh ((` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o)))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o))))))))=(` (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (Suc m)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o))))))) as lem using smt_trivial.
Qed.

Theorem mult_zero_l (n: { n : Natural | True }): (` (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (ZeroN)) n))=ZeroN.
Proof.
  destruct n as [n np ]. 
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.

Theorem mult_suc_l (m: { m : Natural | True }) (n: { n : Natural | True }): (` (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (Suc (` (m)))) n))=(` (add n (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) I (mult m n)))).
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  destruct m as [ | m ]. now smt_trivial. now smt_trivial.
Qed.

Theorem mult_zero_r (n: { n : Natural | True }): (` (mult n (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (ZeroN))))=ZeroN.
Proof.
  destruct n as [n np ]. 
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.

Theorem add_dist_lmult (m: { m : Natural | True }) (n: { n : Natural | True }) (o: { o : Natural | True }): (` (mult m (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined m n))=VV) (fun n: Natural => True) I (add n o))))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun m: Natural => True) I (mult m n)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) I (mult m o)))).
Proof.
  destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction n as [| n IHn ]. smt_app (mult_zero_r (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (m))). smt_app (mult_suc_r (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (m)) (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun m: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o))))). smt_app IHn. smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n)))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (n))))=VV) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (m)) (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (o))))). smt_app (mult_suc_r (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (m)) (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (n))).
Qed.

Theorem mult_one_r (n: { n : Natural | True }): (` (mult n (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (one))))=(` (n)).
Proof.
  destruct n as [n np ]. 
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.
