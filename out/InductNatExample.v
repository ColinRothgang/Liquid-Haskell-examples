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
 unshelve refine (injectionCast Natural (fun VV: Natural => True) _ (n)). now 
 unshelve refine (injectionCast Natural (fun VV: Natural => True) _ (Suc (` (IHm)))).
Defined.

Definition add (m: { m : Natural | True }) (n: { n : Natural | True }): { VV : Natural | (` (add_unrefined m n))=VV } .
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  exact (exist (` (add_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n)))) eq_refl). 
Defined.

Definition mult_unrefined (m: { m : Natural | True }) (n: { n : Natural | True }): { VV : Natural | True }. 
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. now 
 unshelve refine (injectionCast Natural (fun VV: Natural => True) _ (ZeroN)). now 
 unshelve refine (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined (injectionCast Natural (fun n: Natural => True) _ (n)) IHm))=VV) (fun VV: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) _ (n)) IHm)).
Defined.

Definition mult (m: { m : Natural | True }) (n: { n : Natural | True }): { VV : Natural | (` (mult_unrefined m n))=VV } .
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  exact (exist (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n)))) eq_refl). 
Defined.

Definition add_zero_l_spec: Prop. 
Proof. 
 unshelve refine (forall (n:{n: Natural| True}), (` (add (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (ZeroN)) n))=(` (n))).
Defined.
Theorem add_zero_l: add_zero_l_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.

Definition add_suc_l_spec: Prop. 
Proof. 
 unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), Suc (` (add m n))=(` (add (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (Suc (` (m)))) n))).
Defined.
Theorem add_suc_l: add_suc_l_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. now smt_trivial. smt_app IHm.
Qed.

Definition add_zero_r_spec: Prop. 
Proof. 
 unshelve refine (forall (n:{n: Natural| True}), (` (add n (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (ZeroN))))=(` (n))).
Defined.
Theorem add_zero_r: add_zero_r_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.

Definition mult_one_l_spec: Prop. 
Proof. 
 unshelve refine (forall (n:{n: Natural| True}), (` (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (one)) n))=(` (n))).
Defined.
Theorem mult_one_l: mult_one_l_spec.
Proof.
  intros n. destruct n as [n np ]. 
  smt_app (add_zero_r (injectionCast Natural (fun n: Natural => True) _ (n))).
Qed.

Definition add_suc_r_spec: Prop. 
Proof. 
 unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), Suc (` (add m n))=(` (add m (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (Suc (` (n))))))).
Defined.
Theorem add_suc_r: add_suc_r_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. now smt_trivial. smt_app IHm.
Qed.

Definition add_comm_spec: Prop. 
Proof. 
 unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (add m n))=(` (add n m))).
Defined.
Theorem add_comm: add_comm_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. smt_app (add_zero_r (injectionCast Natural (fun n: Natural => True) _ (n))). smt_app IHm. smt_app (add_suc_r (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (m))).
Qed.

Definition add_assoc_spec: Prop. 
Proof. 
 unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), (` (add m (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined m n))=VV) (fun n: Natural => True) I (add n o))))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined m n))=VV) (fun m: Natural => True) I (add m n)) o))).
Defined.
Theorem add_assoc: add_assoc_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. now smt_trivial. smt_app IHm.
Qed.

Definition mult_suc_r_spec: Prop. 
Proof. 
 unshelve refine (forall (n:{n: Natural| True}) (m:{m: Natural| True}), (` (mult n (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (Suc (` (m))))))=(` (add n (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) I (mult n m))))).
Defined.
Theorem mult_suc_r: mult_suc_r_spec.
Proof.
  intros n. intros m. destruct n as [n np ].  destruct m as [m mp ]. 
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn. smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (m))))). smt_app (add_comm (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))). smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (m)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (m))))).
Qed.

Definition add_dist_rmult_spec: Prop. 
Proof. 
 unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), (` (mult (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined m n))=VV) (fun m: Natural => True) I (add m n)) o))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun m: Natural => True) I (mult m o)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) I (mult n o))))).
Defined.
Theorem add_dist_rmult: add_dist_rmult_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. now smt_trivial. smt_app IHm. smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) _ (o)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (o)))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (o))))).
Qed.

Definition mult_assoc_spec: Prop. 
Proof. 
 unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), (` (mult (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun m: Natural => True) I (mult m n)) o))=(` (mult m (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) I (mult n o))))).
Defined.
Theorem mult_assoc: mult_assoc_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. now smt_trivial. 
  assertFresh ((` (mult (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (Suc m)) (injectionCast Natural (fun n: Natural => True) _ (n)))) (injectionCast Natural (fun n: Natural => True) _ (o))))=(` (mult (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun m: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) _ (n)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n)))))) (injectionCast Natural (fun n: Natural => True) _ (o))))) as lem using smt_trivial. 
  assertFresh ((` (mult (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun m: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) _ (n)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n)))))) (injectionCast Natural (fun n: Natural => True) _ (o))))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (o)))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun n: Natural => True) _ (mult (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n)))) (injectionCast Natural (fun n: Natural => True) _ (o))))))) as lem using (smt_app (add_dist_rmult (injectionCast Natural (fun m: Natural => True) _ (n)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n)))) (injectionCast Natural (fun o: Natural => True) _ (o)))). 
  assertFresh ((` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (o)))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun n: Natural => True) _ (mult (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n)))) (injectionCast Natural (fun n: Natural => True) _ (o))))))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (o)))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (m)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (o))))))))) as lem using (smt_app IHm). now 
  assertFresh ((` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (o)))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (m)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (o))))))))=(` (mult (injectionCast Natural (fun m: Natural => True) _ (Suc m)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (o))))))) as lem using smt_trivial.
Qed.

Definition mult_zero_l_spec: Prop. 
Proof. 
 unshelve refine (forall (n:{n: Natural| True}), (` (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (ZeroN)) n))=ZeroN).
Defined.
Theorem mult_zero_l: mult_zero_l_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.

Definition mult_suc_l_spec: Prop. 
Proof. 
 unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (mult (injectionCast Natural (fun m: Natural => True) (fun m: Natural => I) (Suc (` (m)))) n))=(` (add n (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) I (mult m n))))).
Defined.
Theorem mult_suc_l: mult_suc_l_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  destruct m as [ | m ]. now smt_trivial. now smt_trivial.
Qed.

Definition mult_zero_r_spec: Prop. 
Proof. 
 unshelve refine (forall (n:{n: Natural| True}), (` (mult n (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (ZeroN))))=ZeroN).
Defined.
Theorem mult_zero_r: mult_zero_r_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.

Definition add_dist_lmult_spec: Prop. 
Proof. 
 unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), (` (mult m (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined m n))=VV) (fun n: Natural => True) I (add n o))))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun m: Natural => True) I (mult m n)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) I (mult m o))))).
Defined.
Theorem add_dist_lmult: add_dist_lmult_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction n as [| n IHn ]. smt_app (mult_zero_r (injectionCast Natural (fun n: Natural => True) _ (m))). smt_app (mult_suc_r (injectionCast Natural (fun n: Natural => True) _ (m)) (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun m: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) _ (n)) (injectionCast Natural (fun n: Natural => True) _ (o))))). smt_app IHn. smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) _ (m)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n)))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (n))))=VV) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) _ (m)) (injectionCast Natural (fun n: Natural => True) _ (o))))). smt_app (mult_suc_r (injectionCast Natural (fun n: Natural => True) _ (m)) (injectionCast Natural (fun m: Natural => True) _ (n))).
Qed.

Definition mult_one_r_spec: Prop. 
Proof. 
 unshelve refine (forall (n:{n: Natural| True}), (` (mult n (injectionCast Natural (fun n: Natural => True) (fun n: Natural => I) (one))))=(` (n))).
Defined.
Theorem mult_one_r: mult_one_r_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. now smt_trivial. smt_app IHn.
Qed.
