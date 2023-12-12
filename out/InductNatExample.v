Add LoadPath "out" as Project. 
Load LHCoqTactics.
Open Scope Z_scope.
Open Scope Int_scope.
Inductive Natural: Set := ZeroN: Natural | Suc: (Natural -> Natural). 
Load IntNatExample. 
Definition one := Suc ZeroN. 
Definition two := Suc one. 
Definition toInt_unrefined (n: { n : Natural | True }): { v : BinNums.Z | v>=0 }. 
Proof.
  destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now unshelve refine (injectionCast BinNums.Z (fun v: BinNums.Z => v>=0) (0) _). }
    { smt_now unshelve refine (injectionCast BinNums.Z (fun v: BinNums.Z => v>=0) (1+(` (IHn))) _). }
Defined.

Definition toInt (n: { n : Natural | True }): { v : BinNums.Z | (` (toInt_unrefined n))=v } .
Proof.
  destruct n as [n np ]. 
  exact (exist (` (toInt_unrefined (injectionCast Natural (fun n: Natural => True) (n) _))) eq_refl). 
Defined.

Definition add_unrefined (m: { m : Natural | True }) (n: { n : Natural | True }): { VV : Natural | True }. 
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now unshelve refine (injectionCast Natural (fun VV: Natural => True) (n) _). }
    { smt_now unshelve refine (injectionCast Natural (fun VV: Natural => True) (Suc (` (IHm))) _). }
Defined.

Definition add (m: { m : Natural | True }) (n: { n : Natural | True }): { VV : Natural | (` (add_unrefined m n))=VV } .
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  exact (exist (` (add_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) eq_refl). 
Defined.

Definition mult_unrefined (m: { m : Natural | True }) (n: { n : Natural | True }): { VV : Natural | True }. 
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now unshelve refine (injectionCast Natural (fun VV: Natural => True) (ZeroN) _). }
    { smt_now unshelve refine (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined (injectionCast Natural (fun n: Natural => True) (n) _) IHm))=VV) (fun VV: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) (n) _) IHm)). }
Defined.

Definition mult (m: { m : Natural | True }) (n: { n : Natural | True }): { VV : Natural | (` (mult_unrefined m n))=VV } .
Proof.
  destruct m as [m mp ].  destruct n as [n np ]. 
  exact (exist (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) eq_refl). 
Defined.

Definition add_zero_l_spec: Prop. 
Proof. now unshelve refine (forall (n:{n: Natural| True}), (` (add (injectionCast Natural (fun m: Natural => True) (ZeroN) _) n))=(` (n))). .
Defined.
Theorem add_zero_l: add_zero_l_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. }
Qed.

Definition add_suc_l_spec: Prop. 
Proof. now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), Suc (` (add m n))=(` (add (injectionCast Natural (fun m: Natural => True) (Suc (` (m))) _) n))). .
Defined.
Theorem add_suc_l: add_suc_l_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { smt_app IHm. }
Qed.

Definition add_zero_r_spec: Prop. 
Proof. now unshelve refine (forall (n:{n: Natural| True}), (` (add n (injectionCast Natural (fun n: Natural => True) (ZeroN) _)))=(` (n))). .
Defined.
Theorem add_zero_r: add_zero_r_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. }
Qed.

Definition mult_one_l_spec: Prop. 
Proof. now unshelve refine (forall (n:{n: Natural| True}), (` (mult (injectionCast Natural (fun m: Natural => True) (one) _) n))=(` (n))). .
Defined.
Theorem mult_one_l: mult_one_l_spec.
Proof.
  intros n. destruct n as [n np ]. 
  
    { smt_app (add_zero_r (injectionCast Natural (fun n: Natural => True) (n) _)). }
Qed.

Definition add_suc_r_spec: Prop. 
Proof. now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), Suc (` (add m n))=(` (add m (injectionCast Natural (fun n: Natural => True) (Suc (` (n))) _)))). .
Defined.
Theorem add_suc_r: add_suc_r_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { smt_app IHm. }
Qed.

Definition add_comm_spec: Prop. 
Proof. now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (add m n))=(` (add n m))). .
Defined.
Theorem add_comm: add_comm_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_app (add_zero_r (injectionCast Natural (fun n: Natural => True) (n) _)). }
    { smt_app IHm. smt_app (add_suc_r (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _)). }
Qed.

Definition add_assoc_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), (` (add m (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined m n))=VV) (fun n: Natural => True) _ (add n o))))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined m n))=VV) (fun m: Natural => True) _ (add m n)) o))). .
Defined.
Theorem add_assoc: add_assoc_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { smt_app IHm. }
Qed.

Definition mult_suc_r_spec: Prop. 
Proof. now unshelve refine (forall (n:{n: Natural| True}) (m:{m: Natural| True}), (` (mult n (injectionCast Natural (fun n: Natural => True) (Suc (` (m))) _)))=(` (add n (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) _ (mult n m))))). .
Defined.
Theorem mult_suc_r: mult_suc_r_spec.
Proof.
  intros n. intros m. destruct n as [n np ].  destruct m as [m mp ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _)))). smt_app (add_comm (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)). smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _)))). }
Qed.

Definition add_dist_rmult_spec: Prop. 
Proof. now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), (` (mult (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined m n))=VV) (fun m: Natural => True) _ (add m n)) o))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun m: Natural => True) _ (mult m o)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) _ (mult n o))))). .
Defined.
Theorem add_dist_rmult: add_dist_rmult_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { smt_app IHm. smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) (o) _) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (o) _))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _)))). }
Qed.

Definition mult_assoc_spec: Prop. 
Proof. now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), (` (mult (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun m: Natural => True) _ (mult m n)) o))=(` (mult m (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) _ (mult n o))))). .
Defined.
Theorem mult_assoc: mult_assoc_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { 
  assertFresh ((` (mult (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (Suc m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (injectionCast Natural (fun n: Natural => True) (o) _)))=(` (mult (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun m: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) (n) _) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))))) (injectionCast Natural (fun n: Natural => True) (o) _)))) as lem using smt_trivial. . 
  assertFresh ((` (mult (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun m: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) (n) _) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))))) (injectionCast Natural (fun n: Natural => True) (o) _)))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun n: Natural => True) _ (mult (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (injectionCast Natural (fun n: Natural => True) (o) _)))))) as lem using (smt_app (add_dist_rmult (injectionCast Natural (fun m: Natural => True) (n) _) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (injectionCast Natural (fun o: Natural => True) (o) _)). ). 
  assertFresh ((` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun n: Natural => True) _ (mult (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (injectionCast Natural (fun n: Natural => True) (o) _)))))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _)))))))) as lem using (smt_app IHm. ). smt_now 
  assertFresh ((` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _)))))))=(` (mult (injectionCast Natural (fun m: Natural => True) (Suc m) _) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _)))))) as lem using smt_trivial. . }
Qed.

Definition mult_zero_l_spec: Prop. 
Proof. now unshelve refine (forall (n:{n: Natural| True}), (` (mult (injectionCast Natural (fun m: Natural => True) (ZeroN) _) n))=ZeroN). .
Defined.
Theorem mult_zero_l: mult_zero_l_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. }
Qed.

Definition mult_suc_l_spec: Prop. 
Proof. now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (mult (injectionCast Natural (fun m: Natural => True) (Suc (` (m))) _) n))=(` (add n (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) _ (mult m n))))). .
Defined.
Theorem mult_suc_l: mult_suc_l_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  
    { destruct m as [ | m ]. smt_now smt_trivial. smt_now smt_trivial. }
Qed.

Definition mult_zero_r_spec: Prop. 
Proof. now unshelve refine (forall (n:{n: Natural| True}), (` (mult n (injectionCast Natural (fun n: Natural => True) (ZeroN) _)))=ZeroN). .
Defined.
Theorem mult_zero_r: mult_zero_r_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. }
Qed.

Definition add_dist_lmult_spec: Prop. 
Proof. now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), (` (mult m (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined m n))=VV) (fun n: Natural => True) _ (add n o))))=(` (add (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun m: Natural => True) _ (mult m n)) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined m n))=VV) (fun n: Natural => True) _ (mult m o))))). .
Defined.
Theorem add_dist_lmult: add_dist_lmult_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction n as [| n IHn ]. 
    { smt_app (mult_zero_r (injectionCast Natural (fun n: Natural => True) (m) _)). }
    { smt_app (mult_suc_r (injectionCast Natural (fun n: Natural => True) (m) _) (subsumptionCast Natural (fun VV: Natural => (` (add_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun m: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _)))). smt_app IHn. smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) (m) _) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (subsumptionCast Natural (fun VV: Natural => (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))=VV) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (o) _)))). smt_app (mult_suc_r (injectionCast Natural (fun n: Natural => True) (m) _) (injectionCast Natural (fun m: Natural => True) (n) _)). }
Qed.

Definition mult_one_r_spec: Prop. 
Proof. now unshelve refine (forall (n:{n: Natural| True}), (` (mult n (injectionCast Natural (fun n: Natural => True) (one) _)))=(` (n))). .
Defined.
Theorem mult_one_r: mult_one_r_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. }
Qed.
