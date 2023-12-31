Add LoadPath "out" as Project. 
Load LHCoqTactics.
Open Scope Z_scope.
Open Scope Int_scope.
Inductive Natural: Set := ZeroN: Natural | Suc: (Natural -> Natural). 
Load IntNatExample. 
Definition one := Suc ZeroN. 
Definition two := Suc one. 
Definition toInt_unrefined_spec: Type. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| True}), { VV : BinNums.Z | (VV >= (0)) }). 
Defined.
Definition toInt_unrefined: toInt_unrefined_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now unshelve refine (injectionCast BinNums.Z (fun VV: BinNums.Z => (VV >= (0))) (0) _). }
    { smt_now unshelve refine (injectionCast BinNums.Z (fun VV: BinNums.Z => (VV >= (0))) ((1) + (` (IHn))) _). }
Defined.

Definition toInt_spec: Type. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| True}), { VV : BinNums.Z | ((` (toInt_unrefined n)) = (VV)) }). 
Defined.
Definition toInt: toInt_spec.
Proof.
  intros n. destruct n as [n np ]. 
  smt_now unshelve refine (injectionCast BinNums.Z (fun VV: BinNums.Z => ((` (toInt_unrefined (injectionCast Natural (fun n: Natural => True) (n) np))) = (VV))) (` (toInt_unrefined (injectionCast Natural (fun n: Natural => True) (n) np))) eq_refl). 
Defined.

Definition add_unrefined_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { VV : Natural | True }). 
Defined.
Definition add_unrefined: add_unrefined_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now unshelve refine (injectionCast Natural (fun VV: Natural => True) (n) _). }
    { smt_now unshelve refine (injectionCast Natural (fun VV: Natural => True) (Suc (` (IHm))) _). }
Defined.

Definition add_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { VV : Natural | ((` (add_unrefined m n)) = (VV)) }). 
Defined.
Definition add: add_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  smt_now unshelve refine (injectionCast Natural (fun VV: Natural => ((` (add_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) = (VV))) (` (add_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) eq_refl). 
Defined.

Definition mult_unrefined_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { VV : Natural | True }). 
Defined.
Definition mult_unrefined: mult_unrefined_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now unshelve refine (injectionCast Natural (fun VV: Natural => True) (ZeroN) _). }
    { smt_now unshelve refine (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined (injectionCast Natural (fun n: Natural => True) (n) _) IHm)) = (VV))) (fun VV: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) (n) _) IHm)). }
Defined.

Definition mult_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { VV : Natural | ((` (mult_unrefined m n)) = (VV)) }). 
Defined.
Definition mult: mult_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  smt_now unshelve refine (injectionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) = (VV))) (` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) eq_refl). 
Defined.

Definition eqN_unrefined_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { r : Prop | (r = ((` (m)) = (` (n)))) }). 
Defined.
Definition eqN_unrefined: eqN_unrefined_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | lq_anf7205759403792798519 ]. smt_now unshelve refine (injectionCast Prop (fun r: Prop => (r = ((` (m)) = (` (n))))) (True) _). smt_now unshelve refine (injectionCast Prop (fun r: Prop => (r = ((` (m)) = (` (n))))) (False) _). }
    { destruct n as [ | n ]. smt_now unshelve refine (injectionCast Prop (fun r: Prop => (r = ((` (m)) = (` (n))))) (False) _). smt_now unshelve refine (IHm). }
Defined.

Definition eqN_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { r : Prop | ((` (eqN_unrefined m n)) = (r)) }). 
Defined.
Definition eqN: eqN_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  smt_now unshelve refine (injectionCast Prop (fun r: Prop => ((` (eqN_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) = (r))) (` (eqN_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) eq_refl). 
Defined.

Definition geqN_unrefined_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { p : Prop | (p = ((` (toInt m)) >= (` (toInt n)))) }). 
Defined.
Definition geqN_unrefined: geqN_unrefined_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now unshelve refine (injectionCast Prop (fun p: Prop => (p = ((` (toInt m)) >= (` (toInt (injectionCast Natural (fun n: Natural => True) (n) _)))))) (True) _). }
    { destruct m as [ | m ]. destruct n as [ | ds_d1ed ]. destruct () as [ ]. smt_now unshelve refine (injectionCast Prop (fun p: Prop => (p = ((` (toInt m)) >= (` (toInt (injectionCast Natural (fun n: Natural => True) (n) _)))))) (False) _). destruct n as [ | n ]. destruct () as [ ]. smt_now unshelve refine (IHm). }
Defined.

Definition geqN_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { p : Prop | ((` (geqN_unrefined m n)) = (p)) }). 
Defined.
Definition geqN: geqN_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  smt_now unshelve refine (injectionCast Prop (fun p: Prop => ((` (geqN_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) = (p))) (` (geqN_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) eq_refl). 
Defined.

Definition leqN_unrefined_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { p : Prop | (p = ((` (toInt m)) <= (` (toInt n)))) }). 
Defined.
Definition leqN_unrefined: leqN_unrefined_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  
    { smt_now unshelve refine (subsumptionCast Prop (fun p: Prop => ((` (geqN_unrefined (injectionCast Natural (fun n: Natural => True) (n) _) (injectionCast Natural (fun m: Natural => True) (m) _))) = (p))) (fun p: Prop => (p = ((` (toInt m)) <= (` (toInt (injectionCast Natural (fun n: Natural => True) (n) _)))))) _ (geqN (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _))). }
Defined.

Definition leqN_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { p : Prop | ((` (leqN_unrefined m n)) = (p)) }). 
Defined.
Definition leqN: leqN_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  smt_now unshelve refine (injectionCast Prop (fun p: Prop => ((` (leqN_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) = (p))) (` (leqN_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) eq_refl). 
Defined.

Definition geN_unrefined_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { p : Prop | p->(` (geqN m n)) /\ (p = ((` (toInt m)) > (` (toInt n)))) }). 
Defined.
Definition geN_unrefined: geN_unrefined_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| ds_d1e7 IHds_d1e7 ]. 
    { smt_now unshelve refine (injectionCast Prop (fun p: Prop => p->(` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) /\ (p = ((` (toInt m)) > (` (toInt (injectionCast Natural (fun n: Natural => True) (n) _)))))) (False) _). }
    { destruct n as [ | n ]. smt_now unshelve refine (injectionCast Prop (fun p: Prop => p->(` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) /\ (p = ((` (toInt m)) > (` (toInt (injectionCast Natural (fun n: Natural => True) (n) _)))))) (True) _). smt_now unshelve refine (IHds_d1e7). }
Defined.

Definition geN_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { p : Prop | ((` (geN_unrefined m n)) = (p)) }). 
Defined.
Definition geN: geN_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  smt_now unshelve refine (injectionCast Prop (fun p: Prop => ((` (geN_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) = (p))) (` (geN_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) eq_refl). 
Defined.

Definition leN_unrefined_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { p : Prop | (p = ((` (toInt m)) < (` (toInt n)))) }). 
Defined.
Definition leN_unrefined: leN_unrefined_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  
    { smt_now unshelve refine (subsumptionCast Prop (fun p: Prop => ((` (geN_unrefined (injectionCast Natural (fun n: Natural => True) (n) _) (injectionCast Natural (fun m: Natural => True) (m) _))) = (p))) (fun p: Prop => (p = ((` (toInt m)) < (` (toInt (injectionCast Natural (fun n: Natural => True) (n) _)))))) _ (geN (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _))). }
Defined.

Definition leN_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), { p : Prop | ((` (leN_unrefined m n)) = (p)) }). 
Defined.
Definition leN: leN_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  smt_now unshelve refine (injectionCast Prop (fun p: Prop => ((` (leN_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) = (p))) (` (leN_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => True) (n) np))) eq_refl). 
Defined.

Definition subt_unrefined_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))}), { o : Natural | (((` (n)) <> (ZeroN)) = ((` (toInt (injectionCast Natural (fun n: Natural => True) (o) I))) < (` (toInt m)))) }). 
Defined.
Definition subt_unrefined: subt_unrefined_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | lq_anf7205759403792798680 ]. smt_now unshelve refine (injectionCast Natural (fun o: Natural => (((` (n)) <> (ZeroN)) = ((` (toInt (injectionCast Natural (fun n: Natural => True) (o) I))) < (` (toInt m))))) (ZeroN) _). destruct () as [ ]. }
    { destruct n as [ | n ]. smt_now unshelve refine (injectionCast Natural (fun o: Natural => (((` (n)) <> (ZeroN)) = ((` (toInt (injectionCast Natural (fun n: Natural => True) (o) I))) < (` (toInt m))))) (Suc m) _). smt_now unshelve refine (IHm). }
Defined.

Definition subt_spec: Type. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))}), { o : Natural | ((` (subt_unrefined m n)) = (o)) }). 
Defined.
Definition subt: subt_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  smt_now unshelve refine (injectionCast Natural (fun o: Natural => ((` (subt_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))) (n) np))) = (o))) (` (subt_unrefined (injectionCast Natural (fun m: Natural => True) (m) mp) (injectionCast Natural (fun n: Natural => (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))) (n) np))) eq_refl). 
Defined.

Definition add_zero_l_spec: Prop. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| True}), ((` (add (injectionCast Natural (fun m: Natural => True) (ZeroN) I) n)) = (` (n)))). 
Defined.
Theorem add_zero_l: add_zero_l_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. }
Qed.

Definition add_suc_l_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (Suc (` (add m n)) = (` (add (injectionCast Natural (fun m: Natural => True) (Suc (` (m))) I) n)))). 
Defined.
Theorem add_suc_l: add_suc_l_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { smt_app IHm. }
Qed.

Definition add_mono_r_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (geqN (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined m n)) = (VV))) (fun m: Natural => True) I (add m n)) m)) /\ (` (geN n (injectionCast Natural (fun n: Natural => True) (ZeroN) I)))->(` (geN (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined m n)) = (VV))) (fun m: Natural => True) I (add m n)) m))). 
Defined.
Theorem add_mono_r: add_mono_r_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { smt_app (add_suc_l (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)). smt_app IHm. }
Qed.

Definition add_zero_r_spec: Prop. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| True}), ((` (add n (injectionCast Natural (fun n: Natural => True) (ZeroN) I))) = (` (n)))). 
Defined.
Theorem add_zero_r: add_zero_r_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. }
Qed.

Definition mult_one_l_spec: Prop. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| True}), ((` (mult (injectionCast Natural (fun m: Natural => True) (one) I) n)) = (` (n)))). 
Defined.
Theorem mult_one_l: mult_one_l_spec.
Proof.
  intros n. destruct n as [n np ]. 
  
    { smt_app (add_zero_r (injectionCast Natural (fun n: Natural => True) (n) _)). }
Qed.

Definition add_suc_r_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (Suc (` (add m n)) = (` (add m (injectionCast Natural (fun n: Natural => True) (Suc (` (n))) I))))). 
Defined.
Theorem add_suc_r: add_suc_r_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { smt_app IHm. }
Qed.

Definition add_comm_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), ((` (add m n)) = (` (add n m)))). 
Defined.
Theorem add_comm: add_comm_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_app (add_zero_r (injectionCast Natural (fun n: Natural => True) (n) _)). }
    { smt_app IHm. smt_app (add_suc_r (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _)). }
Qed.

Definition add_mono_l_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (geqN (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined m n)) = (VV))) (fun m: Natural => True) I (add m n)) n)) /\ (` (geN m (injectionCast Natural (fun n: Natural => True) (ZeroN) I)))->(` (geN (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined m n)) = (VV))) (fun m: Natural => True) I (add m n)) n))). 
Defined.
Theorem add_mono_l: add_mono_l_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  
    { smt_app (add_mono_r (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _)). smt_app (add_comm (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _)). }
Qed.

Definition add_subt_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), ((` (subt (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined m n)) = (VV))) (fun m: Natural => True) I (add m n)) (subsumptionCast Natural (fun n: Natural => True) (fun n: Natural => (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))) _ (n)))) = (` (m)))). 
Defined.
Theorem add_subt: add_subt_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | lq_anf7205759403792798452 ]. smt_now smt_trivial. destruct n as [ | n ]. destruct () as [ ]. smt_app (add_suc_r (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)). smt_app (add_subt (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)). }
    { destruct n as [ | lq_anf7205759403792798460 ]. smt_app (add_zero_r (injectionCast Natural (fun n: Natural => True) (m) _)). destruct n as [ | n ]. destruct () as [ ]. smt_app (add_suc_r (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)). smt_app IHm. }
Qed.

Definition add_assoc_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), ((` (add m (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined m n)) = (VV))) (fun n: Natural => True) I (add n o)))) = (` (add (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined m n)) = (VV))) (fun m: Natural => True) I (add m n)) o)))). 
Defined.
Theorem add_assoc: add_assoc_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { smt_app IHm. }
Qed.

Definition mult_suc_r_spec: Prop. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| True}) (m:{m: Natural| True}), ((` (mult n (injectionCast Natural (fun n: Natural => True) (Suc (` (m))) I))) = (` (add n (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined m n)) = (VV))) (fun n: Natural => True) I (mult n m)))))). 
Defined.
Theorem mult_suc_r: mult_suc_r_spec.
Proof.
  intros n. intros m. destruct n as [n np ].  destruct m as [m mp ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _)))). smt_app (add_comm (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)). smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _)))). }
Qed.

Definition add_dist_rmult_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), ((` (mult (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined m n)) = (VV))) (fun m: Natural => True) I (add m n)) o)) = (` (add (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined m n)) = (VV))) (fun m: Natural => True) I (mult m o)) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined m n)) = (VV))) (fun n: Natural => True) I (mult n o)))))). 
Defined.
Theorem add_dist_rmult: add_dist_rmult_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { smt_app IHm. smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) (o) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (o) _))) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _)))). }
Qed.

Definition mult_assoc_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), ((` (mult (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined m n)) = (VV))) (fun m: Natural => True) I (mult m n)) o)) = (` (mult m (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined m n)) = (VV))) (fun n: Natural => True) I (mult n o)))))). 
Defined.
Theorem mult_assoc: mult_assoc_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { 
  assertFresh ((` (mult (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (Suc m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (injectionCast Natural (fun n: Natural => True) (o) _))) = (` (mult (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) (n) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))))) (injectionCast Natural (fun n: Natural => True) (o) _)))) as lem using smt_trivial. . 
  assertFresh ((` (mult (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) (n) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))))) (injectionCast Natural (fun n: Natural => True) (o) _))) = (` (add (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _))) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (injectionCast Natural (fun n: Natural => True) (o) _)))))) as lem using (smt_app (add_dist_rmult (injectionCast Natural (fun m: Natural => True) (n) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (injectionCast Natural (fun o: Natural => True) (o) _)). ). 
  assertFresh ((` (add (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _))) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (injectionCast Natural (fun n: Natural => True) (o) _))))) = (` (add (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _))) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _)))))))) as lem using (smt_app IHm. ). smt_now 
  assertFresh ((` (add (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _))) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _))))))) = (` (mult (injectionCast Natural (fun m: Natural => True) (Suc m) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _)))))) as lem using smt_trivial. . }
Qed.

Definition mult_zero_l_spec: Prop. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| True}), ((` (mult (injectionCast Natural (fun m: Natural => True) (ZeroN) I) n)) = (ZeroN))). 
Defined.
Theorem mult_zero_l: mult_zero_l_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. }
Qed.

Definition mult_suc_l_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), ((` (mult (injectionCast Natural (fun m: Natural => True) (Suc (` (m))) I) n)) = (` (add n (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined m n)) = (VV))) (fun n: Natural => True) I (mult m n)))))). 
Defined.
Theorem mult_suc_l: mult_suc_l_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  
    { destruct m as [ | m ]. smt_now smt_trivial. smt_now smt_trivial. }
Qed.

Definition mult_zero_r_spec: Prop. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| True}), ((` (mult n (injectionCast Natural (fun n: Natural => True) (ZeroN) I))) = (ZeroN))). 
Defined.
Theorem mult_zero_r: mult_zero_r_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. }
Qed.

Definition add_dist_lmult_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), ((` (mult m (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined m n)) = (VV))) (fun n: Natural => True) I (add n o)))) = (` (add (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined m n)) = (VV))) (fun m: Natural => True) I (mult m n)) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined m n)) = (VV))) (fun n: Natural => True) I (mult m o)))))). 
Defined.
Theorem add_dist_lmult: add_dist_lmult_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction n as [| n IHn ]. 
    { smt_app (mult_zero_r (injectionCast Natural (fun n: Natural => True) (m) _)). }
    { smt_app (mult_suc_r (injectionCast Natural (fun n: Natural => True) (m) _) (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (add (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (o) _)))). smt_app IHn. smt_app (add_assoc (injectionCast Natural (fun m: Natural => True) (m) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun o: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (o) _)))). smt_app (mult_suc_r (injectionCast Natural (fun n: Natural => True) (m) _) (injectionCast Natural (fun m: Natural => True) (n) _)). }
Qed.

Definition mult_one_r_spec: Prop. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| True}), ((` (mult n (injectionCast Natural (fun n: Natural => True) (one) I))) = (` (n)))). 
Defined.
Theorem mult_one_r: mult_one_r_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. }
Qed.

Definition ge_measure_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), ((` (geN m n)) = ((` (toInt m)) > (` (toInt n))))). 
Defined.
Theorem ge_measure: ge_measure_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| ds_d1e1 IHds_d1e1 ]. 
    { smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHds_d1e1. }
Qed.

Definition ge_geq_suc_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), ((` (geN m n)) = (` (geqN m (injectionCast Natural (fun n: Natural => True) (Suc (` (n))) I))))). 
Defined.
Theorem ge_geq_suc: ge_geq_suc_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition ge_zero_spec: Prop. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| True}), (` (geqN n (injectionCast Natural (fun n: Natural => True) (ZeroN) I))) /\ ((` (n)) <> (ZeroN))->(` (geN n (injectionCast Natural (fun n: Natural => True) (ZeroN) I)))). 
Defined.
Theorem ge_zero: ge_zero_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. smt_app (ge_geq_suc (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (ZeroN) _)). }
Qed.

Definition eq_suc_ge_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (eqN m n))->(` (geN (injectionCast Natural (fun m: Natural => True) (Suc (` (m))) I) n))). 
Defined.
Theorem eq_suc_ge: eq_suc_ge_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | n ]. smt_now smt_trivial. smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition eq_equal_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), ((` (eqN m n)) = ((` (m)) = (` (n))))). 
Defined.
Theorem eq_equal: eq_equal_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | lq_anf7205759403792798546 ]. smt_now smt_trivial. smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition eq_sym_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), ((` (eqN m n)) = (` (eqN n m)))). 
Defined.
Theorem eq_sym: eq_sym_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  
    { smt_app (eq_equal (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)). smt_app (eq_equal (injectionCast Natural (fun m: Natural => True) (n) _) (injectionCast Natural (fun n: Natural => True) (m) _)). }
Qed.

Definition eq_geq_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (eqN m n))->(` (geqN m n))). 
Defined.
Theorem eq_geq: eq_geq_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | lq_anf7205759403792798561 ]. smt_now smt_trivial. destruct m as [ | lq_anf7205759403792798560 ]. destruct n as [ | ds_d1di ]. destruct () as [ ]. smt_now smt_trivial. destruct () as [ ]. }
    { destruct n as [ | n ]. destruct n as [ | lq_anf7205759403792798573 ]. smt_now smt_trivial. destruct m as [ | lq_anf7205759403792798572 ]. destruct n as [ | ds_d1di ]. destruct () as [ ]. smt_now smt_trivial. destruct () as [ ]. smt_app IHm. }
Qed.

Definition geq_refl_spec: Prop. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| True}), (` (geqN n n))). 
Defined.
Theorem geq_refl: geq_refl_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. }
Qed.

Definition geq_trans_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), (` (geqN m n)) /\ (` (geqN n o))->(` (geqN m o))). 
Defined.
Theorem geq_trans: geq_trans_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { destruct n as [ | lq_anf7205759403792798586 ]. smt_now smt_trivial. destruct m as [ | m ]. smt_now smt_trivial. destruct n as [ | n ]. destruct () as [ ]. destruct o as [ | o ]. destruct () as [ ]. smt_app IHm. }
Qed.

Definition le_geq_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), ((` (geqN m n)) = (not(` (leN m n))))). 
Defined.
Theorem le_geq: le_geq_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { destruct m as [ | m ]. destruct n as [ | n ]. destruct () as [ ]. smt_now smt_trivial. destruct n as [ | n ]. destruct () as [ ]. smt_app IHm. }
Qed.

Definition ge_geq_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (geN m n))->(` (geqN m n))). 
Defined.
Theorem ge_geq: ge_geq_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | n ]. smt_now smt_trivial. smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition mult_zero_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), ((` (m)) <> (ZeroN)) /\ ((` (n)) <> (ZeroN))->(` (geqN (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined m n)) = (VV))) (fun m: Natural => True) I (mult m n)) n))). 
Defined.
Theorem mult_zero: mult_zero_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  
    { destruct m as [ | m ]. smt_now smt_trivial. 
  assertFresh ((` (mult (injectionCast Natural (fun m: Natural => True) (Suc m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (` (add (injectionCast Natural (fun m: Natural => True) (n) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))))) as lem using (smt_app (mult_suc_l (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)). ). 
  assertFresh ((` (add (injectionCast Natural (fun m: Natural => True) (n) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))))) = (` (add (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (injectionCast Natural (fun n: Natural => True) (n) _)))) as lem using (smt_app (add_comm (injectionCast Natural (fun m: Natural => True) (n) _) (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun n: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _)))). ). smt_app (ge_zero (injectionCast Natural (fun n: Natural => True) (n) _)). smt_app (add_mono_l (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (injectionCast Natural (fun n: Natural => True) (n) _)). smt_app (ge_geq (subsumptionCast Natural (fun VV: Natural => ((` (add_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (add (subsumptionCast Natural (fun VV: Natural => ((` (mult_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) = (VV))) (fun m: Natural => True) _ (mult (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (n) _))) (injectionCast Natural (fun n: Natural => True) (n) _))) (injectionCast Natural (fun n: Natural => True) (n) _)). }
Qed.

Definition ge_anti_comm_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (geN m n))->not(` (geN n m))). 
Defined.
Theorem ge_anti_comm: ge_anti_comm_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | n ]. smt_now smt_trivial. smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition ge_irreflexive_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (geN m n))->not(` (eqN m n))). 
Defined.
Theorem ge_irreflexive: ge_irreflexive_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition ge_trans_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), (` (geN m n)) /\ (` (geN n o))->(` (geN m o))). 
Defined.
Theorem ge_trans: ge_trans_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { destruct m as [ | m ]. smt_now smt_trivial. destruct o as [ | lq_anf7205759403792798641 ]. smt_now smt_trivial. destruct n as [ | n ]. destruct () as [ ]. destruct o as [ | o ]. destruct () as [ ]. smt_app IHm. }
Qed.

Definition ge_eq_trans_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}) (o:{o: Natural| True}), (` (eqN n o)) /\ (` (geN m n))->(` (geN m o))). 
Defined.
Theorem ge_eq_trans: ge_eq_trans_spec.
Proof.
  intros m. intros n. intros o. destruct m as [m mp ].  destruct n as [n np ].  destruct o as [o op ]. 
  induction m as [| m IHm ]. 
    { destruct o as [ | ds_d1cb ]. smt_now smt_trivial. smt_now smt_trivial. }
    { destruct m as [ | m ]. smt_now smt_trivial. destruct o as [ | lq_anf7205759403792798654 ]. smt_now smt_trivial. destruct n as [ | n ]. destruct () as [ ]. destruct o as [ | o ]. destruct () as [ ]. smt_app IHm. }
Qed.

Definition geq_suc_l_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))}), (` (geqN (injectionCast Natural (fun m: Natural => True) (Suc (` (m))) I) (subsumptionCast Natural (fun n: Natural => (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))) (fun n: Natural => True) I (n))))). 
Defined.
Theorem geq_suc_l: geq_suc_l_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | n ]. smt_now smt_trivial. smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition geq_ge_suc_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))}), (` (geN (injectionCast Natural (fun m: Natural => True) (Suc (` (m))) I) (subsumptionCast Natural (fun n: Natural => (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))) (fun n: Natural => True) I (n))))). 
Defined.
Theorem geq_ge_suc: geq_ge_suc_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | n ]. smt_now smt_trivial. smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition ge_suc_l_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| (` (geN m (injectionCast Natural (fun n: Natural => True) (n) np)))}), (` (geN (injectionCast Natural (fun m: Natural => True) (Suc (` (m))) I) (subsumptionCast Natural (fun n: Natural => (` (geN m (injectionCast Natural (fun n: Natural => True) (n) np)))) (fun n: Natural => True) I (n))))). 
Defined.
Theorem ge_suc_l: ge_suc_l_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | n ]. smt_now smt_trivial. smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition geq_ge_eq_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), ((` (geqN m n)) = ((` (geN m n)) \/ (` (eqN m n))))). 
Defined.
Theorem geq_ge_eq: geq_ge_eq_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | n ]. smt_now smt_trivial. smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition geq_not_le_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), ((` (geqN m n)) = (not(` (leN m n))))). 
Defined.
Theorem geq_not_le: geq_not_le_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | n ]. smt_now smt_trivial. smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition ge_eq_le_exhaustive_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (geN m n)) \/ (` (eqN m n)) \/ (` (leN m n))). 
Defined.
Theorem ge_eq_le_exhaustive: ge_eq_le_exhaustive_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | n ]. smt_now smt_trivial. smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition subt_self_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| True}), (` (eqN m n))->((` (subt m (subsumptionCast Natural (fun n: Natural => True) (fun n: Natural => (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))) _ (n)))) = (ZeroN))). 
Defined.
Theorem subt_self: subt_self_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { smt_now smt_trivial. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition subt_suc_l_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))}), ((` (subt (injectionCast Natural (fun m: Natural => True) (Suc (` (m))) I) n)) = (Suc (` (subt m n))))). 
Defined.
Theorem subt_suc_l: subt_suc_l_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | lq_anf7205759403792798689 ]. smt_now smt_trivial. destruct () as [ ]. }
    { destruct n as [ | n ]. smt_now smt_trivial. smt_app IHm. }
Qed.

Definition geq_suc_spec: Prop. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| True}), (` (geqN (injectionCast Natural (fun m: Natural => True) (Suc (` (n))) I) n))). 
Defined.
Theorem geq_suc: geq_suc_spec.
Proof.
  intros n. destruct n as [n np ]. 
  induction n as [| n IHn ]. 
    { smt_now smt_trivial. }
    { smt_app IHn. }
Qed.

Definition subt_leq_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| (` (geqN (injectionCast Natural (fun m: Natural => True) (m) I) (injectionCast Natural (fun n: Natural => True) (n) np)))}), (` (geqN m (subsumptionCast Natural (fun o: Natural => ((` (subt_unrefined m n)) = (o))) (fun n: Natural => True) I (subt m (subsumptionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) I) (injectionCast Natural (fun n: Natural => True) (n) np)))) (fun n: Natural => (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))) _ (n))))))). 
Defined.
Theorem subt_leq: subt_leq_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  induction m as [| m IHm ]. 
    { destruct n as [ | lq_anf7205759403792798697 ]. smt_now smt_trivial. destruct () as [ ]. }
    { destruct n as [ | n ]. smt_app (geq_refl (injectionCast Natural (fun n: Natural => True) (m) _)). smt_app IHm. smt_app (geq_suc (injectionCast Natural (fun n: Natural => True) (m) _)). smt_app (geq_trans (injectionCast Natural (fun m: Natural => True) (Suc m) _) (injectionCast Natural (fun n: Natural => True) (m) _) (subsumptionCast Natural (fun o: Natural => ((` (subt_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (n) _))) = (o))) (fun o: Natural => True) _ (subt (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (n) _)))). }
Qed.

Definition subt_le_spec: Prop. 
Proof. smt_now unshelve refine (forall (m:{m: Natural| True}) (n:{n: Natural| (` (geqN m (injectionCast Natural (fun n: Natural => True) (n) np)))}), ((` (n)) <> (ZeroN))->(` (geN m (subsumptionCast Natural (fun o: Natural => ((` (subt_unrefined m n)) = (o))) (fun n: Natural => True) I (subt m n))))). 
Defined.
Theorem subt_le: subt_le_spec.
Proof.
  intros m. intros n. destruct m as [m mp ].  destruct n as [n np ]. 
  
    { destruct m as [ | m ]. destruct n as [ | lq_anf7205759403792798710 ]. smt_now smt_trivial. destruct () as [ ]. destruct n as [ | n ]. smt_app (geq_refl (injectionCast Natural (fun n: Natural => True) (m) _)). 
  assertFresh ((` (subt (injectionCast Natural (fun m: Natural => True) (Suc m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (Suc n) _))) = (` (subt (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (n) _)))) as lem using smt_trivial. . smt_app (subt_leq (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (injectionCast Natural (fun m: Natural => True) (m) _) I) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (n) _)). smt_app (geq_ge_suc (injectionCast Natural (fun m: Natural => True) (m) _) (subsumptionCast Natural (fun o: Natural => ((` (subt_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (n) _))) = (o))) (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) _ (subt (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (n) _)))). smt_app (eq_equal (subsumptionCast Natural (fun o: Natural => ((` (subt_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (n) _))) = (o))) (fun m: Natural => True) _ (subt (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (n) _))) (subsumptionCast Natural (fun o: Natural => ((` (subt_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (n) _))) = (o))) (fun n: Natural => True) _ (subt (injectionCast Natural (fun m: Natural => True) (Suc m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (Suc n) _)))). smt_app (ge_eq_trans (injectionCast Natural (fun m: Natural => True) (Suc m) _) (subsumptionCast Natural (fun o: Natural => ((` (subt_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (n) _))) = (o))) (fun n: Natural => True) _ (subt (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (n) _))) (subsumptionCast Natural (fun o: Natural => ((` (subt_unrefined (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (n) _))) = (o))) (fun o: Natural => True) _ (subt (injectionCast Natural (fun m: Natural => True) (Suc m) _) (injectionCast Natural (fun n: Natural => (` (geqN (injectionCast Natural (fun m: Natural => True) (m) _) (injectionCast Natural (fun n: Natural => True) (injectionCast Natural (fun n: Natural => True) (n) _) np)))) (Suc n) _)))). }
Qed.

Definition notZ_spec: Prop. 
Proof. smt_now unshelve refine (forall (n:{n: Natural| (n <> (ZeroN))}), (` (geN (injectionCast Natural (fun m: Natural => True) (Suc (` (n))) I) (injectionCast Natural (fun n: Natural => True) (one) I)))). 
Defined.
Theorem notZ: notZ_spec.
Proof.
  intros n. destruct n as [n np ]. 
  
    { destruct n as [ | n ]. smt_now smt_trivial. smt_now smt_trivial. }
Qed.
