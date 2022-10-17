From Coq Require Export Morphisms Setoid Program.Equality.
From EnTree Require Import
     Basics.HeterogeneousRelations
     Basics.QuantType
     Core.EnTreeDefinition
     Core.SubEvent
     Ref.EnTreeSpecDefinition
     Ref.EnTreeSpecFacts
     Ref.SpecM
     Eq.Eqit
.

Import EnTreeNotations.
Local Open Scope entree_scope.

(***
 *** Definition and basic properties of spec_refines
 ***)

(** Definition of refinement for SpecM **)

Definition SpecPreRel (E1 E2 : EvType) Γ1 Γ2 :=
  Rel (FunStackE E1 Γ1) (FunStackE E2 Γ2).
Definition SpecPostRel (E1 E2 : EvType) Γ1 Γ2 :=
  PostRel (FunStackE E1 Γ1) (FunStackE E2 Γ2).

Definition spec_refines {E1 E2 : EvType} {Γ1 Γ2}
           (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
           {R1 R2} (RR : Rel R1 R2)
           (t1 : @SpecM E1 Γ1 R1) (t2 : @SpecM E2 Γ2 R2) :=
  padded_refines RPre RPost RR t1 t2.

Instance Proper_spec_refines E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR :
  Proper (eutt eq ==> eutt eq ==> Basics.flip Basics.impl)
         (@spec_refines E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR).
Admitted.


(** Monad laws for spec_refines **)

Lemma spec_refines_ret E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR r1 r2 :
  (RR r1 r2 : Prop) ->
  @spec_refines E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR (RetS r1) (RetS r2).
Admitted.

Lemma spec_refines_ret_bind_r E1 E2 Γ1 Γ2 R1 R2 A
      RPre RPost RR (t1 : SpecM E1 Γ1 R1) r (k2 : A -> SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR t1 (k2 r) ->
  spec_refines RPre RPost RR t1 (Ret r >>= k2).
Proof.
  intros; setoid_rewrite bind_ret_l; assumption.
Qed.

Lemma spec_refines_ret_bind_l E1 E2 Γ1 Γ2 R1 R2 A
      RPre RPost RR r (k1 : A -> SpecM E1 Γ1 R1) (t2 : SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR (k1 r) t2 ->
  spec_refines RPre RPost RR (Ret r >>= k1) t2.
Proof.
  intros; setoid_rewrite bind_ret_l; assumption.
Qed.

Lemma spec_refines_bind_bind_r E1 E2 Γ1 Γ2 R1 R2 A1 A2
      RPre RPost RR (t1 : SpecM E1 Γ1 R1) (t2 : SpecM E2 Γ2 A1)
      (k1 : A1 -> SpecM E2 Γ2 A2) (k2 : A2 -> SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR t1 (t2 >>= (fun a => k1 a >>= k2)) ->
  spec_refines RPre RPost RR t1 ((t2 >>= k1) >>= k2).
Proof.
  intros; setoid_rewrite bind_bind; assumption.
Qed.

Lemma spec_refines_bind_bind_l E1 E2 Γ1 Γ2 R1 R2 A1 A2
      RPre RPost RR (t1 : SpecM E1 Γ1 A1) (k1 : A1 -> SpecM E1 Γ1 A2)
      (k2 : A2 -> SpecM E1 Γ1 R1) (t2 : SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR (t1 >>= (fun a => k1 a >>= k2)) t2 ->
  spec_refines RPre RPost RR ((t1 >>= k1) >>= k2) t2.
Proof.
  intros; setoid_rewrite bind_bind; assumption.
Qed.


(** Refinement rules for the SpecM combinators **)

(* FIXME: maybe move these to SpecM.v? *)
#[global]
Instance ReSum_FunStack_EvType (E : EvType) Γ : ReSum E (FunStackE E Γ) :=
  ReSum_FunStackE_E _ _.
#[global]
Instance ReSumRet_FunStack_EvType (E : EvType) Γ : ReSumRet E (FunStackE E Γ) :=
  ReSumRet_FunStackE_E _ _.

Lemma spec_refines_trigger (E1 E2 : EvType) Γ1 Γ2 R1 R2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      RR (e1 : E1) (e2 : E2)
      (k1 : encodes e1 -> SpecM E1 Γ1 R1)
      (k2 : encodes e2 -> SpecM E2 Γ2 R2) :
  RPre (resum e1) (resum e2) ->
  (forall a b,
      RPost (resum e1) (resum e2) a b ->
      spec_refines RPre RPost RR (k1 (resum_ret e1 a)) (k2 (resum_ret e2 b))) ->
  spec_refines RPre RPost RR (TriggerS e1 >>= k1) (TriggerS e2 >>= k2).
Admitted.

Lemma spec_refines_exists_r E1 E2 Γ1 Γ2 R1 R2 A `{QuantType A}
      RPre RPost RR (phi : SpecM E1 Γ1 R1) (kphi : A -> SpecM E2 Γ2 R2) a :
  spec_refines RPre RPost RR phi (kphi a) ->
  spec_refines RPre RPost RR phi (ExistsS A >>= kphi).
Admitted.

Lemma spec_refines_exists_l E1 E2 Γ1 Γ2 R1 R2 A `{QuantType A}
      RPre RPost RR (phi : SpecM E2 Γ2 R2) (kphi : A -> SpecM E1 Γ1 R1) a :
  spec_refines RPre RPost RR (kphi a) phi ->
  spec_refines RPre RPost RR (ExistsS A >>= kphi) phi.
Admitted.

Lemma spec_refines_forall_r E1 E2 Γ1 Γ2 R1 R2 A `{QuantType A}
      RPre RPost RR (phi : SpecM E1 Γ1 R1) (kphi : A -> SpecM E2 Γ2 R2) :
  (forall a, spec_refines RPre RPost RR phi (kphi a)) ->
  spec_refines RPre RPost RR phi (ForallS A >>= kphi).
Admitted.

Lemma spec_refines_forall_l E1 E2 Γ1 Γ2 R1 R2 A `{QuantType A}
      RPre RPost RR (phi : SpecM E2 Γ2 R2) (kphi : A -> SpecM E1 Γ1 R1) :
  (forall a, spec_refines RPre RPost RR (kphi a) phi) ->
  spec_refines RPre RPost RR (ForallS A >>= kphi) phi.
Admitted.


(** Refinement rules for the SpecM combinators **)

Lemma spec_refines_if_r E1 E2 Γ1 Γ2 R1 R2
      RPre RPost RR (t1 : SpecM E1 Γ1 R1) (t2 t3 : SpecM E2 Γ2 R2) b :
  (b = true -> spec_refines RPre RPost RR t1 t2) ->
  (b = false -> spec_refines RPre RPost RR t1 t3) ->
  spec_refines RPre RPost RR t1 (if b then t2 else t3).
Proof.
  intros; destruct b; eauto.
Qed.

Lemma spec_refines_if_l E1 E2 Γ1 Γ2 R1 R2
      RPre RPost RR (t1 t2 : SpecM E1 Γ1 R1) (t3 : SpecM E2 Γ2 R2) b :
  (b = true -> spec_refines RPre RPost RR t1 t3) ->
  (b = false -> spec_refines RPre RPost RR t2 t3) ->
  spec_refines RPre RPost RR (if b then t1 else t2) t3.
Proof.
  intros; destruct b; eauto.
Qed.

Lemma spec_refines_if_bind_r E1 E2 Γ1 Γ2 R1 R2 A
      RPre RPost RR (t1 : SpecM E1 Γ1 R1) (t2 t3 : SpecM E2 Γ2 A)
      (b : bool) (t4 : A -> SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR t1 (if b then t2 >>= t4 else t3 >>= t4) ->
  spec_refines RPre RPost RR t1 ((if b then t2 else t3) >>= t4).
Proof.
  intros; destruct b; eauto.
Qed.

Lemma spec_refines_if_bind_l E1 E2 Γ1 Γ2 R1 R2 A
      RPre RPost RR (t1 t2 : SpecM E1 Γ1 A) (t3 : A -> SpecM E1 Γ1 R1)
      (b : bool) (t4 : SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR (if b then t1 >>= t3 else t2 >>= t3) t4 ->
  spec_refines RPre RPost RR ((if b then t1 else t2) >>= t3) t4.
Proof.
  intros; destruct b; eauto.
Qed.

