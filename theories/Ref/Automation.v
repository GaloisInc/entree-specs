From Coq Require Export
     Datatypes
     Arith.PeanoNat
     Wf_nat
     Morphisms
     Setoid
     Program.Equality
     Lists.List
     Logic.EqdepFacts
     Eqdep EqdepFacts
.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Basics.QuantType
     Core.EnTreeDefinition
     Core.SubEvent
     Ref.EnTreeSpecDefinition
     Ref.EnTreeSpecFacts
     Ref.EnTreeSpecCombinatorFacts
     Ref.SpecM
     Eq.Eqit
     Ref.MRecSpec
     Ref.SpecMFacts
.

(* From Coq 8.15 *)
Notation "( x ; y )" := (existT _ x y) (at level 0, format "( x ;  '/  ' y )").
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").

Import SpecMNotations.
Local Open Scope entree_scope.

(***
 *** Definition and basic properties of spec_refines
 ***)

(** Definition of refinement for SpecM **)

Definition SpecPreRel (E1 E2 : EvType) Γ1 Γ2 :=
  Rel (FunStackE E1 Γ1) (FunStackE E2 Γ2).
Definition SpecPostRel (E1 E2 : EvType) Γ1 Γ2 :=
  PostRel (FunStackE E1 Γ1) (FunStackE E2 Γ2).

(* The precondition requiring events on both sides to be equal *)
Definition eqPreRel {E Γ} : SpecPreRel E E Γ Γ := eq.

(* The postcondition requiring return values on both sides to be equal *)
Definition eqPostRel {E Γ} : SpecPostRel E E Γ Γ :=
  fun e1 e2 a1 a2 => eq_dep1 _ _ e1 a1 e2 a2.

(* Spec refinement = padded refinement *)
Definition spec_refines {E1 E2 : EvType} {Γ1 Γ2}
           (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
           {R1 R2} (RR : Rel R1 R2)
           (t1 : @SpecM E1 Γ1 R1) (t2 : @SpecM E2 Γ2 R2) :=
  padded_refines RPre RPost RR t1 t2.

Instance Proper_spec_refines E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR :
  Proper (eutt eq ==> eutt eq ==> Basics.flip Basics.impl)
         (@spec_refines E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR).
Proof.
  repeat intro. eapply padded_refines_proper_eutt; eauto.
Qed.

(** RetS and bind laws for spec_refines **)

Lemma spec_refines_ret E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR r1 r2 :
  (RR r1 r2 : Prop) ->
  @spec_refines E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR (RetS r1) (RetS r2).
Proof.
  intros. apply padded_refines_ret. auto.
Qed.

Lemma spec_refines_ret_bind_r E1 E2 Γ1 Γ2 R1 R2 A
      RPre RPost RR (t1 : SpecM E1 Γ1 R1) r (k2 : A -> SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR t1 (k2 r) ->
  spec_refines RPre RPost RR t1 (RetS r >>= k2).
Proof.
  intros; setoid_rewrite bind_ret_l; assumption.
Qed.

Lemma spec_refines_ret_bind_l E1 E2 Γ1 Γ2 R1 R2 A
      RPre RPost RR r (k1 : A -> SpecM E1 Γ1 R1) (t2 : SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR (k1 r) t2 ->
  spec_refines RPre RPost RR (RetS r >>= k1) t2.
Proof.
  intros; setoid_rewrite bind_ret_l; assumption.
Qed.

Lemma padded_refines_ret_bind_l E1 E2 `{EncodingType E1} `{EncodingType E2} R1 R2 A 
      RPre RPost RR r (k1 : A -> entree_spec E1 R1) (t : entree_spec E2 R2) :
  padded_refines RPre RPost RR (k1 r) t ->
  padded_refines RPre RPost RR (EnTree.bind (Ret r) k1) t.
Proof.
  intros. rewrite bind_ret_l. auto.
Qed.

Lemma padded_refines_ret_bind_r E1 E2 `{EncodingType E1} `{EncodingType E2} R1 R2 A 
      RPre RPost RR r (k2 : A -> entree_spec E2 R2) (t : entree_spec E1 R1) :
  padded_refines RPre RPost RR t (k2 r) ->
  padded_refines RPre RPost RR t (EnTree.bind (Ret r) k2).
Proof.
  intros. rewrite bind_ret_l. auto.
Qed.

Lemma padded_refines_bind_bind_r E1 E2 `{EncodingType E1} `{EncodingType E2} R1 R2 A1 A2
      RPre RPost RR (t1 : entree_spec E1 R1) (t2 : entree_spec E2 A1)
      (k1 : A1 -> entree_spec E2 A2) (k2 : A2 -> entree_spec E2 R2) :
  padded_refines RPre RPost RR t1 (EnTree.bind t2 (fun a => EnTree.bind (k1 a) k2)) ->
  padded_refines RPre RPost RR t1 (EnTree.bind (EnTree.bind t2 k1) k2).
Proof.
  intros; setoid_rewrite bind_bind; assumption.
Qed.

Lemma padded_refines_bind_bind_l E1 E2 `{EncodingType E1} `{EncodingType E2} R1 R2 A1 A2
      RPre RPost RR (t1 : entree_spec E1 R1) (t2 : entree_spec E2 A1)
      (k1 : A1 -> entree_spec E2 A2) (k2 : A2 -> entree_spec E2 R2) :
  padded_refines RPre RPost RR (EnTree.bind t2 (fun a => EnTree.bind (k1 a) k2)) t1 ->
  padded_refines RPre RPost RR (EnTree.bind (EnTree.bind t2 k1) k2) t1.
Proof.
  intros; setoid_rewrite bind_bind; assumption.
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

Lemma encodes_ReSum_FunStack_EvType:
  forall (E1 : EvType) (Γ1 : FunStack) (e1 : E1), encodes (ReSum_FunStack_EvType E1 Γ1 e1) = encodes e1.
Proof.
  intros E1 Γ1 e1.
  induction Γ1. auto. cbn. setoid_rewrite IHΓ1. auto.
Qed.

Lemma type_eq_map_JMeq : forall (A B : Type), A = B -> exists fab : A -> B, 
  forall a, (fab a) ~= a.
Proof. 
  intros. subst. exists id. auto.
Qed.

(*
Lemma padded_refines_bind_type_eq E1 E2 `{EncodingType E1} `{EncodingType E2} R1 R2 R1' R2' S1 S2 
      PRe RPost 
*)
Lemma spec_refines_trigger_bind (E1 E2 : EvType) Γ1 Γ2 R1 R2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      RR (e1 : E1) (e2 : E2)
      (k1 : encodes e1 -> SpecM E1 Γ1 R1)
      (k2 : encodes e2 -> SpecM E2 Γ2 R2) :
  RPre (resum e1) (resum e2) ->
  (forall a b,
      RPost (resum e1) (resum e2) a b ->
      spec_refines RPre RPost RR (k1 (resum_ret e1 a)) (k2 (resum_ret e2 b))) ->
  spec_refines RPre RPost RR (TriggerS e1 >>= k1) (TriggerS e2 >>= k2).
Proof.
  intros.
  specialize (encodes_ReSum_FunStack_EvType E1 Γ1 e1) as He1. 
  specialize (encodes_ReSum_FunStack_EvType E2 Γ2 e2) as He2.
  symmetry in He1, He2.
  apply type_eq_map_JMeq in He1 as [fe1 Hfe1].
  apply type_eq_map_JMeq in He2 as [fe2 Hfe2].
  eapply padded_refines_bind with (RR := fun a b => (RPost (resum e1) (resum e2) (fe1 a) (fe2 b))).
  - apply padded_refines_vis. auto.
    intros. apply padded_refines_ret.
    assert (fe1 (resum_ret e1 a) = a).
    {
      clear - Hfe1. induction Γ1; cbn; auto.
      - apply JMeq_eq. auto.
      - cbn. erewrite <- IHΓ1; eauto.
    }
    assert (fe2 (resum_ret e2 b) = b).
    {
      clear - Hfe2. induction Γ2; cbn; auto.
      - apply JMeq_eq. auto.
      - cbn. erewrite <- IHΓ2; eauto.
    }
    setoid_rewrite H2.  setoid_rewrite H3.
    auto.
  - intros. eapply H0 in H1.
    assert (r1 = (resum_ret e1 (fe1 r1))).
    {
      clear - Hfe1.
      induction Γ1; eauto. cbn. symmetry. apply JMeq_eq. auto.
    }
    assert (r2 = (resum_ret e2 (fe2 r2))).
    {
      clear - Hfe2.
      induction Γ2; eauto. cbn. symmetry. apply JMeq_eq. auto.
    }
    rewrite H2, H3. auto.
Qed.


(** Refinement rules for Quantifiers **)

Lemma spec_refines_exists_r E1 E2 Γ1 Γ2 R1 R2 A `{QuantType A}
      RPre RPost RR (phi : SpecM E1 Γ1 R1) (kphi : A -> SpecM E2 Γ2 R2) a :
  spec_refines RPre RPost RR phi (kphi a) ->
  spec_refines RPre RPost RR phi (ExistsS A >>= kphi).
Proof.
  intros.
  apply padded_refines_exists_specr. eexists. eauto.
Qed.

Lemma spec_refines_exists_l E1 E2 Γ1 Γ2 R1 R2 A `{QuantType A}
      RPre RPost RR (phi : SpecM E2 Γ2 R2) (kphi : A -> SpecM E1 Γ1 R1) :
  (forall a, spec_refines RPre RPost RR (kphi a) phi) ->
  spec_refines RPre RPost RR (ExistsS A >>= kphi) phi.
Proof.
  intros.
  apply padded_refines_exists_specl. auto.
Qed.

Lemma spec_refines_forall_r E1 E2 Γ1 Γ2 R1 R2 A `{QuantType A}
      RPre RPost RR (phi : SpecM E1 Γ1 R1) (kphi : A -> SpecM E2 Γ2 R2) :
  (forall a, spec_refines RPre RPost RR phi (kphi a)) ->
  spec_refines RPre RPost RR phi (ForallS A >>= kphi).
Proof.
  intros. apply padded_refines_forall_specr. auto.
Qed.

Lemma spec_refines_forall_l E1 E2 Γ1 Γ2 R1 R2 A `{QuantType A}
      RPre RPost RR (phi : SpecM E2 Γ2 R2) (kphi : A -> SpecM E1 Γ1 R1) a :
  spec_refines RPre RPost RR (kphi a) phi ->
  spec_refines RPre RPost RR (ForallS A >>= kphi) phi.
Proof.
  intros. apply padded_refines_forall_specl. eexists. eauto.
Qed.


(** Refinement rules for Assert and Assume **)

Lemma spec_refines_assert_r E1 E2 Γ1 Γ2 R1 R2 (P:Prop)
      RPre RPost RR (phi : SpecM E1 Γ1 R1) (kphi : unit -> SpecM E2 Γ2 R2) :
  P -> spec_refines RPre RPost RR phi (kphi tt) ->
  spec_refines RPre RPost RR phi (AssertS P >>= kphi).
Proof.
  intros. apply padded_refines_assertr; auto.
Qed.


Lemma spec_refines_assert_l E1 E2 Γ1 Γ2 R1 R2 (P:Prop)
      RPre RPost RR (phi : SpecM E2 Γ2 R2) (kphi : unit -> SpecM E1 Γ1 R1) :
  (P -> spec_refines RPre RPost RR (kphi tt) phi) ->
  spec_refines RPre RPost RR (AssertS P >>= kphi) phi.
Proof.
  intros. apply padded_refines_assertl; auto.
Qed.

Lemma spec_refines_assume_r E1 E2 Γ1 Γ2 R1 R2 (P:Prop)
      RPre RPost RR (phi : SpecM E1 Γ1 R1) (kphi : unit -> SpecM E2 Γ2 R2) :
  (P -> spec_refines RPre RPost RR phi (kphi tt)) ->
  spec_refines RPre RPost RR phi (AssumeS P >>= kphi).
Proof.
  intros. apply padded_refines_assumer; auto.
Qed.

Lemma spec_refines_assume_l E1 E2 Γ1 Γ2 R1 R2 (P:Prop)
      RPre RPost RR (phi : SpecM E2 Γ2 R2) (kphi : unit -> SpecM E1 Γ1 R1) :
  P -> spec_refines RPre RPost RR (kphi tt) phi ->
  spec_refines RPre RPost RR (AssumeS P >>= kphi) phi.
Proof.
  intros. apply padded_refines_assumel; auto.
Qed.

(* FIXME: need rules to add binds to all the unary combinators *)

(** Refinement rules for if-then-else **)

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


(** Refinement rules for lists **)

Lemma spec_refines_match_list_r E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A
      (t1 : SpecM E1 Γ1 R1) (t2 : A -> list A -> SpecM E2 Γ2 R2)
      (t3 : SpecM E2 Γ2 R2) xs :
  (forall x xs', xs = x :: xs' -> spec_refines RPre RPost RR t1 (t2 x xs')) ->
  (xs = nil -> spec_refines RPre RPost RR t1 t3) ->
  spec_refines RPre RPost RR t1 (match xs with | x :: xs' => t2 x xs' | nil => t3 end).
Proof.
  intros. destruct xs; eauto.
Qed.

Lemma spec_refines_match_list_l E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A
      (t3 : SpecM E2 Γ2 R2)
      (t1 : A -> list A -> SpecM E1 Γ1 R1) (t2 : SpecM E1 Γ1 R1) xs :
  (forall x xs', xs = x :: xs' -> spec_refines RPre RPost RR (t1 x xs') t3) ->
  (xs = nil -> spec_refines RPre RPost RR t2 t3) ->
  spec_refines RPre RPost RR (match xs with | x :: xs' => t1 x xs' | nil => t2 end) t3.
Proof.
  intros. destruct xs; eauto.
Qed.

Lemma spec_refines_match_list_bind_r B E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A
      (t1 : SpecM E1 Γ1 R1)
      (t2 : A -> list A -> SpecM E2 Γ2 B) (t3 : SpecM E2 Γ2 B)
      (t4 : B -> SpecM E2 Γ2 R2) xs :
  spec_refines RPre RPost RR t1 (match xs with | x :: xs' => t2 x xs' >>= t4 | nil => t3 >>= t4 end) ->
  spec_refines RPre RPost RR t1 ((match xs with | x :: xs' => t2 x xs' | nil => t3 end) >>= t4).
Proof.
  intros. destruct xs; eauto.
Qed.

Lemma spec_refines_match_list_bind_l B E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A
      (t3 : SpecM E2 Γ2 R2)
      (t1 : A -> list A -> SpecM E1 Γ1 B) (t2 : SpecM E1 Γ1 B)
      (t4 : B -> SpecM E1 Γ1 R1) xs :
  spec_refines RPre RPost RR (match xs with | x :: xs' => t1 x xs' >>= t4 | nil => t2 >>= t4 end) t3 ->
  spec_refines RPre RPost RR ((match xs with | x :: xs' => t1 x xs' | nil => t2 end) >>= t4) t3.
Proof.
  intros. destruct xs; eauto.
Qed.


(** Refinement rules for pairs **)

Lemma spec_refines_match_pair_r E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A B
      (t1 : SpecM E1 Γ1 R1) (t2 : A -> B -> SpecM E2 Γ2 R2) pr :
  (forall x y, pr = (x, y) -> spec_refines RPre RPost RR t1 (t2 x y)) ->
  spec_refines RPre RPost RR t1 (match pr with | (x,y) => t2 x y end).
Proof.
  intros. destruct pr; eauto.
Qed.
Lemma spec_refines_match_pair_l E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A B
      (t1 : A -> B -> SpecM E1 Γ1 R1) (t2 : SpecM E2 Γ2 R2) pr :
  (forall x y, pr = (x, y) -> spec_refines RPre RPost RR (t1 x y) t2) ->
  spec_refines RPre RPost RR (match pr with | (x,y) => t1 x y end) t2.
Proof.
  intros. destruct pr; eauto.
Qed.

Lemma spec_refines_match_pair_bind_r C E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A B
      (t1 : SpecM E1 Γ1 R1) (t2 : A -> B -> SpecM E2 Γ2 C)
      (t3 : C -> SpecM E2 Γ2 R2) pr :
  spec_refines RPre RPost RR t1 (match pr with | (x,y) => t2 x y >>= t3 end) ->
  spec_refines RPre RPost RR t1 ((match pr with | (x,y) => t2 x y end) >>= t3).
Proof.
  intros. destruct pr; eauto.
Qed.
Lemma spec_refines_match_pair_bind_l C E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A B
      (t1 : A -> B -> SpecM E1 Γ1 C) (t2 : SpecM E2 Γ2 R2)
      (t3 : C -> SpecM E1 Γ1 R1) pr :
  spec_refines RPre RPost RR (match pr with | (x,y) => t1 x y >>= t3 end) t2 ->
  spec_refines RPre RPost RR ((match pr with | (x,y) => t1 x y end) >>= t3) t2.
Proof.
  intros. destruct pr; eauto.
Qed.


(** The trepeat combinator **)

(* Repeat a specification n times *)
Fixpoint trepeat {E Γ R} (n : nat) (s : SpecM E Γ R) : SpecM E Γ unit :=
  match n with
  | 0 => RetS tt
  | S m => s;; trepeat m s
  end.

Lemma spec_refines_trepeat_zero_r E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR
      (t1 : SpecM E1 Γ1 R1) (t2 : SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR t1 (RetS tt) ->
  spec_refines RPre RPost RR t1 (trepeat 0 t2).
Proof. eauto. Qed.

Lemma spec_refines_trepeat_suc_r E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR
      (t1 : SpecM E1 Γ1 R1) n (t2 : SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR t1 (t2 ;; trepeat n t2) ->
  spec_refines RPre RPost RR t1 (trepeat (S n) t2).
Proof. eauto. Qed.

Lemma spec_refines_trepeat_bind_zero_r E1 E2 Γ1 Γ2 R1 R2 R3 RPre RPost RR
      (t1 : SpecM E1 Γ1 R1) (t2 : SpecM E2 Γ2 R2) (t3 : unit -> SpecM E2 Γ2 R3) :
  spec_refines RPre RPost RR t1 (t3 tt) ->
  spec_refines RPre RPost RR t1 (trepeat 0 t2 >>= t3).
Proof. eauto. Qed.

Lemma spec_refines_trepeat_bind_suc_r E1 E2 Γ1 Γ2 R1 R2 R3 RPre RPost RR
      (t1 : SpecM E1 Γ1 R1) n (t2 : SpecM E2 Γ2 R2) (t3 : unit -> SpecM E2 Γ2 R3) :
  spec_refines RPre RPost RR t1 (t2 ;; (trepeat n t2 >>= t3)) ->
  spec_refines RPre RPost RR t1 (trepeat (S n) t2 >>= t3).
Proof.
  unfold BindS; simpl; unfold BindS, Monad.bind. rewrite Eqit.bind_bind. eauto.
Qed.


(** Refinement rules for recursion **)

Lemma spec_refines_call (E1 E2 : EvType) Γ1 Γ2 frame1 frame2
      (RPre : SpecPreRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (RPost : SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (RR : Rel (encodes call1) (encodes call2)) :
  RPre (inl call1) (inl call2) ->
  (forall r1 r2, RPost (inl call1) (inl call2) r1 r2 -> RR r1 r2) ->
  spec_refines RPre RPost RR (CallS _ _ _ call1) (CallS _ _ _ call2).
Proof.
  intros. apply padded_refines_vis. auto. intros.
  apply padded_refines_ret. auto.
Qed.

(* The bind of one recursive call refines the bind of another if the recursive
   calls are in the current RPre and, for all return values for them in RPost,
   the bind continuations refine each other *)
Lemma spec_refines_call_bind (E1 E2 : EvType) Γ1 Γ2 frame1 frame2 R1 R2
      (RPre : SpecPreRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (RPost : SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      RR (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (k1 : FrameCallRet frame1 call1 -> SpecM E1 (frame1 :: Γ1) R1)
      (k2 : FrameCallRet frame2 call2 -> SpecM E2 (frame2 :: Γ2) R2) :
  RPre (inl call1) (inl call2) ->
  (forall r1 r2,
      RPost (inl call1) (inl call2) r1 r2 ->
      spec_refines RPre RPost RR (k1 (resum_ret call1 r1)) (k2 (resum_ret call2 r2))) ->
  spec_refines RPre RPost RR (CallS _ _ _ call1 >>= k1) (CallS _ _ _ call2 >>= k2).
Proof.
  intros. eapply padded_refines_bind; try eapply spec_refines_call; eauto.
Qed.

(* Add a bind to a RetS to a CallS on the left *)
Lemma spec_refines_call_bind_ret_l (E1 E2 : EvType) Γ1 Γ2 frame1 frame2 R2
      (RPre : SpecPreRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (RPost : SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (call1 : FrameCall frame1) t2 (RR : Rel (FrameCallRet frame1 call1) R2) :
  spec_refines RPre RPost RR (CallS _ _ _ call1 >>= RetS) t2 ->
  spec_refines RPre RPost RR (CallS _ _ _ call1) t2.
Proof. intro; rewrite <- (bind_ret_r (CallS _ _ _ _)); eauto. Qed.

(* Add a bind to a RetS to a CallS on the right *)
Lemma spec_refines_call_bind_ret_r (E1 E2 : EvType) Γ1 Γ2 frame1 frame2
      (RPre : SpecPreRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (RPost : SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      R1 t1 (call2 : FrameCall frame2) (RR : Rel R1 (FrameCallRet frame2 call2)) :
  spec_refines RPre RPost RR t1 (CallS _ _ _ call2 >>= RetS) ->
  spec_refines RPre RPost RR t1 (CallS _ _ _ call2).
Proof. intro H; rewrite <- (bind_ret_r (CallS _ _ _ _)); eauto. Qed.

(* Add a precondition relation for a new frame on the FunStack *)
Definition pushPreRel {E1 E2 : EvType} {Γ1 Γ2 frame1 frame2}
           (precond : Rel (FrameCall frame1) (FrameCall frame2))
           (RPre : SpecPreRel E1 E2 Γ1 Γ2) :
  SpecPreRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2) :=
  fun a1 a2 => match a1,a2 with
               | inl args1, inl args2 => precond args1 args2
               | inr ev1, inr ev2 => RPre ev1 ev2
               | _, _ => False
               end.

(* Add a postcondition relation for a new frame on the FunStack *)
Definition pushPostRel {E1 E2 : EvType} {Γ1 Γ2 frame1 frame2}
           (postcond : PostRel (FrameCall frame1) (FrameCall frame2))
           (RPost : SpecPostRel E1 E2 Γ1 Γ2) :
  SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2) :=
  fun a1 a2 => match a1,a2 with
               | inl args1, inl args2 => postcond args1 args2
               | inr ev1, inr ev2 => RPost ev1 ev2
               | _, _ => fun _ _ => False
               end.

Lemma spec_refines_multifix (E1 E2 : EvType) Γ1 Γ2 frame1 frame2 
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (bodies2 : FrameTuple E2 (frame2 :: Γ2) frame2)
      (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (RR : Rel (encodes call1) (encodes call2))
      (precond : Rel (FrameCall frame1) (FrameCall frame2))
      (postcond : PostRel (FrameCall frame1) (FrameCall frame2)) :
  precond call1 call2 ->
  (forall r1 r2, postcond call1 call2 r1 r2 -> RR r1 r2) ->
  (forall call1' call2',
      precond call1' call2' ->
      spec_refines (pushPreRel precond RPre) (pushPostRel postcond RPost)
                   (postcond call1' call2')
                   (applyFrameTuple _ _ _ bodies1 call1')
                   (applyFrameTuple _ _ _ bodies2 call2')) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1)
               (MultiFixS E2 Γ2 frame2 bodies2 call2).

Proof.
  intros Hcalls HRR Hbody.
  unfold MultiFixS. 
  eapply padded_refines_interp_mrec_spec with (RPreInv := precond) (RPostInv := postcond).
  - intros. apply Hbody in H. eapply padded_refines_monot; try apply H; auto; clear - E1.
    + intros call1 call2 Hcall. 
      destruct call1; destruct call2; cbn in *; try contradiction;
        constructor; auto.
    + intros call1 call2 r1 r2 H. destruct H; auto.
  - apply Hbody in Hcalls.
    eapply padded_refines_monot; try apply Hcalls; auto; clear - E1.
    + intros call1 call2 Hcall. 
      destruct call1; destruct call2; cbn in *; try contradiction;
        constructor; auto.
    + intros call1 call2 r1 r2 H. destruct H; auto.
Qed.

(* The bind of one multifix refines the bind of another if: the recursive calls
   which start the multifixes are related to each other by the supplied
   precondition; the bodies of the multifixes refine each other and return
   values that satisfy the supplied postcondition for all calls that satisfy the
   precondition; and that the bind continuations refine each other for all
   outputs in the supplied postcondition *)
Lemma spec_refines_multifix_bind (E1 E2 : EvType) Γ1 Γ2 frame1 frame2 R1 R2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2) RR
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (bodies2 : FrameTuple E2 (frame2 :: Γ2) frame2)
      (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (k1 : FrameCallRet frame1 call1 -> SpecM E1 Γ1 R1)
      (k2 : FrameCallRet frame2 call2 -> SpecM E2 Γ2 R2)
      (precond : Rel (FrameCall frame1) (FrameCall frame2))
      (postcond : PostRel (FrameCall frame1) (FrameCall frame2)) :
  precond call1 call2 ->
  (forall call1' call2',
      precond call1' call2' ->
      spec_refines (pushPreRel precond RPre) (pushPostRel postcond RPost)
                   (postcond call1' call2')
                   (applyFrameTuple _ _ _ bodies1 call1')
                   (applyFrameTuple _ _ _ bodies2 call2')) ->
  (forall r1 r2,
      postcond call1 call2 r1 r2 ->
      spec_refines RPre RPost RR (k1 r1) (k2 r2)) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1 >>= k1)
               (MultiFixS E2 Γ2 frame2 bodies2 call2 >>= k2).
Proof.
  intros.
  eapply padded_refines_bind; try eapply spec_refines_multifix; eauto.
Qed.

(* Build a RecFrame with a single, unary function *)
Definition unary1Frame (A B : Type) : RecFrame :=
  cons (LRT_Fun A (fun _ => LRT_Ret B)) nil.

Notation unary1Call x := (mkFrameCall (unary1Frame _ _) 0 x).


(* The total correctness specification *)
Definition total_spec {E Γ A B} `{QuantType B}
           (pre : A -> Prop) (post : A -> B -> Prop) (a : A) : SpecM E Γ B :=
  AssumeS (pre a);;
  b <- ExistsS B;;
  AssertS (post a b);;
  RetS b.

Definition uncall_unary1Frame {A B} (c : FrameCall (unary1Frame A B)) : A.
destruct c. cbn in args. destruct n.
- destruct args as [a ?]. exact a.
- destruct args as [[] []].
Defined.

Definition call_unary1Frame {A B} (c : FrameCall (unary1Frame A B)) (b : B) : encodes c.
destruct c. destruct n. destruct args. cbn. exact b.
cbn in args. destruct args as [ [] _].
Defined.

(* The one-step unfolding of total_spec with recursive calls *)
Definition total_spec_fix_body {E Γ A B} `{QuantType A} `{QuantType B}
           (pre : A -> Prop) (post : A -> B -> Prop) (rdec : A -> A -> Prop)
           (a : A) : SpecM E (unary1Frame A B :: Γ) B :=
  AssumeS (pre a);;
  n <- ExistsS nat;;
  trepeat n (a' <- ExistsS A;;
             AssertS (pre a' /\ rdec a' a);;
             CallS E Γ _ (mkFrameCall (unary1Frame A B) 0 a'));;
  b <- ExistsS B;;
  AssertS (post a b);;
  RetS b.

(* total_spec defined with recursive calls, primarily written as part of a proof*)
Definition total_spec_fix {E Γ A B} `{QuantType A} `{QuantType B}
           (pre : A -> Prop) (post : A -> B -> Prop) (rdec : A -> A -> Prop)
           (a : A) : SpecM E Γ B.
  eapply @interp_mrec_spec with (D := (FrameCall (unary1Frame A B)));
    try  (apply (total_spec_fix_body pre post rdec a)).
  clear a.
  intros call. specialize (uncall_unary1Frame call) as a. cbn. 
  eapply EnTree.bind.
  exact (total_spec_fix_body pre post rdec (uncall_unary1Frame call)).
  intros b. exact (Ret (call_unary1Frame call b)).
Defined.

(* Add a precondition relation for proving total_spec refinement *)
Definition pushTSPreRel {E1 E2 : EvType} {Γ1 Γ2 frame1 A2 B2}
           (tsPre : A2 -> Prop)
           (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
           (RPre : SpecPreRel E1 E2 Γ1 Γ2) :
  SpecPreRel E1 E2 (frame1 :: Γ1) (unary1Frame A2 B2 :: Γ2) :=
  fun a1 a2 => match a1,a2 with
               | inl args1, inl (FrameCallOfArgs _ 0 (existT _ a2 _)) =>
                 tsPre a2 /\ precond args1 (unary1Call a2)
               | inr ev1, inr ev2 => RPre ev1 ev2
               | _, _ => False
               end.

(* Add a postcondition relation for proving total_spec refinement *)
Definition pushTSPostRel {E1 E2 : EvType} {Γ1 Γ2 frame1 A2 B2}
           (tsPost : A2 -> B2 -> Prop)
           (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
           (RPost : SpecPostRel E1 E2 Γ1 Γ2) :
  SpecPostRel E1 E2 (frame1 :: Γ1) (unary1Frame A2 B2 :: Γ2) :=
  fun a1 a2 => match a1,a2 return encodes a1 -> encodes a2 -> Prop with
               | inl args1, inl (FrameCallOfArgs _ 0 (existT _ a2 _)) =>
                 fun r1 b2 => tsPost a2 b2 /\ postcond args1 (unary1Call a2) r1 b2
               | inr a1', inr a2' => RPost a1' a2'
               | _, _ => fun _ _ => False
               end.

(* Add a postcondition to the return relation for proving total_spec refinement *)
Definition pushTSRR {frame1 A2 B2}
           (tsPost : A2 -> B2 -> Prop)
           (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
           (call1 : FrameCall frame1) (a2 : A2) :
  Rel (FrameCallRet frame1 call1) B2 :=
  fun r1 r2 => tsPost a2 r2 /\ postcond call1 (unary1Call a2) r1 r2.

Ltac quantr := apply padded_refines_assumer || apply padded_refines_assertr ||
                     apply interp_mrec_spec_assumer || apply interp_mrec_spec_assertr || 
                     apply padded_refines_exists_specr || 
                     apply padded_refines_forall_specr ||
                     apply interp_mrec_spec_forall_specr ||
                     apply interp_mrec_spec_exists_specr
.

Ltac quantl := apply padded_refines_assumel || apply padded_refines_assertl ||
                     apply interp_mrec_spec_assumel || apply interp_mrec_spec_assertl ||
                     apply padded_refines_exists_specl || 
                     apply padded_refines_forall_specl ||
                     apply interp_mrec_spec_forall_specl ||
                     apply interp_mrec_spec_exists_specl.

Lemma total_spec_fix_refines_total_spec_aux1:
  forall (E : EvType) (Γ : FunStack) (A B : Type) (H : QuantType A) (H0 : QuantType B)
    (pre : A -> Prop) (post : Rel A B) (rdec : Rel A A) (a : A),
    strict_refines
     (interp_mrec_spec
        (fun call : FrameCall (unary1Frame A B) =>
           EnTree.bind
             (EnTree.bind (AssumeS (pre (uncall_unary1Frame call)))
                (fun _ : unit =>
                    EnTree.bind (ExistsS nat) (fun n : nat =>
                       EnTree.bind
                         (trepeat n
                           (EnTree.bind (ExistsS A)
                                        (fun a' : A =>
                                           EnTree.bind (AssertS (pre a' /\ rdec a' (uncall_unary1Frame call)))
                                                       (fun _ : unit =>
                                                          CallS E Γ (unary1Frame A B)
                                                                (FrameCallOfArgs (unary1Frame A B) 0
                                                                                 (existT (fun _ : A => unit) a' tt))))))
                         (fun _ : unit =>
                            EnTree.bind (exists_spec B)
                                        (fun b : B =>
                                           EnTree.bind (AssertS (post (uncall_unary1Frame call) b))
                                                       (fun _ : unit => RetS b)))))) (fun b : B => RetS (call_unary1Frame call b)))
        (CallS E Γ (unary1Frame A B)
               (FrameCallOfArgs (unary1Frame A B) 0 (existT (fun _ : A => unit) a tt))))
     (total_spec_fix pre post rdec a).
Proof.
  intros E Γ A B H H0 pre post rdec a. setoid_rewrite interp_mrec_spec_inl at 1.
  rewrite tau_eutt. match goal with |- strict_refines (interp_mrec_spec ?b _) _ =>
                                      set b as body end.
  eapply padded_refines_interp_mrec_spec with (RPreInv := eq) (RPostInv := PostRelEq).
  - intros. subst. destruct d2.
    destruct n. 2 : destruct args as [ [] _].
    destruct args as [a' []]. cbn. cbn. eapply padded_refines_bind with (RR := eq).
    2 : { intros. apply padded_refines_ret. subst. constructor. }
    quantr. intros. quantl. auto. quantl. intros.
    quantr. exists a0. eapply padded_refines_bind with (RR := eq).
    + eapply padded_refines_monot; try apply strict_refines_refl; intros; subst.
      destruct x1; constructor; auto. destruct PR. destruct H2. constructor.
      destruct H2. constructor. auto.
    + intros. subst. quantl. intros. quantr. exists a1. quantl.
      intros. quantr. auto. apply padded_refines_ret. auto.
 - cbn. quantr. intros. (* lets get a better way to rewrite bind_bind *)
   eapply padded_refines_monot with (RPre1 := eq) (RPost1 := PostRelEq) (RR1 := eq); eauto.
   + intros. subst. destruct x1; constructor; auto.
   + intros. destruct e1; dependent destruction PR. dependent destruction H6.
     constructor. dependent destruction H6. constructor.
   + repeat apply padded_refines_bind_bind_l. quantl. eexists. eauto.
     apply padded_refines_ret_bind_l. apply padded_refines_bind_bind_l.
     eapply padded_refines_bind. apply strict_refines_refl.
     intros. subst. apply padded_refines_bind_bind_l.
     eapply padded_refines_bind. apply strict_refines_refl.
     intros [] [] _. apply padded_refines_bind_bind_l. 
     quantl. intros. quantr. exists a0. apply padded_refines_bind_bind_l.
     quantl. intros. quantr. auto. repeat apply padded_refines_ret_bind_l.
     apply padded_refines_ret. cbv. auto.
Qed.
   
Lemma total_spec_fix_refines_total_spec {E Γ A B} `{QuantType A} `{QuantType B}
           (pre : A -> Prop) (post : A -> B -> Prop) (rdec : A -> A -> Prop)
           (a : A) : 
  well_founded rdec ->
  strict_refines (total_spec_fix pre post rdec a) (@total_spec E Γ A B _ pre post a).
Proof.
  intros Hwf. revert a. apply well_founded_ind with (R := rdec). auto.
  intros x Hind. unfold total_spec_fix. unfold total_spec_fix_body. cbn.
  match goal with |- strict_refines (interp_mrec_spec ?b _) _ =>
                    set b as body end.
  quantr. intro. quantl. auto. quantl. intros n.
  induction n.
  - cbn. rewrite bind_ret_l. quantl. intros b. quantr. exists b.
    quantl. intros. quantr. auto. rewrite interp_mrec_spec_ret.
    apply padded_refines_ret. auto.
  - cbn. repeat rewrite bind_bind.
    quantl. intros a. rewrite bind_bind. quantl.
    intros [Hpre Hdec]. rewrite interp_mrec_spec_bind.
    specialize (Hind a Hdec). 
    match goal with |- padded_refines eq PostRelEq eq (EnTree.bind ?tf _ ) _ =>
                      assert (strict_refines tf (total_spec_fix pre post rdec a)) end.
    apply total_spec_fix_refines_total_spec_aux1.
    eapply padded_refines_weaken_r
           with (phi2 := EnTree.bind (total_spec pre post a)  (fun _  =>
              EnTree.bind (exists_spec B)
                (fun b : B => EnTree.bind (AssertS (post x b)) (fun _ : unit => RetS b))) )
    .
    { eapply padded_refines_bind; eauto. eapply padded_refines_weaken_l; eauto. } 
    clear - Hwf Hpre Hdec. cbn.
    apply padded_refines_bind_bind_l. quantl. auto.
    apply padded_refines_bind_bind_l. quantl. intros b. apply padded_refines_bind_bind_l.
    quantl. intros. rewrite bind_ret_l. quantl. intros bf.
    quantl. intros Hbf. quantr. exists bf. quantr. auto. apply padded_refines_ret.
    auto.
Qed.

Definition lift_ts_pre
  {frame1 : RecFrame} {A2 B2 : Type} (tsPre : A2 -> Prop)
  (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2))) :
  Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)) :=
  fun c1 c2 => exists a : A2, FrameCallOfArgs (unary1Frame A2 B2) 0 (existT _ a tt) = c2 /\ precond c1 (unary1Call a) /\ tsPre a.

Definition lift_ts_post:
  forall {frame1 : RecFrame} {A2 B2 : Type} (tsPost : A2 -> B2 -> Prop)
    (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2))),
    PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)).
  intros frame1 A2 B2 tsPost postcond.
  intros c1 c2 a b.
  specialize (postcond c1 c2).
  destruct c2. cbn in b. destruct n.
  cbn in b. destruct args. apply (tsPost x b /\ postcond a b).
  destruct args. destruct x.
Defined.
(*with some strategic lemmas this should be doable *)

Lemma spec_refines_total_spec_monot_aux1:
  forall (E1 E2 : EvType) (Γ1 Γ2 : FunStack) (frame1 : RecFrame) (A2 B2 : Type) (RPre : SpecPreRel E1 E2 Γ1 Γ2)
    (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2))) (tsPre : A2 -> Prop)
    (x0 : FrameCall frame1 +
            (fix FunStackE (E : Type) (Γ : FunStack) {struct Γ} : Type :=
               match Γ with
               | nil => (ErrorE + E)%type
               | frame :: Γ' => (FrameCall frame + FunStackE E Γ')%type
               end) E1 Γ1) (x1 : FrameCall (unary1Frame A2 B2) + FunStackE E2 Γ2),
    pushTSPreRel tsPre precond RPre x0 x1 -> HeterogeneousRelations.sum_rel (lift_ts_pre tsPre precond) RPre x0 x1.
Proof.
  intros E1 E2 Γ1 Γ2 frame1 A2 B2 RPre preEq pre.
  intros x c PR. destruct x.
  - cbn in PR. destruct c.
    + destruct f0. destruct n. destruct args. 2 :destruct PR. 
      cbn. constructor. exists x. destruct l. destruct PR. auto.
    + destruct PR.
  - destruct c; try (destruct PR; fail). red in PR. constructor. auto.
Qed.

Lemma spec_refines_total_spec_monot_aux2:
  forall (E1 E2 : EvType) (Γ1 Γ2 : FunStack) (frame1 : RecFrame) (A2 B2 : Type) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
    (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2))) (tsPost : A2 -> B2 -> Prop)
    (e1 : FrameCall frame1 +
            (fix FunStackE (E : Type) (Γ : FunStack) {struct Γ} : Type :=
               match Γ with
               | nil => (ErrorE + E)%type
               | frame :: Γ' => (FrameCall frame + FunStackE E Γ')%type
               end) E1 Γ1) (e2 : FrameCall (unary1Frame A2 B2) + FunStackE E2 Γ2) (x0 : encodes e1) (x1 : encodes e2),
    SumPostRel (lift_ts_post tsPost postcond) RPost e1 e2 x0 x1 -> pushTSPostRel tsPost postcond RPost e1 e2 x0 x1.
Proof.
  intros E1 E2 Γ1 Γ2 frame1 A2 B2 RPost postcond tsPost.
  intros c1 c2 a b Hab.
  destruct c1.
  - destruct Hab; auto.
    destruct e2. cbn in args. destruct n. cbn in args.
    2 : destruct args as [ [] _ ].
    destruct args as [ a2 [] ]. auto.
  - cbn in *.  destruct c2; auto.
    + dependent destruction Hab.
    + dependent destruction Hab. auto.
Qed.

(*
Lemma spec_refines_total_spec_post_aux {E1 Γ1 E2 Γ2 A B} `{EncodingType E1} `{EncodingType E2} `{QuantType A} `{QuantType B}
           (pre : A -> Prop) (post : A -> B -> Prop) (rdec : A -> A -> Prop) (phi1) : 
. *)

Axiom inj_FrameCallOfArgs : forall frame n x y, FrameCallOfArgs frame n x = FrameCallOfArgs frame n y ->
                                        x = y.

Lemma spec_refines_total_spec (E1 E2 : EvType) Γ1 Γ2 frame1
      A2 B2 `{QuantType A2} `{QuantType B2}
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (call1 : FrameCall frame1) (a2 : A2)
      (RR : Rel (FrameCallRet frame1 call1) B2)
      (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
      (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
      (tsPre : A2 -> Prop) (tsPost : A2 -> B2 -> Prop)
      (rdec : A2 -> A2 -> Prop) :
  well_founded rdec ->
  tsPre a2 -> precond call1 (unary1Call a2) ->
  (forall r1 r2, tsPost a2 r2 -> postcond call1 (unary1Call a2) r1 r2 -> RR r1 r2) ->
  (forall call1' a2',
      tsPre a2' -> precond call1' (unary1Call a2') ->
      spec_refines (pushTSPreRel tsPre precond RPre)
                   (pushTSPostRel tsPost postcond RPost)
                   (pushTSRR tsPost postcond call1' a2')
                   (applyFrameTuple _ _ _ bodies1 call1')
                   (total_spec_fix_body tsPre tsPost rdec a2')) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1)
               (total_spec tsPre tsPost a2).
Proof.
  intros Hwf Ha2 Hca HPost HPost'. intros.
  eapply total_spec_fix_refines_total_spec in Hwf as Hstrict. Unshelve. all : auto.
  eapply padded_refines_weaken_l; eauto.
  eapply padded_refines_interp_mrec_spec with (RPreInv := lift_ts_pre tsPre precond)
                                              (RPostInv := lift_ts_post tsPost postcond). Unshelve.
  - clear Hca Ha2 Hstrict . rename a2 into a0. intros c1 c2 Hpre. destruct c2. destruct n.
    2 : { destruct args as [ [] _]. }
    cbn in args. destruct args as [a2 [] ]. simpl. setoid_rewrite bind_ret_r.
    idtac. red in Hpre. destruct Hpre as [a2' [Heq [H1 H2] ]].
    assert (a2 = a2'). apply inj_FrameCallOfArgs in Heq. dependent destruction Heq.
    auto.
    subst.
    eapply padded_refines_monot; try apply HPost'; eauto.
    + apply spec_refines_total_spec_monot_aux1.
    + apply spec_refines_total_spec_monot_aux2.
  - eapply padded_refines_monot; try eapply HPost'; eauto.
    + apply spec_refines_total_spec_monot_aux1.
    + apply spec_refines_total_spec_monot_aux2.
    + intros. destruct PR. auto.
Qed.


(***
 *** Hints for automation
 ***)

Create HintDb refines.
Create HintDb prepostcond.

(* If nothing else works, shelve the current refinement goal *)
#[global] Hint Extern 999 (spec_refines _ _ _ _ _) => shelve : refines.


(** IntroArg Definition and Hints **)

(* Classes of variables and their associated naming conventions *)
Inductive ArgName := Any | RetAny | Hyp | Call | Exists | Forall | If | Match.
Ltac argName n :=
  match n with
  | Any      => fresh "a"
  | RetAny   => fresh "r"
  | Hyp      => fresh "H"
  | Call     => fresh "call"
  | Exists   => fresh "e_exists"
  | Forall   => fresh "e_forall"
  | If       => fresh "e_if"
  | Match    => fresh "e_match"
  end.

(* IntroArg marks a goal which introduces a variable. This is used to control
   how variables are introduced, allowing them to be eliminated and to give them
   meaningful names using argName above *)
Polymorphic Definition IntroArg (n : ArgName) A (goal : A -> Type) :=
  forall a, goal a.

#[global] Hint Opaque IntroArg : refines prepostcond.

Polymorphic Lemma IntroArg_fold n A goal : IntroArg n A goal -> forall a, goal a.
Proof. intros H a; exact (H a). Qed.

(* Polymorphic Lemma IntroArg_unfold n A (goal : A -> Prop) : (forall a, goal a) -> IntroArg n A goal. *)
(* Proof. unfold IntroArg; intro H; exact H. Qed. *)

Ltac IntroArg_intro e := intro e.

Ltac IntroArg_forget := let e := fresh in intro e; clear e.

Polymorphic Definition IntroArg_beta n A (f : A -> Type) x goal :
  IntroArg n (f x) goal ->
  IntroArg n ((fun x' => f x') x) goal := fun f x => f x.

Polymorphic Definition IntroArg_prod n A B (goal : A * B -> Type) :
  IntroArg n A (fun a => IntroArg n B (fun b => goal (a , b))) ->
  IntroArg n _ goal := fun H '(a, b) => H a b.

Polymorphic Definition IntroArg_sigT n A P (goal : sigT P -> Type) :
  IntroArg n A (fun a => IntroArg n (P a) (fun p => goal (existT _ a p))) ->
  IntroArg n _ goal := fun H '(a ; p) => H a p.

Polymorphic Definition IntroArg_unit n (goal : unit -> Type) :
  goal tt -> IntroArg n _ goal := fun H 'tt => H.

Polymorphic Lemma IntroArg_and n P Q (goal : P /\ Q -> Prop)
  : IntroArg n P (fun p => IntroArg n Q (fun q => goal (conj p q))) ->
    IntroArg n _ goal.
Proof. intros H [ p q ]; apply H. Qed.

Polymorphic Lemma IntroArg_true n (goal : True -> Prop) : goal I -> IntroArg n _ goal.
Proof. intros H []; eauto. Qed.

Polymorphic Lemma IntroArg_false n (goal : False -> Prop) : IntroArg n _ goal.
Proof. intros []. Qed.

Polymorphic Lemma IntroArg_eq_sigT_const n A B (a a' : A) (b b' : B) (goal : Prop)
  : IntroArg n (a = a') (fun _ => IntroArg n (b = b') (fun _ => goal)) ->
    IntroArg n (existT _ a b = existT _ a' b') (fun _ => goal).
Proof. intros H eq; apply H; injection eq; eauto. Qed.

Polymorphic Lemma IntroArg_eq_dep1_const n A B (a : A) (b b' : B a) (goal : Prop)
  : IntroArg n (b = b') (fun _ => goal) ->
    IntroArg n (eq_dep1 A B a b a b') (fun _ => goal).
Proof.
  intro H. unfold IntroArg in *. intro Heqdep. apply H.
  apply eq_dep1_dep in Heqdep. apply eq_dep_eq. auto.
Qed.

Polymorphic Lemma IntroArg_eqPostRel n E Γ e a1 a2 (goal : _ -> Prop) :
  IntroArg n (a1 = a2) (fun pf => goal (eq_dep1_intro _ _ _ _ _ _ (eq_refl e) pf)) ->
  IntroArg n (@eqPostRel E Γ e e a1 a2) goal.
Proof.
  intros H H0; dependent destruction H0.
  apply H.
Qed.

Polymorphic Lemma IntroArg_pushPreRel_inl n E1 E2 Γ1 Γ2 frame1 frame2
            (precond : Rel (FrameCall frame1) (FrameCall frame2))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2) e1 e2 (goal : _ -> Prop) :
  IntroArg n (precond e1 e2) goal ->
  IntroArg n (@pushPreRel E1 E2 Γ1 Γ2 frame1 frame2
                          precond RPre (inl e1) (inl e2)) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushPreRel_inr n E1 E2 Γ1 Γ2 frame1 frame2
            (precond : Rel (FrameCall frame1) (FrameCall frame2))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2) e1 e2 (goal : _ -> Prop) :
  IntroArg n (RPre e1 e2) goal ->
  IntroArg n (@pushPreRel E1 E2 Γ1 Γ2 frame1 frame2
                          precond RPre (inr e1) (inr e2)) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushPostRel_inl n E1 E2 Γ1 Γ2 frame1 frame2
            (postcond : PostRel (FrameCall frame1) (FrameCall frame2))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            (call1 : FrameCall frame1) (call2 : FrameCall frame2)
            r1 r2 (goal : _ -> Prop) :
  IntroArg n (postcond _ _ r1 r2) goal ->
  IntroArg n (@pushPostRel E1 E2 Γ1 Γ2 frame1 frame2
                           postcond RPost (inl call1) (inl call2) r1 r2) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushPostRel_inr n E1 E2 Γ1 Γ2 frame1 frame2
            (postcond : PostRel (FrameCall frame1) (FrameCall frame2))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            e1 e2 r1 r2 (goal : _ -> Prop) :
  IntroArg n (RPost _ _ r1 r2) goal ->
  IntroArg n (@pushPostRel E1 E2 Γ1 Γ2 frame1 frame2
                           postcond RPost (inr e1) (inr e2) r1 r2) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSPreRel_inl n E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPre : A2 -> Prop)
            (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2)
            args1 a2 (goal : _ -> Prop) :
  IntroArg n (tsPre a2 /\ precond args1 (unary1Call a2)) goal ->
  IntroArg n (@pushTSPreRel E1 E2 Γ1 Γ2 frame1 A2 B2
                            tsPre precond RPre (inl args1)
                            (inl (mkFrameCall (unary1Frame A2 B2) 0 a2))) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSPreRel_inr n E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPre : A2 -> Prop)
            (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2)
            e1 e2 (goal : _ -> Prop) :
  IntroArg n (RPre e1 e2) goal ->
  IntroArg n (@pushTSPreRel E1 E2 Γ1 Γ2 frame1 A2 B2
                            tsPre precond RPre (inr e1) (inr e2)) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSPostRel_inl n E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPost : A2 -> B2 -> Prop)
            (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            args1 a2 r1 b2 (goal : _ -> Prop) :
  IntroArg n (tsPost a2 b2 /\ postcond args1 (unary1Call a2) r1 b2) goal ->
  IntroArg n (@pushTSPostRel E1 E2 Γ1 Γ2 frame1 A2 B2
                             tsPost postcond RPost (inl args1)
                             (inl (mkFrameCall (unary1Frame A2 B2) 0 a2)) r1 b2) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSPostRel_inr n E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPost : A2 -> B2 -> Prop)
            (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            e1 e2 r1 r2 (goal : _ -> Prop) :
  IntroArg n (RPost e1 e2 r1 r2) goal ->
  IntroArg n (@pushTSPostRel E1 E2 Γ1 Γ2 frame1 A2 B2
                             tsPost postcond RPost (inr e1) (inr e2) r1 r2) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSRR n frame1 A2 B2
            (tsPost : A2 -> B2 -> Prop)
            (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            call1 a2 r1 r2 (goal : _ -> Prop) :
  IntroArg n (tsPost a2 r2 /\ postcond call1 (unary1Call a2) r1 r2) goal ->
  IntroArg n (@pushTSRR frame1 A2 B2 tsPost postcond call1 a2 r1 r2) goal.
Proof. intro H. apply H. Qed.

Polymorphic Definition IntroArg_FrameCall n frame goal :
  forRange (length frame)
           (fun i goal' => IntroArg Any (LRTInput (nthLRT frame i))
                                    (fun args => goal (lrtApply _ _ (mkFrameCall frame i) args))
                             -> goal')
           (IntroArg n (FrameCall frame) goal) :=
  @recFrameCall frame goal.

Polymorphic Definition IntroArg_LRTInput_Ret {n R goal} :
  goal tt -> IntroArg n (LRTInput (LRT_Ret R)) goal :=
  fun H 'tt => H.

Polymorphic Definition IntroArg_LRTInput_Fun {n A lrt goal} :
  IntroArg n A (fun a => IntroArg n (LRTInput (lrt a)) (fun args => goal (existT _ a args))) ->
  IntroArg n (LRTInput (LRT_Fun A lrt)) goal :=
  fun H '(existT _ x l) => H x l.

Ltac IntroArg_intro_dependent_destruction n :=
  let e := argName n in
    IntroArg_intro e; dependent destruction e.

Ltac IntroArg_base_tac n A g :=
  lazymatch A with
  | (fun _ => _) _ => simple apply IntroArg_beta
  | prod _ _ => simple apply IntroArg_prod
  | sigT _ => simple apply IntroArg_sigT
  | unit => simple apply IntroArg_unit
  | _ /\ _ => simple apply IntroArg_and
  | True => simple apply IntroArg_true
  | False => simple apply IntroArg_false
  | existT _ _ _ = existT _ _ _ => simple apply IntroArg_eq_sigT_const
  | eqPreRel (existT _ _ _) (existT _ _ _) => simple apply IntroArg_eq_sigT_const
  | eq_dep1 _ _ _ _ _ _ => simple apply IntroArg_eq_dep1_const
  | @pushPreRel _ _ _ _ _ _ _ _ (inl _) (inl _) =>
    simple apply IntroArg_pushPreRel_inl
  | @pushPreRel _ _ _ _ _ _ _ _ (inr _) (inr _) =>
    simple apply IntroArg_pushPreRel_inr
  | @pushPostRel _ _ _ _ _ _ _ _ (inl _) (inl _) _ _ =>
    simple apply IntroArg_pushPostRel_inl
  | @pushPostRel _ _ _ _ _ _ _ _ (inr _) (inr _) _ _ =>
    simple apply IntroArg_pushPostRel_inr
  | @pushTSPreRel _ _ _ _ _ _ _ _ _ _ (inl _) (inl _) =>
    simple apply IntroArg_pushTSPreRel_inl
  | @pushTSPreRel _ _ _ _ _ _ _ _ _ _ (inr _) (inr _) =>
    simple apply IntroArg_pushTSPreRel_inr
  | @pushTSPostRel _ _ _ _ _ _ _ _ _ _ (inl _) (inl _) _ _ =>
    simple apply IntroArg_pushTSPostRel_inl
  | @pushTSPostRel _ _ _ _ _ _ _ _ _ _ (inr _) (inr _) _ _ =>
    simple apply IntroArg_pushTSPostRel_inr
  | @pushTSRR _ _ _ _ _ _ _ _ _ =>
    simple apply IntroArg_pushTSRR
  | eqPostRel _ _ _ _ _ _ => apply IntroArg_eqPostRel
  | true  = true  => IntroArg_intro_dependent_destruction n
  | false = false => IntroArg_intro_dependent_destruction n
  | true  = false => IntroArg_intro_dependent_destruction n
  | false = true  => IntroArg_intro_dependent_destruction n
  end.

#[global] Hint Extern 101 (IntroArg ?n ?A ?g) =>
  IntroArg_base_tac n A g : refines prepostcond.

#[global] Hint Extern 101 (IntroArg ?n (FrameCall ?frame) _) =>
  apply (@IntroArg_FrameCall n frame) : refines.
#[global] Hint Extern 101 (IntroArg ?n (LRTInput _) _) =>
  apply IntroArg_LRTInput_Fun || apply IntroArg_LRTInput_Ret;
  simpl lrtApply; simpl applyFrameTuple : refines prepostcond.
  
#[global] Hint Extern 102 (IntroArg ?n (@eq bool _ _) _) =>
  let e := argName n in IntroArg_intro e; rewrite e in * : refines prepostcond.

#[global] Hint Extern 199 (IntroArg ?n (?x = ?y) _) =>
  let e := argName n in IntroArg_intro e;
    try first [ is_var x; subst x | is_var y; subst y ] : refines.

#[global] Hint Extern 999 (IntroArg ?n _ _) =>
  let e := argName n in IntroArg_intro e : refines prepostcond.


(** Hints for Relation Goals **)

(* RelGoal marks a relation goal *)
Definition RelGoal (goal : Prop) := goal.

#[global] Hint Opaque RelGoal : refines.

Polymorphic Lemma RelGoal_fold goal : RelGoal goal -> goal.
Proof. eauto. Qed.

(* If nothing else works for a RelGoal, try reflexivity and then shelve it *)
#[global] Hint Extern 999 (RelGoal _) =>
  unfold RelGoal; cbn;
  unfold resum_ret, ReSumRet_FrameCall_FunStackE;
  (reflexivity || shelve) : refines.

#[global] Lemma RelGoal_and P Q :
  RelGoal P -> RelGoal Q -> RelGoal (P /\ Q).
Proof. split; eauto. Qed.

#[global] Hint Extern 101 (RelGoal (_ /\ _)) =>
  simple apply RelGoal_and : refines.

#[global] Lemma RelGoal_beta A (f : A -> Prop) x :
  RelGoal (f x) -> RelGoal ((fun x' => f x') x).
Proof. eauto. Qed.

#[global] Hint Extern 101 (RelGoal ((fun _ => _) _)) =>
  simple apply RelGoal_beta : refines.

Lemma RelGoal_eqPreRel_refl {E Γ e} :
  RelGoal (@eqPreRel E Γ e e).
Proof. constructor. Qed.

#[global] Hint Extern 101 (RelGoal (eqPreRel _ _ _ _)) =>
  apply RelGoal_eqPreRel_refl : refines.

Lemma RelGoal_eq_dep1_refl {U P p x} :
  RelGoal (eq_dep1 U P p x p x).
Proof. unshelve econstructor; eauto. Qed.

#[global] Hint Extern 101 (RelGoal (eq_dep1 _ _ _ _ _ _)) =>
  apply RelGoal_eq_dep1_refl : refines.

Polymorphic Lemma RelGoal_pushPreRel_inl E1 E2 Γ1 Γ2 frame1 frame2
            (precond : Rel (FrameCall frame1) (FrameCall frame2))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2) e1 e2 :
  RelGoal (precond e1 e2) ->
  RelGoal (@pushPreRel E1 E2 Γ1 Γ2 frame1 frame2 precond RPre (inl e1) (inl e2)).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushPreRel _ _ _ _ _ _ _ _ (inl _) (inl _))) =>
  apply RelGoal_pushPreRel_inl : refines.


Polymorphic Lemma RelGoal_pushPreRel_inr E1 E2 Γ1 Γ2 frame1 frame2
            (precond : Rel (FrameCall frame1) (FrameCall frame2))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2) e1 e2 :
  RelGoal (RPre e1 e2) ->
  RelGoal (@pushPreRel E1 E2 Γ1 Γ2 frame1 frame2 precond RPre (inr e1) (inr e2)).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushPreRel _ _ _ _ _ _ _ _ (inr _) (inr _))) =>
  apply RelGoal_pushPreRel_inr : refines.


Polymorphic Lemma RelGoal_pushPostRel_inl E1 E2 Γ1 Γ2 frame1 frame2
            (postcond : PostRel (FrameCall frame1) (FrameCall frame2))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            (call1 : FrameCall frame1) (call2 : FrameCall frame2)
            r1 r2 :
  RelGoal (postcond _ _ r1 r2) ->
  RelGoal (@pushPostRel E1 E2 Γ1 Γ2 frame1 frame2
                           postcond RPost (inl call1) (inl call2) r1 r2).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushPostRel _ _ _ _ _ _ _ _ (inl _) (inl _))) =>
  apply RelGoal_pushPostRel_inl : refines.


Polymorphic Lemma RelGoal_pushPostRel_inr E1 E2 Γ1 Γ2 frame1 frame2
            (postcond : PostRel (FrameCall frame1) (FrameCall frame2))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            e1 e2 r1 r2 :
  RelGoal (RPost _ _ r1 r2) ->
  RelGoal (@pushPostRel E1 E2 Γ1 Γ2 frame1 frame2
                           postcond RPost (inr e1) (inr e2) r1 r2).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushPostRel _ _ _ _ _ _ _ _ (inr _) (inr _))) =>
  apply RelGoal_pushPostRel_inr : refines.


Polymorphic Lemma RelGoal_pushTSPreRel_inl E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPre : A2 -> Prop)
            (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2)
            args1 a2 :
  RelGoal (tsPre a2 /\ precond args1 (unary1Call a2)) ->
  RelGoal (@pushTSPreRel E1 E2 Γ1 Γ2 frame1 A2 B2
                            tsPre precond RPre (inl args1)
                            (inl (mkFrameCall (unary1Frame A2 B2) 0 a2))).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushTSPreRel _ _ _ _ _ _ _ _ _ _ (inl _) (inl _))) =>
  apply RelGoal_pushTSPreRel_inl : refines.

Polymorphic Lemma RelGoal_pushTSPreRel_inr E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPre : A2 -> Prop)
            (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2)
            e1 e2 :
  RelGoal (RPre e1 e2) ->
  RelGoal (@pushTSPreRel E1 E2 Γ1 Γ2 frame1 A2 B2
                            tsPre precond RPre (inr e1) (inr e2)).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushTSPreRel _ _ _ _ _ _ _ _ _ _ (inr _) (inr _))) =>
  apply RelGoal_pushTSPreRel_inr : refines.


Polymorphic Lemma RelGoal_pushTSPostRel_inl E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPost : A2 -> B2 -> Prop)
            (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            args1 a2 r1 b2 :
  RelGoal (tsPost a2 b2 /\ postcond args1 (unary1Call a2) r1 b2) ->
  RelGoal (@pushTSPostRel E1 E2 Γ1 Γ2 frame1 A2 B2
                             tsPost postcond RPost (inl args1)
                             (inl (mkFrameCall (unary1Frame A2 B2) 0 a2)) r1 b2).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushTSPostRel _ _ _ _ _ _ _ _ _ _ (inl _) (inl _))) =>
  apply RelGoal_pushTSPostRel_inl : refines.


Polymorphic Lemma RelGoal_pushTSPostRel_inr E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPost : A2 -> B2 -> Prop)
            (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            e1 e2 r1 r2 :
  RelGoal (RPost e1 e2 r1 r2) ->
  RelGoal (@pushTSPostRel E1 E2 Γ1 Γ2 frame1 A2 B2
                             tsPost postcond RPost (inr e1) (inr e2) r1 r2).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushTSPostRel _ _ _ _ _ _ _ _ _ _ (inr _) (inr _))) =>
  apply RelGoal_pushTSPostRel_inr : refines.


Polymorphic Lemma RelGoal_pushTSRR frame1 A2 B2
            (tsPost : A2 -> B2 -> Prop)
            (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            call1 a2 r1 r2 :
  RelGoal (tsPost a2 r2 /\ postcond call1 (unary1Call a2) r1 r2) ->
  RelGoal (@pushTSRR frame1 A2 B2 tsPost postcond call1 a2 r1 r2).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal (@pushTSRR _ _ _ _ _ _ _ _ _)) =>
  apply RelGoal_pushTSRR : refines.


(** Refinement hints using IntroArg and RelGoal **)

(* RetS |= RetS *)
Polymorphic Definition spec_refines_ret_IntroArg E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR r1 r2 :
  (RelGoal (RR r1 r2 : Prop)) ->
  @spec_refines E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR (RetS r1) (RetS r2) :=
  spec_refines_ret E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR r1 r2.

#[global] Hint Extern 102 (spec_refines _ _ _ (RetS _) (RetS _)) =>
  apply spec_refines_ret_IntroArg : refines.


(* Monad laws *)

#[global]
Hint Extern 101 (spec_refines _ _ _ _ (RetS _ >>= _)) =>
  simple apply spec_refines_ret_bind_r : refines.
#[global]
Hint Extern 101 (spec_refines _ _ _ (RetS _ >>= _) _) =>
  simple apply spec_refines_ret_bind_l : refines.

#[global]
Hint Extern 101 (spec_refines _ _ _ _ ((_ >>= _) >>= _)) =>
  simple apply spec_refines_bind_bind_r : refines.
#[global]
Hint Extern 101 (spec_refines _ _ _ ((_ >>= _) >>= _) _) =>
  simple apply spec_refines_bind_bind_l : refines.


(* Trigger |= Trigger *)

Definition spec_refines_trigger_bind_IntroArg (E1 E2 : EvType) Γ1 Γ2 R1 R2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      RR (e1 : E1) (e2 : E2)
      (k1 : encodes e1 -> SpecM E1 Γ1 R1)
      (k2 : encodes e2 -> SpecM E2 Γ2 R2) :
  RelGoal (RPre (resum e1) (resum e2)) ->
  (IntroArg Any _ (fun a =>
     IntroArg Any _ (fun b =>
       IntroArg Hyp (RPost (resum e1) (resum e2) a b) (fun _ =>
         spec_refines RPre RPost RR (k1 (resum_ret e1 a)) (k2 (resum_ret e2 b)))))) ->
  spec_refines RPre RPost RR (TriggerS e1 >>= k1) (TriggerS e2 >>= k2) :=
  spec_refines_trigger_bind E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR e1 e2 k1 k2.

#[global]
Hint Extern 102 (spec_refines _ _ _ (TriggerS _ >>= _) (TriggerS _ >>= _)) =>
  apply spec_refines_trigger_bind_IntroArg : refines.


(* Rules for quantifiers *)

Definition spec_refines_exists_l_IntroArg E1 E2 Γ1 Γ2 R1 R2 A `{QuantType A}
      RPre RPost RR (phi : SpecM E2 Γ2 R2) (kphi : A -> SpecM E1 Γ1 R1) :
  (IntroArg Exists A (fun a =>spec_refines RPre RPost RR (kphi a) phi)) ->
  spec_refines RPre RPost RR (ExistsS A >>= kphi) phi :=
  spec_refines_exists_l E1 E2 Γ1 Γ2 R1 R2 A RPre RPost RR phi kphi.

Definition spec_refines_forall_r_IntroArg E1 E2 Γ1 Γ2 R1 R2 A `{QuantType A}
      RPre RPost RR (phi : SpecM E1 Γ1 R1) (kphi : A -> SpecM E2 Γ2 R2) :
  (IntroArg Forall A (fun a => spec_refines RPre RPost RR phi (kphi a))) ->
  spec_refines RPre RPost RR phi (ForallS A >>= kphi) :=
  spec_refines_forall_r E1 E2 Γ1 Γ2 R1 R2 A RPre RPost RR phi kphi.

#[global] Hint Extern 101 (spec_refines _ _ _ _ (ForallS _ >>= _)) =>
  simple apply spec_refines_forall_r_IntroArg : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (ExistsS _ >>= _) _) =>
  simple apply spec_refines_exists_l_IntroArg : refines.

#[global] Hint Extern 102 (spec_refines _ _ _ _ (ExistsS _ >>= _)) =>
  simple eapply spec_refines_exists_r : refines.
#[global] Hint Extern 102 (spec_refines _ _ _ (ForallS _ >>= _) _) =>
  simple eapply spec_refines_forall_l : refines.


(* Rules for assume and assert *)

Definition spec_refines_assert_l_IntroArg E1 E2 Γ1 Γ2 R1 R2 (P:Prop)
      RPre RPost RR (phi : SpecM E2 Γ2 R2) (kphi : unit -> SpecM E1 Γ1 R1) :
  (IntroArg Hyp P (fun _ => spec_refines RPre RPost RR (kphi tt) phi)) ->
  spec_refines RPre RPost RR (AssertS P >>= kphi) phi :=
  spec_refines_assert_l E1 E2 Γ1 Γ2 R1 R2 P RPre RPost RR phi kphi.

Definition spec_refines_assume_r_IntroArg E1 E2 Γ1 Γ2 R1 R2 (P:Prop)
      RPre RPost RR (phi : SpecM E1 Γ1 R1) (kphi : unit -> SpecM E2 Γ2 R2) :
  (IntroArg Hyp P (fun _ => spec_refines RPre RPost RR phi (kphi tt))) ->
  spec_refines RPre RPost RR phi (AssumeS P >>= kphi) :=
  spec_refines_assume_r E1 E2 Γ1 Γ2 R1 R2 P RPre RPost RR phi kphi.

Definition spec_refines_assert_r_IntroArg E1 E2 Γ1 Γ2 R1 R2 (P:Prop)
      RPre RPost RR (phi : SpecM E1 Γ1 R1) (kphi : unit -> SpecM E2 Γ2 R2) :
  RelGoal P -> spec_refines RPre RPost RR phi (kphi tt) ->
  spec_refines RPre RPost RR phi (AssertS P >>= kphi) :=
  spec_refines_assert_r E1 E2 Γ1 Γ2 R1 R2 P RPre RPost RR phi kphi.

Definition spec_refines_assume_l_IntroArg E1 E2 Γ1 Γ2 R1 R2 (P:Prop)
      RPre RPost RR (phi : SpecM E2 Γ2 R2) (kphi : unit -> SpecM E1 Γ1 R1) :
      RelGoal P -> spec_refines RPre RPost RR (kphi tt) phi ->
  spec_refines RPre RPost RR (AssumeS P >>= kphi) phi :=
  spec_refines_assume_l E1 E2 Γ1 Γ2 R1 R2 P RPre RPost RR phi kphi.

#[global] Hint Extern 101 (spec_refines _ _ _ _ (AssumeS _ >>= _)) =>
  simple apply spec_refines_assume_r_IntroArg : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (AssertS _ >>= _) _) =>
  simple apply spec_refines_assert_l_IntroArg : refines.

#[global] Hint Extern 102 (spec_refines _ _ _ _ (AssertS _ >>= _)) =>
  simple eapply spec_refines_assert_r_IntroArg : refines.
#[global] Hint Extern 102 (spec_refines _ _ _ (AssumeS _ >>= _) _) =>
  simple eapply spec_refines_assume_l_IntroArg : refines.


(* Rules for if-then-else *)

Definition spec_refines_if_r_IntroArg E1 E2 Γ1 Γ2 R1 R2
           RPre RPost RR (t1 : SpecM E1 Γ1 R1) (t2 t3 : SpecM E2 Γ2 R2) b :
  (IntroArg If (b = true) (fun _ => spec_refines RPre RPost RR t1 t2)) ->
  (IntroArg If (b = false) (fun _ => spec_refines RPre RPost RR t1 t3)) ->
  spec_refines RPre RPost RR t1 (if b then t2 else t3) :=
  spec_refines_if_r E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR t1 t2 t3 b.

Definition spec_refines_if_l_IntroArg E1 E2 Γ1 Γ2 R1 R2
           RPre RPost RR (t1 t2 : SpecM E1 Γ1 R1) (t3 : SpecM E2 Γ2 R2) b :
  (IntroArg If (b = true) (fun _ => spec_refines RPre RPost RR t1 t3)) ->
  (IntroArg If (b = false) (fun _ => spec_refines RPre RPost RR t2 t3)) ->
  spec_refines RPre RPost RR (if b then t1 else t2) t3 :=
  spec_refines_if_l E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR t1 t2 t3 b.

#[global] Hint Extern 101 (spec_refines _ _ _ _ (if _ then _ else _)) =>
  apply spec_refines_if_r_IntroArg : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (if _ then _ else _) _) =>
  apply spec_refines_if_l_IntroArg : refines.

#[global] Hint Extern 101 (spec_refines _ _ _ _ ((if _ then _ else _) >>= _)) =>
  apply spec_refines_if_bind_r : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ ((if _ then _ else _) >>= _) _) =>
  apply spec_refines_if_bind_l : refines.


(* Rules for pattern-matching on lists *)

Definition spec_refines_match_list_r_IntroArg E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A
           (t1 : SpecM E1 Γ1 R1) (t2 : A -> list A -> SpecM E2 Γ2 R2)
           (t3 : SpecM E2 Γ2 R2) xs :
  (IntroArg Any A (fun x =>
     IntroArg Any (list A) (fun xs' =>
       IntroArg Match (xs = x :: xs') (fun _ =>
         spec_refines RPre RPost RR t1 (t2 x xs'))))) ->
  (IntroArg Match (xs = nil) (fun _ => spec_refines RPre RPost RR t1 t3)) ->
  spec_refines RPre RPost RR t1 (match xs with
                                 | x :: xs' => t2 x xs' | nil => t3 end) :=
  spec_refines_match_list_r E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A t1 t2 t3 xs.

Definition spec_refines_match_list_l_IntroArg E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A
           (t3 : SpecM E2 Γ2 R2)
           (t1 : A -> list A -> SpecM E1 Γ1 R1) (t2 : SpecM E1 Γ1 R1) xs :
  (IntroArg Any A (fun x =>
     IntroArg Any (list A) (fun xs' =>
       IntroArg Match (xs = x :: xs') (fun _ =>
         spec_refines RPre RPost RR (t1 x xs') t3)))) ->
  (IntroArg Match (xs = nil) (fun _ => spec_refines RPre RPost RR t2 t3)) ->
  spec_refines RPre RPost RR (match xs with
                              | x :: xs' => t1 x xs' | nil => t2 end) t3 :=
  spec_refines_match_list_l E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A t3 t1 t2 xs.

#[global]
Hint Extern 101 (spec_refines _ _ _ _ (match _ with | _ :: _ => _ | nil => _ end)) =>
  apply spec_refines_match_list_r_IntroArg : refines.
#[global]
Hint Extern 101 (spec_refines _ _ _ (match _ with | _ :: _ => _ | nil => _ end) _) =>
  apply spec_refines_match_list_l_IntroArg : refines.

#[global]
Hint Extern 101 (spec_refines _ _ _ _ ((match _ with | _ :: _ => _ | nil => _ end) >>= _)) =>
  apply spec_refines_match_list_bind_r : refines.
#[global]
Hint Extern 101 (spec_refines _ _ _ ((match _ with | _ :: _ => _ | nil => _ end) >>= _) _) =>
  apply spec_refines_match_list_bind_l : refines.


(* Rules for pattern-matching on pairs *)

Definition spec_refines_match_pair_r_IntroArg E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A B
           (t1 : SpecM E1 Γ1 R1) (t2 : A -> B -> SpecM E2 Γ2 R2) pr :
  (IntroArg Any A (fun x =>
     IntroArg Any B (fun y =>
       IntroArg Match (pr = (x, y)) (fun _ =>
         spec_refines RPre RPost RR t1 (t2 x y))))) ->
  spec_refines RPre RPost RR t1 (match pr with | (x,y) => t2 x y end) :=
  spec_refines_match_pair_r E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A B t1 t2 pr.

Definition spec_refines_match_pair_l_IntroArg E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A B
           (t1 : A -> B -> SpecM E1 Γ1 R1) (t2 : SpecM E2 Γ2 R2) pr :
  (IntroArg Any A (fun x =>
     IntroArg Any B (fun y =>
       IntroArg Match (pr = (x, y)) (fun _ =>
         spec_refines RPre RPost RR (t1 x y) t2)))) ->
  spec_refines RPre RPost RR (match pr with | (x,y) => t1 x y end) t2 :=
  spec_refines_match_pair_l E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A B t1 t2 pr.

#[global]
Hint Extern 101 (spec_refines _ _ _ _ (match _ with | (_,_) => _ end)) =>
  apply spec_refines_match_pair_r_IntroArg : refines.
#[global]
Hint Extern 101 (spec_refines _ _ _ (match _ with | (_,_) => _ end) _) =>
  apply spec_refines_match_pair_l_IntroArg : refines.

#[global]
Hint Extern 101 (spec_refines _ _ _ _ ((match _ with | (_,_) => _ end) >>= _)) =>
  apply spec_refines_match_pair_bind_r : refines.
#[global]
Hint Extern 101 (spec_refines _ _ _ ((match _ with | (_,_) => _ end) >>= _) _) =>
  apply spec_refines_match_pair_bind_l : refines.


(** * Rules for liftStackS  *)

Lemma liftStackS_ret_bind_l (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) A1 a k1 t2 :
  spec_refines RPre RPost RR (k1 a) t2 ->
  spec_refines RPre RPost RR (liftStackS A1 (RetS a) >>= k1) t2.
Admitted.

#[global] Hint Extern 101 (spec_refines _ _ _ (liftStackS _ (RetS _) >>= _) _) =>
  simple apply liftStackS_ret_bind_l : refines.


(** * Refinement Hints About Recursion *)

Definition WellFoundedRelation A := sig (@well_founded A).
Definition PreAndPostConditions frame1 frame2 : Type :=
  Rel (FrameCall frame1) (FrameCall frame2) *
  PostRel (FrameCall frame1) (FrameCall frame2).
Polymorphic Definition from_user {A} {x : A} := x.

Definition wfRelOf {A} :
  WellFoundedRelation A -> Rel A A := @proj1_sig _ (@well_founded A).
Definition preOf {frame1 frame2} :
  PreAndPostConditions frame1 frame2 ->
  Rel (FrameCall frame1) (FrameCall frame2) := fst.
Definition postOf {frame1 frame2} :
  PreAndPostConditions frame1 frame2 ->
  PostRel (FrameCall frame1) (FrameCall frame2) := snd.

Inductive ContinueType := Continue_multifix | Continue_total_spec.
Polymorphic Definition ContinueArg ct : Type :=
  match ct with
  | Continue_multifix => (Prop * Type * Type)%type
  | Continue_total_spec => (Prop * Prop * Type * Type)%type
  end.
Polymorphic Definition Continue {ct : ContinueType} : ContinueArg ct -> Type :=
  match ct return ContinueArg ct -> Type with
  | Continue_multifix => fun '(precond, goal1, goal2) => (precond * goal1 * goal2)%type
  | Continue_total_spec => fun '(tsPre, precond, H, goal) => (tsPre * precond * H * goal)%type
  end.
Arguments Continue {ct carg}.

Lemma Continue_multifix_unfold precond goal1 goal2 :
  RelGoal precond -> goal1 -> goal2 ->
  @Continue Continue_multifix (precond, goal1, goal2).
  Proof. split; eauto. Qed.
Lemma Continue_total_spec_unfold tsPre precond H goal :
  RelGoal tsPre -> RelGoal precond -> H -> goal ->
  @Continue Continue_total_spec (tsPre, precond, H, goal).
Proof. split; eauto. Qed.

Ltac Continue_unfold :=
  match goal with
  | |- @Continue Continue_multifix _ => simple apply Continue_multifix_unfold
  | |- @Continue Continue_total_spec _ => simple apply Continue_total_spec_unfold
  end.

#[global] Hint Opaque WellFoundedRelation : refines prepostcond.
#[global] Hint Opaque PreAndPostConditions : refines prepostcond.
#[global] Hint Opaque Continue : refines prepostcond.

#[global] Hint Extern 999 (WellFoundedRelation _) => shelve : refines prepostcond.
#[global] Hint Extern 999 (PreAndPostConditions _ _) => shelve : refines prepostcond.
#[global] Hint Extern 999 (Continue) => shelve : refines prepostcond.

Lemma spec_refines_multifix_bind_IntroArg (E1 E2 : EvType) Γ1 Γ2 frame1 frame2 R1 R2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2) RR
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (bodies2 : FrameTuple E2 (frame2 :: Γ2) frame2)
      (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (k1 : FrameCallRet frame1 call1 -> SpecM E1 Γ1 R1)
      (k2 : FrameCallRet frame2 call2 -> SpecM E2 Γ2 R2)
      (prepostconds : PreAndPostConditions frame1 frame2) :
  @Continue Continue_multifix
            (preOf prepostconds call1 call2,
             IntroArg Call _ (fun call1' => IntroArg Call _ (fun call2' =>
              IntroArg Hyp (preOf prepostconds call1' call2') (fun _ =>
              spec_refines (pushPreRel (preOf prepostconds) RPre)
                           (pushPostRel (postOf prepostconds) RPost)
                           (postOf prepostconds call1' call2')
                           (applyFrameTuple _ _ _ bodies1 call1')
                           (applyFrameTuple _ _ _ bodies2 call2')))),
             IntroArg RetAny _ (fun r1 => IntroArg RetAny _ (fun r2 =>
              IntroArg Hyp (postOf prepostconds call1 call2 r1 r2) (fun _ =>
              spec_refines RPre RPost RR (k1 r1) (k2 r2))))) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1 >>= k1)
               (MultiFixS E2 Γ2 frame2 bodies2 call2 >>= k2).
Proof.
  destruct prepostconds; intros [[]].
  unfold IntroArg in *; eapply spec_refines_multifix_bind; eauto.
Qed.

Lemma spec_refines_multifix_IntroArg (E1 E2 : EvType) Γ1 Γ2 frame1 frame2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (bodies2 : FrameTuple E2 (frame2 :: Γ2) frame2)
      (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (RR : Rel (encodes call1) (encodes call2))
      (prepostconds : PreAndPostConditions frame1 frame2) :
  @Continue Continue_multifix
            (preOf prepostconds call1 call2,
             IntroArg RetAny _ (fun r1 => IntroArg RetAny _ (fun r2 =>
              IntroArg Hyp (postOf prepostconds call1 call2 r1 r2) (fun _ =>
              RelGoal (RR r1 r2)))),
             IntroArg Call _ (fun call1' => IntroArg Call _ (fun call2' =>
              IntroArg Hyp (preOf prepostconds call1' call2') (fun _ =>
              spec_refines (pushPreRel (preOf prepostconds) RPre)
                           (pushPostRel (postOf prepostconds) RPost)
                           (postOf prepostconds call1' call2')
                           (applyFrameTuple _ _ _ bodies1 call1')
                           (applyFrameTuple _ _ _ bodies2 call2'))))) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1)
               (MultiFixS E2 Γ2 frame2 bodies2 call2).
Proof.
  destruct prepostconds; intros [[]].
  unfold IntroArg in *; eapply spec_refines_multifix; eauto.
Qed.

Lemma spec_refines_total_spec_IntroArg (E1 E2 : EvType) Γ1 Γ2 frame1
      A2 B2 `{QuantType A2} `{QuantType B2}
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (call1 : FrameCall frame1) (a2 : A2)
      (RR : Rel (FrameCallRet frame1 call1) B2)
      (tsPre : A2 -> Prop) (tsPost : A2 -> B2 -> Prop)
      (rdec : WellFoundedRelation A2)
      (prepostconds : PreAndPostConditions frame1 (unary1Frame A2 B2)) :
  @Continue Continue_total_spec
            (tsPre a2, preOf prepostconds call1 (unary1Call a2),
             IntroArg RetAny _ (fun r1 => IntroArg RetAny _ (fun r2 =>
              IntroArg Hyp (tsPost a2 r2) (fun _ =>
              IntroArg Hyp (postOf prepostconds call1 (unary1Call a2) r1 r2) (fun _ =>
              RelGoal (RR r1 r2))))),
             IntroArg Call _ (fun call1' => IntroArg Any _ (fun a2' =>
              IntroArg Hyp (tsPre a2') (fun _ =>
              IntroArg Hyp (preOf prepostconds call1' (unary1Call a2')) (fun _ =>
              spec_refines (pushTSPreRel tsPre (preOf prepostconds) RPre)
                           (pushTSPostRel tsPost (postOf prepostconds) RPost)
                           (pushTSRR tsPost (postOf prepostconds) call1' a2')
                           (applyFrameTuple _ _ _ bodies1 call1')
                           (total_spec_fix_body tsPre tsPost (wfRelOf rdec) a2')))))) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1)
               (total_spec tsPre tsPost a2).
Proof.
  destruct rdec, prepostconds; intros [[[]]].
  unfold IntroArg, RelGoal in *; simpl in *.
  unshelve eapply spec_refines_total_spec; eauto.
Qed.

#[global]
Hint Extern 101 (spec_refines ?RPre ?RPost ?RR
                              (MultiFixS ?E1 ?Γ1 ?frame1 ?bodies1 ?call1 >>= ?k1)
                              (MultiFixS ?E2 ?Γ2 ?frame2 ?bodies2 ?call2 >>= ?k2)) =>
  unshelve (
    let HPrePost := fresh "HPrePost" in
    epose (HPrePost := from_user (A:=PreAndPostConditions frame1 frame2));
    eapply (spec_refines_multifix_bind_IntroArg E1 E2 Γ1 Γ2 frame1 frame2 _ _
              RPre RPost RR bodies1 bodies2 call1 call2 k1 k2 HPrePost)) : refines.
#[global]
Hint Extern 101 (spec_refines ?RPre ?RPost ?RR
                              (MultiFixS ?E1 ?Γ1 ?frame1 ?bodies1 ?call1)
                              (MultiFixS ?E2 ?Γ2 ?frame2 ?bodies2 ?call2)) =>
  unshelve (
    let HPrePost := fresh "HPrePost" in
    epose (HPrePost := from_user (A:=PreAndPostConditions frame1 frame2));
    eapply (spec_refines_multifix_IntroArg E1 E2 Γ1 Γ2 frame1 frame2
              RPre RPost bodies1 bodies2 call1 call2 RR HPrePost)) : refines.
#[global]
Hint Extern 101 (spec_refines ?RPre ?RPost ?RR
                              (MultiFixS ?E1 ?Γ1 ?frame1 ?bodies1 ?call1)
                              (@total_spec ?E2 ?Γ2 ?A2 ?B2 _ ?tsPre ?tsPost ?a2)) =>
  unshelve (
    let HWf := fresh "HWf" in
    epose (HWf := from_user (A:=WellFoundedRelation A2));
    let HPrePost := fresh "HPrePost" in
    epose (HPrePost := from_user (A:=PreAndPostConditions frame1 (unary1Frame A2 B2)));
    eapply (spec_refines_total_spec_IntroArg E1 E2 Γ1 Γ2 frame1 A2 B2
              RPre RPost bodies1 call1 a2 RR tsPre tsPost HWf HPrePost));
  unfold total_spec_fix_body : refines.

Lemma spec_refines_call_bind_IntroArg (E1 E2 : EvType) Γ1 Γ2 frame1 frame2 R1 R2
      (RPre : SpecPreRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (RPost : SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      RR (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (k1 : FrameCallRet frame1 call1 -> SpecM E1 (frame1 :: Γ1) R1)
      (k2 : FrameCallRet frame2 call2 -> SpecM E2 (frame2 :: Γ2) R2) :
  RelGoal (RPre (inl call1) (inl call2)) ->
  (IntroArg RetAny _ (fun r1 => IntroArg RetAny _ (fun r2 =>
   IntroArg Hyp (RPost (inl call1) (inl call2) r1 r2) (fun _ =>
   spec_refines RPre RPost RR (k1 (resum_ret call1 r1)) (k2 (resum_ret call2 r2)))))) ->
  spec_refines RPre RPost RR (CallS _ _ _ call1 >>= k1) (CallS _ _ _ call2 >>= k2).
Proof. apply spec_refines_call_bind. Qed.

Lemma spec_refines_call_IntroArg (E1 E2 : EvType) Γ1 Γ2 frame1 frame2
      (RPre : SpecPreRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (RPost : SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (RR : Rel (FrameCallRet frame1 call1) (FrameCallRet frame2 call2)) :
  RelGoal (RPre (inl call1) (inl call2)) ->
  IntroArg RetAny _ (fun r1 => IntroArg RetAny _ (fun r2 =>
   IntroArg Hyp (RPost (inl call1) (inl call2) r1 r2) (fun _ =>
   RelGoal (RR r1 r2)))) ->
  spec_refines RPre RPost RR (CallS _ _ _ call1) (CallS _ _ _ call2).
Proof. intros; apply spec_refines_call; eauto. Qed.

#[global] Hint Extern 101 (spec_refines _ _ _ (CallS _ _ _ _ >>= _) (CallS _ _ _ _ >>= _)) =>
  apply spec_refines_call_bind_IntroArg : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (CallS _ _ _ _) (CallS _ _ _ _)) =>
  apply spec_refines_call_IntroArg : refines.

#[global] Hint Extern 201 (spec_refines _ _ _ (CallS _ _ _ ?call1) _) =>
  simple apply (spec_refines_call_bind_ret_l _ _ _ _ _ _ _ _ _ call1) : refines.
#[global] Hint Extern 201 (spec_refines _ _ _ _ (CallS _ _ _ ?call2)) =>
  simple apply (spec_refines_call_bind_ret_r _ _ _ _ _ _ _ _ _ _ _ call2) : refines.

#[global] Hint Extern 991 (spec_refines _ _ _ (CallS _ _ _ _ >>= _) (trepeat _ _)) =>
  simple apply spec_refines_trepeat_suc_r : refines.
#[global] Hint Extern 991 (spec_refines _ _ _ (CallS _ _ _ _ >>= _) (trepeat _ _ >>= _)) =>
  simple apply spec_refines_trepeat_bind_suc_r : refines.

#[global] Hint Extern 992 (spec_refines _ _ _ _ (trepeat _ _)) =>
  simple apply spec_refines_trepeat_zero_r : refines.
#[global] Hint Extern 992 (spec_refines _ _ _ _ (trepeat _ _ >>= _)) =>
  simple apply spec_refines_trepeat_bind_zero_r : refines.


(** * Tactics for proving refinement *)

Ltac prove_refinement_rewrite :=
  try unshelve rewrite_strat (bottomup (hints refines)).

Ltac split_prod_goal :=
  repeat match goal with
  | |- _ /\ _        => split
  | |- { _ : _ & _ } => split
  | |- _ * _         => split
  | |- unit          => exact tt
  | |- True          => trivial
  end.

Ltac prove_refinement_prepostcond :=
  unshelve typeclasses eauto with prepostcond;
  simpl LRTOutput in *; simpl FrameCallIndex;
  split_prod_goal; prove_refinement_rewrite.

Ltac shelve_goal_if_Type :=
  match goal with
  | |- WellFoundedRelation _ => idtac
  | |- PreAndPostConditions _ _ => idtac
  | |- Continue => idtac
  | |- ?g => let t := type of g in
             match t with
             | Type => shelve
             | Set => shelve
             | _ => idtac
             end
  end.

Ltac prove_refinement :=
  unshelve typeclasses eauto with refines;
  split_prod_goal; shelve_goal_if_Type;
  cbn [ IntroArg_prod IntroArg_sigT IntroArg_unit
        IntroArg_FrameCall
        IntroArg_LRTInput_Fun IntroArg_LRTInput_Ret ] in *;
  split_prod_goal; prove_refinement_rewrite;
  try solve [ assumption | reflexivity | contradiction ].

Ltac prove_refinement_continue :=
  Continue_unfold; prove_refinement.


(** * Tactics for pre/post-conditions and well-founded relations *)

Definition DecreasingNat {A} (_ : A) := nat.
#[global] Hint Opaque DecreasingNat : prepostcond.
#[global] Hint Extern 999 (DecreasingNat _) => shelve : prepostcond.

Tactic Notation "wellfounded_decreasing_nat" :=
  let f := fresh "f" in
  enough (IntroArg Any _ DecreasingNat) as f
    by (exact (exist _ (fun a b => f a < f b) (well_founded_ltof _ f)));
  prove_refinement_prepostcond.
Tactic Notation "wellfounded_decreasing_nat" uconstr(f) :=
  exact (exist _ (fun a b => f a < f b) (well_founded_ltof _ f)).

Definition well_founded_False {A} :
  @well_founded A (fun _ _ => False).
Proof. constructor; contradiction. Defined.

Ltac wellfounded_none :=
  exact (exist _ (fun _ _ => False) well_founded_False).

Definition PreCase {frame1 frame2} i j
  (a1 : LRTInput (nthLRT frame1 i))
  (a2 : LRTInput (nthLRT frame2 j)) := Prop.
Definition PostCase {frame1 frame2} i j args1 args2
  (r1 : LRTOutput (nthLRT frame1 i) args1)
  (r2 : LRTOutput (nthLRT frame2 j) args2) := Prop.

#[global] Hint Opaque PreCase : prepostcond.
#[global] Hint Opaque PostCase : prepostcond.

#[global] Hint Extern 999 (PreCase _ _ _ _) => shelve : prepostcond.
#[global] Hint Extern 999 (PostCase _ _ _ _ _ _) => shelve : prepostcond.

Definition prepost_case {frame1 frame2} i j
  (pre : IntroArg Any (LRTInput (nthLRT frame1 i)) (fun a1 =>
         IntroArg Any (LRTInput (nthLRT frame2 j)) (fun a2 =>
         PreCase i j a1 a2)))
  (post : IntroArg Any _ (fun args1 => IntroArg Any _ (fun args2 =>
          IntroArg RetAny (LRTOutput (nthLRT frame1 i) args1) (fun r1 =>
          IntroArg RetAny (LRTOutput (nthLRT frame2 j) args2) (fun r2 =>
          PostCase i j args1 args2 r1 r2)))))
  (prepostcond : PreAndPostConditions frame1 frame2) :
  PreAndPostConditions frame1 frame2.
Proof.
  unfold IntroArg, PreCase, PostCase in *; split.
  all: intros [m args1] [n args2].
  all: destruct (Nat.eq_dec m i) as [p1|]; destruct (Nat.eq_dec n j) as [p2|].
  all: try (destruct p1; destruct p2).
  1: apply pre; eauto.
  1-3: exact (preOf prepostcond (FrameCallOfArgs _ m args1)
                                (FrameCallOfArgs _ n args2)).
  1: apply post; eauto.
  1-3: exact (postOf prepostcond (FrameCallOfArgs _ m args1)
                                (FrameCallOfArgs _ n args2)).
Defined.

Notation eqPreCase :=
  (fun (args1 : LRTInput (nthLRT _ _)) (args2 : LRTInput (nthLRT _ _)) =>
       eq args1 args2)
  (only parsing).
Notation eqPostCase :=
  (ltac:(intros args1 args2 r1 r2;
         apply (eq_dep1 _ _ args1 r1 args2 r2)))
  (only parsing).

Tactic Notation "prepost_case" constr(i) constr(j) :=
  apply (prepost_case i j); prove_refinement_prepostcond.
Tactic Notation "prepost_case" constr(i) constr(j) "withPre" uconstr(pre) :=
  apply (prepost_case i j); [ exact pre | prove_refinement_prepostcond |].
Tactic Notation "prepost_case" constr(i) constr(j) "withPost" uconstr(post) :=
  apply (prepost_case i j); [ prove_refinement_prepostcond | exact post |].
Tactic Notation "prepost_case" constr(i) constr(j) "with" uconstr(pre) "," uconstr(post) :=
  apply (prepost_case i j); [exact pre | exact post |].

Definition PreExcludedCase (i j : nat) := False.
Definition PostExcludedCase (i j : nat) := False.

Tactic Notation "prepost_exclude_case" constr(i) constr(j) :=
  apply (prepost_case i j); [ exact (fun _ _ => PreExcludedCase i j)
                            | exact (fun _ _ _ _ => PostExcludedCase i j)].
Tactic Notation "prepost_exclude_remaining" :=
  exact (fun calli callj => PreExcludedCase (FrameCallIndex calli) (FrameCallIndex callj),
         fun calli callj _ _ => PostExcludedCase (FrameCallIndex calli) (FrameCallIndex callj)).

#[global] Hint Extern 101 (IntroArg ?n (wfRelOf _ _ _) _) =>
  let e := argName n in IntroArg_intro e;
  cbn in e; revert e; apply (IntroArg_fold n _ _) : refines.
#[global] Hint Extern 101 (IntroArg ?n (preOf _ _ _) _) =>
  let e := argName n in IntroArg_intro e;
  cbn in e; revert e; apply (IntroArg_fold n _ _) : refines.
#[global] Hint Extern 101 (IntroArg ?n (postOf _ _ _ _ _) _) =>
  let e := argName n in IntroArg_intro e;
  cbn in e; revert e; apply (IntroArg_fold n _ _) : refines.
#[global] Hint Extern 101 (RelGoal (wfRelOf _ _ _)) =>
  unfold RelGoal; cbn; apply RelGoal_fold : refines.
#[global] Hint Extern 101 (RelGoal (preOf _ _ _)) =>
  unfold RelGoal; cbn; apply RelGoal_fold : refines.
#[global] Hint Extern 101 (RelGoal (postOf _ _ _ _ _)) =>
  unfold RelGoal; cbn; apply RelGoal_fold : refines.



(** * Testing *)

Open Scope nat_scope.

Lemma test_ifs E x :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (if 0 <=? x then if x <? 256 then RetS 1 else RetS 0 else RetS 0)
                  (if x <? 256 then if 0 <=? x then RetS 1 else RetS 0 else RetS 0).
Proof.
  prove_refinement.
Qed.

Lemma test_exists E x :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (RetS (x+1))
                  (ExistsS nat >>= RetS).
Proof.
  prove_refinement.
Qed.

Lemma test_spins E (x : nat) :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (MultiFixS E nil (unary1Frame nat nat)
                    ((fun a => CallS _ _ _ (mkFrameCall (unary1Frame nat nat) 0 a)), tt)
                    (mkFrameCall (unary1Frame nat nat) 0 x))
                  (MultiFixS E nil (unary1Frame nat nat)
                    ((fun a => CallS _ _ _ (mkFrameCall (unary1Frame nat nat) 0 a)), tt)
                    (mkFrameCall (unary1Frame nat nat) 0 x)).
Proof.
  prove_refinement.
  - prepost_case 0 0 with eqPreCase, eqPostCase.
    prepost_exclude_remaining.
  - prove_refinement_continue.
Qed.

Definition testFrame1 : RecFrame :=
  LRT_Fun nat (fun _ => LRT_Ret nat) :: LRT_Fun nat (fun _ => LRT_Ret nat) :: nil.

Lemma test_spins_rets E (x : nat) :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (MultiFixS E nil testFrame1
                    ((fun a => CallS _ _ _ (mkFrameCall testFrame1 0 a)),
                     ((fun a => RetS a), tt))
                    (mkFrameCall testFrame1 1 x))
                  (MultiFixS E nil testFrame1
                    ((fun a => RetS a),
                     ((fun a => CallS _ _ _ (mkFrameCall testFrame1 1 a)), tt))
                    (mkFrameCall testFrame1 0 x)).
Proof.
  prove_refinement.
  - prepost_case 1 0 with eqPreCase, eqPostCase.
    prepost_case 0 1 with eqPreCase, eqPostCase.
    prepost_exclude_remaining.
  - prove_refinement_continue.
Qed.

Lemma test_total_spec_easy E (x : nat) :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (MultiFixS E nil (unary1Frame nat nat)
                    ((fun a => RetS (a + 1)), tt)
                    (mkFrameCall (unary1Frame nat nat) 0 x))
                  (total_spec (fun _ => True)
                              (fun a b => b = (a + 1)) x).
Proof.
  prove_refinement.
  - wellfounded_none.
  - prepost_case 0 0 withPre eqPreCase; [ exact (r = r0) |].
    prepost_exclude_remaining.
  - prove_refinement_continue.
Qed.

Lemma test_total_spec_loop E (x : nat) :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (MultiFixS E nil (unary1Frame nat nat)
                    ((fun a => if a =? 0 then RetS 0
                               else a' <- CallS _ _ _ (mkFrameCall (unary1Frame nat nat)
                                                      0 (pred a)) ;;
                                    RetS (S a')), tt)
                    (mkFrameCall (unary1Frame nat nat) 0 x))
                  (total_spec (fun _ => True)
                              (fun a b => a = b) x).
Proof.
  prove_refinement.
  - wellfounded_decreasing_nat; exact a.
  - prepost_case 0 0 withPre eqPreCase; [ exact (r = r0) |].
    prepost_exclude_remaining.
  - prove_refinement_continue.
    + apply Nat.eqb_eq in e_if; eauto.
    + destruct a0; [ discriminate e_if | eauto ].
    + destruct a0; [ discriminate e_if | eauto ].
Qed.

(* 
Lemma test_total_spec_less_easy E (x : nat) :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (MultiFixS E nil testFrame1
                    ((fun a => CallS _ _ _ (mkFrameCall testFrame1 1 (a + 1))),
                     ((fun a => RetS (a + 1)), tt))
                    (mkFrameCall testFrame1 1 x))
                  (total_spec (fun _ => True)
                              (fun a b => a = (b + 2)) x).
Proof.
  prove_refinement.
  - wellfounded_none.
  - prepost_case 0 0 withPre eqPreCase.
    { simpl; intros. exact () } *)
