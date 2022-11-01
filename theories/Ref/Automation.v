From Coq Require Export
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

(** Ret and bind laws for spec_refines **)

Lemma spec_refines_ret E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR r1 r2 :
  (RR r1 r2 : Prop) ->
  @spec_refines E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR (RetS r1) (RetS r2).
Proof.
  intros. apply padded_refines_ret. auto.
Qed.

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
  | 0 => Ret tt
  | S m => s;; trepeat m s
  end.

Lemma spec_refines_trepeat_zero_r E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR
      (t1 : SpecM E1 Γ1 R1) (t2 : SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR t1 (Ret tt) ->
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
  intros. eapply padded_refines_bind.
  - unfold CallS. unfold trigger. apply padded_refines_vis.
    auto. cbn.
    eauto. intros a b Hab. apply padded_refines_ret.
    Unshelve. 
    2 : {
      intros c1 c2. 
      exact (exists a, exists b, c1 = resum_ret call1 a /\ c2 = resum_ret call2 b /\ RPost _ _ a b).
      }
      cbn. exists a. exists b. auto.
  - intros r1 r2 Hr12. cbn in Hr12. decompose record Hr12.
    subst. apply H0. auto.
Qed.


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
  intros Hcalls Hbody Hk.
  eapply padded_refines_bind with (RR := postcond call1 call2).
  - unfold MultiFixS. 
    eapply padded_refines_interp_mrec_spec with (RPreInv := precond) (RPostInv := postcond).
    + intros. apply Hbody in H. eapply padded_refines_monot; try apply H; auto; clear - E1.
      * intros call1 call2 Hcall. 
        destruct call1; destruct call2; cbn in *; try contradiction;
          constructor; auto.
      * intros call1 call2 r1 r2 H. destruct H; auto.
    + apply Hbody in Hcalls.
      eapply padded_refines_monot; try apply Hcalls; auto; clear - E1.
      * intros call1 call2 Hcall. 
        destruct call1; destruct call2; cbn in *; try contradiction;
          constructor; auto.
      * intros call1 call2 r1 r2 H. destruct H; auto.
  - auto.
Qed.

(* Build a RecFrame with a single, unary function *)
Definition unary1Frame (A B : Type) : RecFrame :=
  cons (LRT_Fun A (fun _ => LRT_Ret B)) nil.


(* The total correctness specification *)
Definition total_spec {E Γ A B} `{QuantType B}
           (pre : A -> Prop) (post : A -> B -> Prop) (a : A) : SpecM E Γ B :=
  AssumeS (pre a);;
  b <- ExistsS B;;
  AssertS (post a b);;
  Ret b.

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
  b <- exists_spec B;;
  AssertS (post a b);;
  Ret b.

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
           (pre : A2 -> Prop) (preEq : Rel (FrameCall frame1) A2)
           (RPre : SpecPreRel E1 E2 Γ1 Γ2) :
  SpecPreRel E1 E2 (frame1 :: Γ1) (unary1Frame A2 B2 :: Γ2) :=
  fun a1 a2 => match a1,a2 with
               | inl args1, inl (FrameCallOfArgs _ 0 (existT _ a2 _)) =>
                 pre a2 /\ preEq args1 a2
               | inr ev1, inr ev2 => RPre ev1 ev2
               | _, _ => False
               end.

(* Add a postcondition relation for proving total_spec refinement *)
Definition pushTSPostRel {E1 E2 : EvType} {Γ1 Γ2 frame1 A2 B2}
           (post : A2 -> B2 -> Prop)
           (postEq : forall call1', A2 -> FrameCallRet frame1 call1' -> B2 -> Prop)
           (RPost : SpecPostRel E1 E2 Γ1 Γ2) :
  SpecPostRel E1 E2 (frame1 :: Γ1) (unary1Frame A2 B2 :: Γ2) :=
  fun a1 a2 => match a1,a2 return encodes a1 -> encodes a2 -> Prop with
               | inl args1, inl (FrameCallOfArgs _ 0 (existT _ a2 _)) =>
                 fun r1 b2 => post a2 b2 /\ postEq args1 a2 r1 b2
               | inr a1', inr a2' => RPost a1' a2'
               | _, _ => fun _ _ => False
               end.

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
                                                       (fun _ : unit => Ret b)))))) (fun b : B => Ret (call_unary1Frame call b)))
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
                (fun b : B => EnTree.bind (AssertS (post x b)) (fun _ : unit => Ret b))) )
    .
    { eapply padded_refines_bind; eauto. eapply padded_refines_weaken_l; eauto. } 
    clear - Hwf Hpre Hdec. cbn.
    apply padded_refines_bind_bind_l. quantl. auto.
    apply padded_refines_bind_bind_l. quantl. intros b. apply padded_refines_bind_bind_l.
    quantl. intros. rewrite bind_ret_l. quantl. intros bf.
    quantl. intros Hbf. quantr. exists bf. quantr. auto. apply padded_refines_ret.
    auto.
Qed.

Definition lift_preEq
  {frame1 : RecFrame} {A2 B2 : Type} pre preEq : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)) :=
  fun c1 c2 => exists a : A2, FrameCallOfArgs (unary1Frame A2 B2) 0 (existT _ a tt) = c2 /\ preEq c1 a /\ pre a.

Definition lift_postEq:
  forall {frame1 : RecFrame} {A2 B2 : Type} (post : Rel A2 B2),
    (forall call1' : FrameCall frame1, A2 -> Rel (FrameCallRet frame1 call1') B2) ->
    PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)).
  intros frame1 A2 B2 post postEq.
  intros c1 c2 a b.
  specialize (postEq c1 (uncall_unary1Frame c2)).
  destruct c2. cbn in b. destruct n.
  cbn in b. destruct args. apply (post x b /\ postEq a b).
  destruct args. destruct x.
Defined.
(*with some strategic lemmas this should be doable *)

Lemma spec_refines_total_spec_monot_aux1:
  forall (E1 E2 : EvType) (Γ1 Γ2 : FunStack) (frame1 : RecFrame) (A2 B2 : Type) (RPre : SpecPreRel E1 E2 Γ1 Γ2)
    (preEq : Rel (FrameCall frame1) A2) (pre : A2 -> Prop)
    (x0 : FrameCall frame1 +
            (fix FunStackE (E : Type) (Γ : FunStack) {struct Γ} : Type :=
               match Γ with
               | nil => (ErrorE + E)%type
               | frame :: Γ' => (FrameCall frame + FunStackE E Γ')%type
               end) E1 Γ1) (x1 : FrameCall (unary1Frame A2 B2) + FunStackE E2 Γ2),
    pushTSPreRel pre preEq RPre x0 x1 -> HeterogeneousRelations.sum_rel (lift_preEq pre preEq) RPre x0 x1.
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
    (postEq : forall call1' : FrameCall frame1, A2 -> Rel (FrameCallRet frame1 call1') B2) (post : Rel A2 B2)
    (e1 : FrameCall frame1 +
            (fix FunStackE (E : Type) (Γ : FunStack) {struct Γ} : Type :=
               match Γ with
               | nil => (ErrorE + E)%type
               | frame :: Γ' => (FrameCall frame + FunStackE E Γ')%type
               end) E1 Γ1) (e2 : FrameCall (unary1Frame A2 B2) + FunStackE E2 Γ2) (x0 : encodes e1) (x1 : encodes e2),
    SumPostRel (lift_postEq post postEq) RPost e1 e2 x0 x1 -> pushTSPostRel post postEq RPost e1 e2 x0 x1.
Proof.
  intros E1 E2 Γ1 Γ2 frame1 A2 B2 RPost postEq post.
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
      (preEq : Rel (FrameCall frame1) A2)
      (postEq : forall call1' a2', FrameCallRet frame1 call1' -> B2 -> Prop)
      (pre : A2 -> Prop) (post : A2 -> B2 -> Prop)
      (rdec : A2 -> A2 -> Prop) :
  well_founded rdec ->
  pre a2 -> preEq call1 a2 ->
  (forall r1 r2, postEq call1 a2 r1 r2 -> RR r1 r2) ->
  (* this condition should be signed off on by Eddy *)
  (forall c a x y, postEq c a x y -> post a y) ->
  (forall call1' a2',
      pre a2' -> preEq call1' a2' ->
      spec_refines (pushTSPreRel pre preEq RPre)
                   (pushTSPostRel post postEq RPost)
                   (postEq call1' a2')
                   (applyFrameTuple _ _ _ bodies1 call1')
                   (total_spec_fix_body pre post rdec a2')) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1)
               (total_spec pre post a2).
Proof.
  intros Hwf Ha2 Hca HPost HPost'. intros.
  eapply total_spec_fix_refines_total_spec in Hwf as Hstrict. Unshelve. all : auto.
  eapply padded_refines_weaken_l; eauto.
  eapply padded_refines_interp_mrec_spec with (RPreInv := lift_preEq pre preEq) (RPostInv := lift_postEq post postEq).
  - clear Hca Ha2 Hstrict . rename a2 into a0. intros c1 c2 Hpre. destruct c2. destruct n.
    2 : { destruct args as [ [] _]. }
    cbn in args. destruct args as [a2 [] ]. simpl. setoid_rewrite bind_ret_r.
    specialize (H1 c1 a2).
    assert (pre a2 /\ preEq c1 a2).
    {
      clear - Hpre. (* might be premature *)
      red in Hpre. decompose record Hpre. clear Hpre.
      cbv in H0. apply inj_FrameCallOfArgs in H0.
      dependent destruction H0. auto.
    }
    destruct H2. specialize (H1 H2 H3).
    (* should be able to *)
    eapply padded_refines_monot; try apply H1.
    + apply spec_refines_total_spec_monot_aux1.
    + apply spec_refines_total_spec_monot_aux2.
    + cbn. intros a b Hab. split; eauto.
  - specialize (H1 call1 a2 Ha2 Hca). eapply padded_refines_monot; try apply H1.
    + apply spec_refines_total_spec_monot_aux1.
    + apply spec_refines_total_spec_monot_aux2.
    + auto.
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
Inductive ArgName := Any | RetAny | Hyp | Exists | Forall | If | Match.
Ltac argName n :=
  match n with
  | Any      => fresh "a"
  | RetAny   => fresh "r"
  | Hyp      => fresh "H"
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

Polymorphic Lemma IntroArg_fold n A goal : forall a, IntroArg n A goal -> goal a.
Proof. intros a H; exact (H a). Qed.

(* Polymorphic Lemma IntroArg_unfold n A (goal : A -> Prop) : (forall a, goal a) -> IntroArg n A goal. *)
(* Proof. unfold IntroArg; intro H; exact H. Qed. *)

Ltac IntroArg_intro e := intro e.

Ltac IntroArg_forget := let e := fresh in intro e; clear e.

Polymorphic Lemma IntroArg_beta n A (f : A -> Type) x goal :
  IntroArg n (f x) goal ->
  IntroArg n ((fun x' => f x') x) goal.
Proof. eauto. Qed.

Polymorphic Lemma IntroArg_and n P Q (goal : P /\ Q -> Prop)
  : IntroArg n P (fun p => IntroArg n Q (fun q => goal (conj p q))) ->
    IntroArg n _ goal.
Proof. intros H [ p q ]; apply H. Qed.

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
            (pre : A2 -> Prop) (preEq : Rel (FrameCall frame1) A2)
            (RPre : SpecPreRel E1 E2 Γ1 Γ2)
            args1 a2 (goal : _ -> Prop) :
  IntroArg n (pre a2 /\ preEq args1 a2) goal ->
  IntroArg n (@pushTSPreRel E1 E2 Γ1 Γ2 frame1 A2 B2
                            pre preEq RPre (inl args1)
                            (inl (mkFrameCall (unary1Frame A2 B2) 0 a2))) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSPreRel_inr n E1 E2 Γ1 Γ2 frame1 A2 B2
            (pre : A2 -> Prop) (preEq : Rel (FrameCall frame1) A2)
            (RPre : SpecPreRel E1 E2 Γ1 Γ2)
            e1 e2 (goal : _ -> Prop) :
  IntroArg n (RPre e1 e2) goal ->
  IntroArg n (@pushTSPreRel E1 E2 Γ1 Γ2 frame1 A2 B2
                            pre preEq RPre (inr e1) (inr e2)) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSPostRel_inl n E1 E2 Γ1 Γ2 frame1 A2 B2
            (post : A2 -> B2 -> Prop)
            (postEq : forall call1', A2 -> FrameCallRet frame1 call1' -> B2 -> Prop)
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            args1 a2 r1 b2 (goal : _ -> Prop) :
  IntroArg n (post a2 b2 /\ postEq args1 a2 r1 b2) goal ->
  IntroArg n (@pushTSPostRel E1 E2 Γ1 Γ2 frame1 A2 B2
                             post postEq RPost (inl args1)
                             (inl (mkFrameCall (unary1Frame A2 B2) 0 a2)) r1 b2) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSPostRel_inr n E1 E2 Γ1 Γ2 frame1 A2 B2
            (post : A2 -> B2 -> Prop)
            (postEq : forall call1', A2 -> FrameCallRet frame1 call1' -> B2 -> Prop)
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            e1 e2 r1 r2 (goal : _ -> Prop) :
  IntroArg n (RPost e1 e2 r1 r2) goal ->
  IntroArg n (@pushTSPostRel E1 E2 Γ1 Γ2 frame1 A2 B2
                             post postEq RPost (inr e1) (inr e2) r1 r2) goal.
Proof. intro H. apply H. Qed.

Ltac IntroArg_intro_dependent_destruction n :=
  let e := argName n in
    IntroArg_intro e; dependent destruction e.

Ltac IntroArg_base_tac n A g :=
  lazymatch A with
  | (fun _ => _) _ => simple apply IntroArg_beta
  | _ /\ _ => simple apply IntroArg_and
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
  | eqPostRel _ _ _ _ _ _ => apply IntroArg_eqPostRel
  | true  = true  => IntroArg_intro_dependent_destruction n
  | false = false => IntroArg_intro_dependent_destruction n
  | true  = false => IntroArg_intro_dependent_destruction n
  | false = true  => IntroArg_intro_dependent_destruction n
  end.

#[global] Hint Extern 101 (IntroArg ?n ?A ?g) =>
  IntroArg_base_tac n A g : refines prepostcond.

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

(* If nothing else works for a RelGoal, try reflexivity and then shelve it *)
#[global] Hint Extern 999 (RelGoal _) =>
  unfold RelGoal; (reflexivity || shelve) : refines.


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
            (pre : A2 -> Prop) (preEq : Rel (FrameCall frame1) A2)
            (RPre : SpecPreRel E1 E2 Γ1 Γ2)
            args1 a2 :
  RelGoal (pre a2 /\ preEq args1 a2) ->
  RelGoal (@pushTSPreRel E1 E2 Γ1 Γ2 frame1 A2 B2
                            pre preEq RPre (inl args1)
                            (inl (mkFrameCall (unary1Frame A2 B2) 0 a2))).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushTSPreRel _ _ _ _ _ _ _ _ _ _ (inl _) (inl _))) =>
  apply RelGoal_pushTSPreRel_inl : refines.


Polymorphic Lemma RelGoal_pushTSPreRel_inr E1 E2 Γ1 Γ2 frame1 A2 B2
            (pre : A2 -> Prop) (preEq : Rel (FrameCall frame1) A2)
            (RPre : SpecPreRel E1 E2 Γ1 Γ2)
            e1 e2 :
  RelGoal (RPre e1 e2) ->
  RelGoal (@pushTSPreRel E1 E2 Γ1 Γ2 frame1 A2 B2
                            pre preEq RPre (inr e1) (inr e2)).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushTSPreRel _ _ _ _ _ _ _ _ _ _ (inr _) (inr _))) =>
  apply RelGoal_pushTSPreRel_inr : refines.


Polymorphic Lemma RelGoal_pushTSPostRel_inl E1 E2 Γ1 Γ2 frame1 A2 B2
            (post : A2 -> B2 -> Prop)
            (postEq : forall call1', A2 -> FrameCallRet frame1 call1' -> B2 -> Prop)
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            args1 a2 r1 b2 :
  RelGoal (post a2 b2 /\ postEq args1 a2 r1 b2) ->
  RelGoal (@pushTSPostRel E1 E2 Γ1 Γ2 frame1 A2 B2
                             post postEq RPost (inl args1)
                             (inl (mkFrameCall (unary1Frame A2 B2) 0 a2)) r1 b2).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushTSPostRel _ _ _ _ _ _ _ _ _ _ (inl _) (inl _))) =>
  apply RelGoal_pushTSPostRel_inl : refines.


Polymorphic Lemma RelGoal_pushTSPostRel_inr E1 E2 Γ1 Γ2 frame1 A2 B2
            (post : A2 -> B2 -> Prop)
            (postEq : forall call1', A2 -> FrameCallRet frame1 call1' -> B2 -> Prop)
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            e1 e2 r1 r2 :
  RelGoal (RPost e1 e2 r1 r2) ->
  RelGoal (@pushTSPostRel E1 E2 Γ1 Γ2 frame1 A2 B2
                             post postEq RPost (inr e1) (inr e2) r1 r2).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushTSPostRel _ _ _ _ _ _ _ _ _ _ (inr _) (inr _))) =>
  apply RelGoal_pushTSPostRel_inr : refines.


(** Refinement hints using IntroArg and RelGoal **)

(* Ret |= Ret *)
Definition spec_refines_ret_IntroArg E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR r1 r2 :
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
  unshelve (simple eapply spec_refines_exists_r); [shelve|] : refines.
#[global] Hint Extern 102 (spec_refines _ _ _ (ForallS _ >>= _) _) =>
  unshelve (simple eapply spec_refines_forall_l); [shelve|] : refines.


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
