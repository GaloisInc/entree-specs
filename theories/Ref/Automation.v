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
Admitted.


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
Proof. simpl; rewrite bind_bind; eauto. Qed.


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
  intros Hwf Ha2 Hca HPost.
Admitted.


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

Definition spec_refines_ret_IntroArg E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR r1 r2 :
  (RelGoal (RR r1 r2 : Prop)) ->
  @spec_refines E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR (RetS r1) (RetS r2) :=
  spec_refines_ret E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR r1 r2.

#[global] Hint Extern 102 (spec_refines _ _ _ (Ret _) (Ret _)) =>
  apply spec_refines_ret_IntroArg : refines.
