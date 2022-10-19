From Coq Require Export
     Morphisms
     Setoid
     Program.Equality
     Lists.List
.

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


(** Refinement rules for recursion **)

(* The bind of one recursive call refines the bind of another if the recursive
   calls are in the current RPre and, for all return values for them in RPost,
   the bind continuations refine each other *)
Lemma spec_refines_call_bind (E1 E2 : EvType) Γ1 Γ2 frame1 frame2 R1 R2
      (RPre : SpecPreRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (RPost : SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      RR (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (k1 : FrameCallOut frame1 call1 -> SpecM E1 (frame1 :: Γ1) R1)
      (k2 : FrameCallOut frame2 call2 -> SpecM E2 (frame2 :: Γ2) R2) :
  RPre (inl call1) (inl call2) ->
  (forall r1 r2,
      RPost (inl call1) (inl call2) r1 r2 ->
      spec_refines RPre RPost RR (k1 (resum_ret call1 r1)) (k2 (resum_ret call2 r2))) ->
  spec_refines RPre RPost RR (CallS _ _ _ call1 >>= k1) (CallS _ _ _ call2 >>= k2).
Admitted.

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
      (k1 : FrameCallOut frame1 call1 -> SpecM E1 Γ1 R1)
      (k2 : FrameCallOut frame2 call2 -> SpecM E2 Γ2 R2)
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
Admitted.

(* Build a RecFrame with a single, unary function *)
Definition unary1Frame (A B : Type) : RecFrame :=
  cons (LRT_Fun A (fun _ => LRT_Ret B)) nil.

(* Repeat a specification n times *)
Fixpoint trepeat {E Γ R} (n : nat) (s : SpecM E Γ R) : SpecM E Γ unit :=
  match n with
  | 0 => Ret tt
  | S m => s;; trepeat m s
  end.

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
               | inl args1, inl (inl (existT _ a2 _)) =>
                 pre a2 /\ preEq args1 a2
               | inr ev1, inr ev2 => RPre ev1 ev2
               | _, _ => False
               end.

(* Add a postcondition relation for proving total_spec refinement *)
Definition pushTSPostRel {E1 E2 : EvType} {Γ1 Γ2 frame1 A2 B2}
           (post : A2 -> B2 -> Prop)
           (postEq : forall call1', A2 -> FrameCallOut frame1 call1' -> B2 -> Prop)
           (RPost : SpecPostRel E1 E2 Γ1 Γ2) :
  SpecPostRel E1 E2 (frame1 :: Γ1) (unary1Frame A2 B2 :: Γ2) :=
  fun a1 a2 => match a1,a2 return encodes a1 -> encodes a2 -> Prop with
               | inl args1, inl (inl (existT _ a2 _)) =>
                 fun r1 b2 => post a2 b2 /\ postEq args1 a2 r1 b2
               | inr a1', inr a2' => RPost a1' a2'
               | _, _ => fun _ _ => False
               end.

Lemma spec_refines_total_spec (E1 E2 : EvType) Γ1 Γ2 frame1
      A2 B2 `{QuantType A2} `{QuantType B2}
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (call1 : FrameCall frame1) (a2 : A2)
      (RR : Rel (FrameCallOut frame1 call1) B2)
      (preEq : Rel (FrameCall frame1) A2)
      (postEq : forall call1' a2', FrameCallOut frame1 call1' -> B2 -> Prop)
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
Admitted.
