From Coq Require Import
     Program
     Setoid
     Morphisms
     Relations
     Logic.FunctionalExtensionality
.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Monad
     Basics.Tacs
     Basics.HeterogeneousRelations
     Eq.Paco2.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Core.SubEvent
     Eq.Eqit
.

Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.

Require Import ITree.Basics.Basics.

Require Export TypedVar MrecMonad.

From Equations Require Import Equations Signature.


Section interp_mtree_match.
Context (MR : mrec_ctx) (In : Type) (Out : EncodedType In) (x : var (In && Out) MR).
Context (body : forall i : In, mtree MR (encodes i)).

Lemma interp_mtree_ret (R : Type) (r : R) : interp_mtree MR In Out x body (ret r) ≅ ret r.
Proof. 
  pstep. red. cbn. constructor. auto.
Qed.

Lemma interp_mtree_tau (R : Type) (m : mtree MR R) : interp_mtree MR In Out x body (Tau m) ≅
                                                                 Tau (interp_mtree MR In Out x body m).
Proof.
  pstep. red. cbn. constructor. left. apply Reflexive_eqit. auto.
Qed.

Lemma observe_interp_mtree_vis R e (k : _ -> mtree MR R) :
  observe (interp_mtree MR In Out x body (Vis e k)) =
               match bring_to_front MR x e with
               | inl i && f => TauF (interp_mtree MR In Out x body ((EnTree.bind (body i) (fun x => k (f x)) )))
               | inr e' && f => VisF e' (fun x0 : encodes e' => interp_mtree MR In Out x body ((k (f x0))))
               end.
Proof.
  destruct (bring_to_front MR x e)  eqn : Heq.
  destruct x0; simpl; setoid_rewrite Heq; auto.
Qed.

Lemma interp_mtree_vis R e (k : _ -> mtree MR R) :
  interp_mtree MR In Out x body (Vis e k) ≅
               match bring_to_front MR x e with
               | inl i && f  => Tau (interp_mtree MR In Out x body ((EnTree.bind (body i) (fun x => k (f x)))))
               | inr e' && f => Vis e' (fun x0 : encodes e' => interp_mtree MR In Out x body ((k (f x0))))
               end.
Proof.
  specialize (observe_interp_mtree_vis R e k) as H. symmetry in  H. apply simpobs in H.
  rewrite <- H.
  destruct (bring_to_front MR x e); destruct x0; reflexivity. 
Qed.
      
End interp_mtree_match.

Section interp_mtree_proper.

Context (MR : mrec_ctx) (In : Type) (Out : EncodedType In) (x : var (In && Out) MR).
Context (body1 body2 : forall i : In, mtree MR (encodes i)).
Context (b1 b2 : bool).
Context (Hbody : forall i, eqit eq b1 b2 (body1 i) (body2 i)).

Theorem interp_mtree_proper  (R : Type): forall (m1 m2 : mtree MR R),
  eqit eq b1 b2 m1 m2 -> eqit eq b1 b2 (interp_mtree MR In Out x body1 m1) (interp_mtree MR In Out x body2 m2).
Proof.
  ginit. gcofix CIH. intros m1 m2 Hm12.
  punfold Hm12.
  red in Hm12. genobs m1 om1. genobs m2 om2. 
  hinduction Hm12 before r; intros; subst; pclearbot.
  - gstep. red. unfold observe. simpl. setoid_rewrite <- Heqom1. setoid_rewrite <- Heqom2.
    constructor. auto.
  - gstep. red. unfold observe. simpl. setoid_rewrite <- Heqom1. setoid_rewrite <- Heqom2.
    constructor. gfinal. left. eauto.
  - unfold interp_mtree. rewrite <- Heqom1. rewrite <- Heqom2. 
    gstep. red. setoid_rewrite observe_interp_mtree_vis. 
    destruct (bring_to_front MR x e). destruct x0.
    + constructor. gfinal. left. eapply CIH. eapply eqit_bind. apply Hbody.
      intros. subst. apply REL.
    + constructor. gfinal. left. eapply CIH. apply REL.
  - unfold interp_mtree at 1. rewrite <- Heqom1. setoid_rewrite interp_mtree_tau.
    inv CHECK. destruct b2;
    rewrite tau_euttge; eauto. 
  - unfold interp_mtree at 2. rewrite <- Heqom2. setoid_rewrite interp_mtree_tau.
    inv CHECK. destruct b1; rewrite tau_euttge; eauto.
Qed.

End interp_mtree_proper.



Definition ptwise {A : Type} {B : A -> Type} : (forall (a : A), relation (B a)) -> relation (forall (a : A), B a) :=
  fun R (f g : forall a, B a) => forall a, (R a (f a) (g a) ).

#[global] Instance interp_mtree_proper_inst R (MR : mrec_ctx) (In : Type) (Out : EncodedType In) (x : var (In && Out) MR) (b1 b2 : bool) :
  Proper (ptwise (fun i => eqit (@eq (encodes i)) b1 b2 ) ==> eqit eq b1 b2 ==> eqit (@eq R) b1 b2 ) (@interp_mtree MR In Out x R).
Proof.
  repeat intro. eapply interp_mtree_proper; eauto.
Qed.

#[global] Instance interp_mtree_proper_inst' R (MR : mrec_ctx) (In : Type) (Out : EncodedType In) (x : var (In && Out) MR) (b1 b2 : bool) :
  Proper (eq ==> eqit eq b1 b2 ==> eqit (@eq R) b1 b2 ) (@interp_mtree MR In Out x R).
Proof.
  repeat intro. eapply interp_mtree_proper; eauto. subst. intros. reflexivity.
Qed.

Section interp_mtree_bind.
Context (MR : mrec_ctx) (In : Type) (Out : EncodedType In) (x : var (In && Out) MR).
Context (body : forall i : In, mtree MR (encodes i)).

Lemma interp_mtree_bind (R S : Type) (m : mtree _ R) (k : R -> mtree _ S) : 
  interp_mtree MR In Out x body (bind m k) ≅
               bind (interp_mtree MR In Out x body m) 
               (fun y => interp_mtree MR In Out x body (k y)).
Proof.
  ginit. revert m. gcofix CIH. intros.
  destruct (observe m) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  -  rewrite <- Heq. setoid_rewrite bind_ret_l. apply Reflexive_eqit_gen. auto.
  - rewrite <- Heq. unfold bind. cbn. rewrite bind_tau. 
    repeat rewrite interp_mtree_tau. rewrite bind_tau. gstep. constructor.
    gfinal. left. eapply CIH.
  - rewrite <- Heq. unfold bind. cbn. rewrite bind_vis.
    repeat rewrite interp_mtree_vis. destruct (bring_to_front MR x e).
    destruct x0.
    + rewrite bind_tau. gstep. constructor. rewrite <- bind_bind. 
      gfinal. left. eapply CIH.
    + rewrite bind_vis. gstep. constructor. intros. red.
      gfinal. left. eapply CIH.
Qed.

End interp_mtree_bind.


Lemma JMeq_comp (A B : Type) (f : A -> B) (g : B -> A) : 
  B = A ->
  f ~= @id B -> g ~= @id A ->
  forall a, g (f a) = a.
Proof.
  intros. subst. auto.
Qed.
Lemma JMeq_comp' (A B C : Type) (f : A -> B) (g : C -> B) (h : C -> A) :
  A = B -> B = C ->   f ~= @id B -> g ~= @id B -> h ~= @id A -> 
  forall c, (f (h c) =  g c).
Proof.
  intros. subst. auto.
Qed.
(*
Lemma JMeq_comp' (A B C : Type) (f : A -> B) (g : C -> B) (h : ) :
  A = B -> B = C ->   f ~= @id B -> g ~= @id A -> h ~= @id C -> 
  forall a, ()
*)
 Section interp_mtree_callm.
Context (MR : mrec_ctx) (In : Type) (Out : EncodedType In) (x : var (In && Out) MR).
Context (body : forall i : In, mtree MR (encodes i)).

Lemma interp_mtree_callm (v : In) : interp_mtree MR In Out x body (callm x v) ≈ interp_mtree MR In Out x body (body v).
Proof.
  unfold callm.
  specialize (bring_to_front_call x v) as Hcall1.
  specialize (call_cont x v) as Hcall2.
  specialize (bring_to_front_cont x (projT1 (call x v))) as Hcall3.
  specialize (encodes_positions x (projT1 (call x v) ) v (call_position x v)) as Henc.
  destruct (call x v). setoid_rewrite bind_trigger.
  rewrite interp_mtree_vis. cbn in *. 
  destruct (bring_to_front MR x x0). cbn in *. subst.
  rewrite tau_eutt. setoid_rewrite interp_mtree_bind.
  setoid_rewrite interp_mtree_ret. setoid_rewrite <- bind_ret_r at 5.
  eapply eqit_bind. reflexivity.
  intros. subst. rewrite JMeq_comp; auto. reflexivity.
Qed.

Context (T1 : Type) (T2 : EncodedType T1) (y : var (T1 && T2) MR).
Lemma interp_mtree_callm_neq (v : T1) (Hneq : var_neq x y) : 
                                        interp_mtree MR In Out x body (callm y v) ≈
                                                     callm (remove_var _ _ _ x y Hneq) v.
Proof.
  unfold callm.
  specialize (bring_to_front_call_neq x y Hneq v) as Hcall1.
  specialize (call_cont y v) as Hcall2.
  specialize (bring_to_front_cont x (projT1 (call y v))) as Hcall3.
  specialize (call_cont ((remove_var (In && Out) (T1 && T2) MR x y Hneq)) v ) as Hcall4.
  specialize (encodes_positions y (projT1 (call y v) ) v (call_position y v)) as Henc.
  assert (Henc' : encodes v = 
           encodes (projT1 (call (remove_var (In && Out) (T1 && T2) MR x y Hneq) v))).
  { eapply encodes_positions. eapply call_position. }
  destruct (call y v). cbn in *.
  destruct (call (remove_var (In && Out) (T1 && T2) MR x y Hneq) v).
  setoid_rewrite bind_trigger.
  rewrite interp_mtree_vis. destruct (bring_to_front MR x x0).
  cbn in *. subst. pstep. constructor. left. setoid_rewrite interp_mtree_ret.
  cbn in *. pstep. constructor. apply JMeq_comp'; eauto.
Qed.

(* reason about remove_var, call and bring_to_front *)

End interp_mtree_callm.
