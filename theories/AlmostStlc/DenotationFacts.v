Require Export MrecMonad.
Require Export HeterogeneousRelations.
Require Export EnTreeDefinition.
Require Export Syntax.
Require Export Denotation.
From Coq Require Import Lists.List Logic.JMeq Eqdep CRelationClasses.

Require Export MapEFacts.
Require Export InterpMTreeFacts.
Require Export Eq.Eqit.
From Equations Require Import Equations Signature.
Require Import Coq.Program.Equality.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Lemma remove_denote_encodes R MR (x : var R MR)
      (d : denote_mrec_ctx
         (remove (denote_call_frame R && encodes_call_frame R) (denote_mfix_ctx MR) (denote_var x))) :
  encodes d = encodes (projT1 (remove_denote x d) ).
Proof.
  dependent induction x.
  - Transparent remove_denote. simpl in *. Opaque remove_denote. auto.
  - Transparent remove_denote. simpl in *. Opaque remove_denote. 
    destruct d. auto. 
    specialize (IHx d). destruct (remove_denote x d). auto.
Qed.

Lemma remove_denote_cont R MR (x : var R MR)
      (d : denote_mrec_ctx
         (remove (denote_call_frame R && encodes_call_frame R) (denote_mfix_ctx MR) (denote_var x))) : 
  projT2 (remove_denote x d) ~= @id (encodes d).
Proof.
  dependent induction x.
  - Transparent remove_denote. simpl in *. Opaque remove_denote. auto.
  - Transparent remove_denote. simpl in *. Opaque remove_denote.
    destruct d. auto. specialize (IHx d). destruct (remove_denote x d).
    auto.
Qed.

Lemma remove_denote'_encodes R MR (x : var R MR)
                                 (d : denote_mrec_ctx (denote_mfix_ctx (remove R MR x))) : 
  encodes d = encodes (projT1 (remove_denote' x d)).
Proof.
  dependent induction x.
  - Transparent remove_denote'. simpl in *. Opaque remove_denote'. auto.
  - Transparent remove_denote'. simpl in *. Opaque remove_denote'. 
    destruct d. auto. 
    specialize (IHx d). destruct (remove_denote' x d). auto.
Qed.

Lemma remove_denote'_cont R MR (x : var R MR)
                                 (d : denote_mrec_ctx (denote_mfix_ctx (remove R MR x))) : 
  projT2 (remove_denote' x d) ~= @id (encodes d).
Proof.
  dependent induction x.
  - Transparent remove_denote'. simpl in *. Opaque remove_denote'. auto.
  - Transparent remove_denote'. simpl in *. Opaque remove_denote'. 
    destruct d. auto. 
    specialize (IHx d). destruct (remove_denote' x d). auto.
Qed.

Lemma call_mrec_call_frame_encodes t1 t2 R  (x : var (t1,t2) R) (c : denote_type t1) : 
  encodes (projT1 (call_mrec_call_frame x c)) = denote_type t2.
Proof.
  dependent induction x.
  - simp call_mrec_call_frame. auto.
  - destruct b. simp call_mrec_call_frame.
    specialize (IHx t1 t2 x eq_refl JMeq_refl c).
    destruct (call_mrec_call_frame x c) eqn : Heq. auto.
Qed.

Lemma call_mrec_call_frame_cont t1 t2 R  (x : var (t1,t2) R) (c : denote_type t1) : 
  projT2 (call_mrec_call_frame x c) ~= @id (denote_type t2).
Proof.
  dependent induction x.
  - simp call_mrec_call_frame. auto.
  - destruct b. simp call_mrec_call_frame.
    specialize (IHx t1 t2 x eq_refl JMeq_refl c).
    destruct (call_mrec_call_frame x c) eqn : Heq.
    auto.
Qed.
(*do I need a bring_to_front proof? *)

Lemma call_mrec_encodes t1 t2 R MR (xt : var (t1,t2) R) (xR : var R MR) (c : denote_type t1) :
  encodes (projT1 (call_mrec xt xR c)) = denote_type t2.
Proof.
  dependent induction xR.
  - simp call_mrec.
    specialize (call_mrec_call_frame_encodes t1 t2 _ xt c) as H.
    destruct (call_mrec_call_frame xt c). auto.
  - simp call_mrec. specialize (IHxR xt c).
    destruct (call_mrec xt xR c). auto.
Qed.

Lemma call_mrec_cont t1 t2 R MR (xt : var (t1,t2) R) (xR : var R MR) (c : denote_type t1) :
  projT2 (call_mrec xt xR c) ~= @id (denote_type t2).
Proof.
  dependent induction xR.
  - simp call_mrec.
    specialize (call_mrec_call_frame_cont t1 t2 _ xt c) as H.
    destruct (call_mrec_call_frame xt c). auto.
  - specialize (IHxR xt c). simp call_mrec.
    destruct (call_mrec xt xR). auto.
Qed.

Lemma bring_to_front_call_mrec t1 t2 (R : call_frame) (MR : mfix_ctx)
      (v : denote_type t1) (xt : var (t1,t2) R) (xR : var R MR) : 
  projT1 (bring_to_front _ (denote_var xR) (projT1 (call_mrec xt xR v))) =
                 inl (projT1 (call_mrec_call_frame xt v)).
Proof.
  dependent induction xR.
  - simp call_mrec. simp denote_var.
    destruct (call_mrec_call_frame xt v).
    simpl projT1. simp bring_to_front. cbn. simp bring_to_front. auto. 
  - specialize (IHxR xt). simp denote_var. 
    simp call_mrec. destruct (call_mrec xt xR v). simpl projT1.
    cbn in IHxR. cbn. simp bring_to_front.
    destruct (bring_to_front (denote_mfix_ctx l) (denote_var xR) x). cbn in IHxR. subst.
    auto.
Qed.

Lemma bring_to_front_call_mrec_neq t1 t2 (R1 R2  : call_frame) (MR : mfix_ctx)
      (v : denote_type t1) (xt : var (t1,t2) R1) (xR : var R1 MR) (yR : var R2 MR) (Hneq : var_neq xR yR) : 
  projT1 (bring_to_front _ (denote_var yR) (projT1 (call_mrec xt xR v))) =
    inr (projT1 (remove_denote' yR (projT1 (call_mrec xt (remove_var R2 R1 MR yR xR (var_neq_sym xR yR Hneq)) v)))).
Proof.
  dependent induction Hneq.
  - simp var_neq_sym.
    Transparent remove_var. simpl remove_var. Opaque remove_var.
    Transparent call_mrec. simpl call_mrec. Opaque call_mrec.
    destruct (call_mrec_call_frame xt v) eqn : Hc.
    simpl projT1. Transparent remove_denote'. simpl remove_denote'. Opaque remove_denote'.
    Transparent denote_var. simpl denote_var. Opaque denote_var.
    simp bring_to_front. cbn. simp bring_to_front. auto. 
  - simp var_neq_sym.
    Transparent remove_var. simpl remove_var. Opaque remove_var.
    Transparent call_mrec. simpl call_mrec. Opaque call_mrec.
    Transparent denote_var. simpl denote_var. Opaque denote_var.
    destruct (call_mrec xt x v) eqn : Hc. simpl projT1.
    setoid_rewrite bring_to_front_equation_3. cbn.
    Transparent remove_denote'. simpl remove_denote'. Opaque remove_denote'.
    cbn. match goal with |- _ =  inr (projT1 ?cm) => destruct cm eqn : Hc' end.
    cbn. Transparent TypedVar.remove. cbn in Hc'. Opaque TypedVar.remove.
    rewrite Hc in Hc'. injection Hc'. intros. subst. auto.
  - specialize (IHHneq xt). simp var_neq_sym. simp remove_var.
    simp call_mrec. Transparent denote_var. simpl denote_var. Opaque denote_var.
    Transparent remove_var. simpl remove_var. Opaque remove_var.
    Transparent remove_denote'. simpl remove_denote'. Opaque remove_denote'.
    destruct (call_mrec xt x v) eqn : Hc. simpl projT1 in *.
    Transparent call_mrec. simpl call_mrec. Opaque call_mrec.
    destruct (call_mrec xt (remove_var b a l y x (var_neq_sym x y Hneq)) v) eqn : Hc'.
    simpl projT1 in *.
    destruct (remove_denote' y x1) eqn : Hc''. simpl projT1 in *.
    simp bring_to_front. cbn. simp bring_to_front.
    destruct (bring_to_front (denote_mfix_ctx l) (denote_var y) x0). cbn in IHHneq. subst.
    auto.
Qed.

(* write lemmas for the continuations, saying the types work out and the functions 
   are identity 
   have a var_neq 
*)

(* need lemmas about denote_bodies and call_mrec_call_frame
   might need some more reasoning about mfix bodies and var

 *)

#[global] Instance valid_remove_denote R MR (xR : var R MR) : valid_handler (remove_denote xR).
Proof.
  intros d1. dependent induction xR.
  - Transparent remove_denote. cbn. Opaque remove_denote. auto.
  - Transparent remove_denote. cbn. Opaque remove_denote. auto.
    destruct d1.
    + cbn. auto.
    + specialize (IHxR d). destruct (remove_denote xR d). auto.
Qed.

(* need to fmap the typecast *)
Lemma denote_mfix t1 t2 (R : call_frame) (MR : mfix_ctx) (xt : var (t1,t2) R) (xR : var R MR) (v : denote_type t1) f :
  let '(d && g) := call_mrec_call_frame xt v in
  mapE (remove_denote xR) (interp_mtree (denote_var xR) f (call_term xt xR v)) ≈
       mapE (remove_denote xR) (interp_mtree (denote_var xR) f (Functor.fmap g (f d))).
Proof.
  destruct (call_mrec_call_frame xt v) eqn : Hcall1. unfold call_term.
  destruct (call_mrec xt xR v) eqn : Hcall2. setoid_rewrite interp_mtree_bind at 1.
  setoid_rewrite interp_mtree_ret. specialize (bring_to_front_call_mrec _ _ R MR v xt xR) as Hbtf. 
  rewrite Hcall2 in Hbtf. rewrite Hcall1 in Hbtf. cbn in Hbtf.
  setoid_rewrite interp_mtree_vis. destruct (bring_to_front (denote_mfix_ctx MR) (denote_var xR) x0) eqn : Hb.
  cbn in Hbtf. subst. rewrite tau_eutt. setoid_rewrite interp_mtree_bind at 1. setoid_rewrite bind_bind.
  setoid_rewrite interp_mtree_bind. setoid_rewrite interp_mtree_ret.
  eapply mapE_proper_inst. apply valid_handler_self_eq. apply valid_remove_denote.
  setoid_rewrite bind_ret_l. eapply eqit_bind. reflexivity.
  intros. subst. apply eqit_Ret. cbn in e. 
  eapply JMeq_comp'; eauto.
  - specialize (call_mrec_encodes t1 t2 R MR xt xR v) as H.
    rewrite Hcall2 in H. auto.
  - specialize (call_mrec_call_frame_encodes t1 t2 R xt v) as H.
    rewrite Hcall1 in H. cbn in H. auto.
  - specialize (call_mrec_cont t1 t2 R MR xt xR v) as H.
    rewrite Hcall2 in H. auto.
  - specialize (call_mrec_call_frame_cont t1 t2 R xt v) as H. 
    rewrite Hcall1 in H. auto.
  - specialize (bring_to_front_cont (denote_var xR) x0 ) as H. 
    rewrite Hb in H. auto.
Qed.
(* need to figure this out *)

Lemma remove_denote_remove_denote'_projT1:
  forall (R2 : call_frame) (MR : mfix_ctx) (yR : var R2 MR)
    (x0 : denote_mrec_ctx (denote_mfix_ctx (remove R2 MR yR))),
    projT1 (remove_denote yR (projT1 (remove_denote' yR x0))) = x0.
Proof.
  intros R2 MR yR x0.
  dependent induction yR.
  - Transparent remove_denote'. cbn. Transparent remove_denote. cbn.
    Opaque remove_denote'. Opaque remove_denote. auto.
  - Transparent remove_denote'. cbn. Transparent remove_denote. cbn.
    Opaque remove_denote'. Opaque remove_denote.
    destruct x0.
    + cbn. auto.
    + cbn. specialize (IHyR d).
      destruct (remove_denote' yR d). simpl.
      simpl in IHyR. destruct (remove_denote yR x). cbn in *. subst. auto.
Qed.

Lemma JMeq_comp'':
  forall (A B C D : Type)
    (d : C -> D)
    (d0 : A -> D)
    (e : B -> C)
    (e0 : A -> B) (a : A),
    A = B -> B = C -> C = D -> d ~= @id D -> d0 ~= @id D -> e ~= @id C -> e0 ~= @id B -> d (e (e0 a)) = d0 a.
Proof.
  intros. subst. auto.
Qed.

Lemma denote_mfix_neq t1 t2 (R1 R2 : call_frame) (MR : mfix_ctx) (xt : var (t1,t2) R1) (xR : var R1 MR)
      (yR : var R2 MR) (Hneq : var_neq xR yR) (v : denote_type t1) f :
  mapE (remove_denote yR) (interp_mtree (denote_var yR) f (call_term xt xR v)) ≈
       call_term xt (remove_var R2 R1 MR yR xR (var_neq_sym xR yR Hneq)) v.
Proof.
  unfold call_term.
  specialize (bring_to_front_call_mrec_neq t1 t2 R1 R2 MR v xt xR yR Hneq) as H. 
  destruct (call_mrec xt xR v) eqn : Hcall1.
  destruct (call_mrec xt (remove_var R2 R1 MR yR xR (var_neq_sym xR yR Hneq)) v) eqn :  Hcall2.
  setoid_rewrite interp_mtree_bind. setoid_rewrite interp_mtree_vis.
  setoid_rewrite interp_mtree_ret.
  cbn in H. destruct (bring_to_front (denote_mfix_ctx MR) (denote_var yR) x )
                     eqn : Heq.
  cbn in H. subst. 
  rewrite mapE_bind; try apply valid_remove_denote.
  rewrite mapE_vis. 
  specialize (remove_denote_remove_denote'_projT1 R2 MR yR x0) as Hx0.
  destruct (remove_denote yR (projT1 (remove_denote' yR x0))) eqn : Heq'. simpl in Hx0. subst.
  setoid_rewrite bind_vis. apply eqit_Vis. intros.
  setoid_rewrite bind_ret_l. rewrite mapE_ret. apply eqit_Ret.
  specialize (call_mrec_cont t1 t2 R1 MR xt xR v) as Hcont1.
  rewrite Hcall1 in Hcont1. cbn in Hcont1.
  specialize (call_mrec_cont t1 t2 _ _ xt 
                             (remove_var R2 R1 MR yR xR (var_neq_sym xR yR Hneq)) v ) as Hcont2.
  rewrite Hcall2 in Hcont2. cbn in Hcont2.
  cbn in Heq. specialize (bring_to_front_cont (denote_var yR) x) as Hcont3.
  rewrite Heq in Hcont3. cbn in Hcont3. 
  specialize (remove_denote_cont _ _ yR (projT1 (remove_denote' yR x0))) as Hcont4.
  rewrite Heq' in Hcont4. cbn in Hcont4.
  eapply JMeq_comp''; eauto.
  - apply remove_denote'_encodes.
  - setoid_rewrite <- remove_denote'_encodes.
    specialize (call_mrec_encodes t1 t2 _ _ xt xR v) as Henc.
    rewrite Hcall1 in Henc. cbn in Henc. rewrite Henc.
    specialize (call_mrec_encodes t1 t2 _ _ xt (remove_var R2 R1 MR yR xR (var_neq_sym xR yR Hneq)) v)
     as Henc'. rewrite Hcall2 in Henc'. cbn in *. rewrite Henc'. auto.
  - specialize (call_mrec_encodes t1 t2 _ _ xt xR v) as Henc.
    rewrite <- Henc. rewrite Hcall1. auto.
Qed.
