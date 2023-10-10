Require Export TypedVar.
Require Export SyntaxSeq.
Require Export SmallStepSeq.
Require Export DenotationFacts.
Require Export DenotationSeq.
Require Export TypesEquiv.
Require Export MapEFacts.
Import List.ListNotations.
Open Scope list_scope.
From Equations Require Import Equations Signature.
Require Import Coq.Program.Equality.
Require Import ExtLib.Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.


Lemma call_extract (MR : mfix_ctx) (d : denote_mrec_ctx (denote_mfix_ctx MR)) : 
  exists R (xR : var R MR) t1 t2 (x : var (t1,t2) R)  (vin : denote_type t1),
    projT1 (call_mrec x xR vin) = d.
Proof.
  revert d. induction MR.
  intros [].
  rename a into R. intros [dR | dMR].
  - exists R, VarZ. clear IHMR. induction R.
    inversion dR. destruct a as [tin tout].
    destruct dR as [vvin | ?].
    + exists tin, tout, VarZ, vvin. simp call_mrec. rewrite call_mrec_call_frame_equation_1. auto.
    + specialize (IHR d). destruct IHR as [t1 [t2 [x [vin H] ]] ].
      simp call_mrec in H.
      exists t1,t2, (VarS x), vin. simp call_mrec. rewrite call_mrec_call_frame_equation_2.
      destruct (call_mrec_call_frame x vin). cbn in *. injection H. intros. subst. auto.
  - specialize (IHMR dMR). destruct IHMR as [R' [xR [t1 [t2 [x [vin H]]]]]].
    exists R', (VarS xR), t1, t2, x, vin. simp call_mrec. destruct (call_mrec x xR vin).
    cbn in H. subst. auto.
Qed.

Lemma JMeq_id_comp:
  forall A B C
    (e : A -> B) 
    (e0 : C -> A), 
    A = B -> B = C ->
    e ~= (@id B) -> e0 ~= (@id A) -> (fun x => e (e0 x)) ~= (@id B).
Proof.
  intros. subst. auto.
Qed.

Lemma valid_perm_handler_aux1:
  forall (MR1 MR2 : mrec_ctx) (Hperm : perm MR1 MR2) (d1 : denote_mrec_ctx MR1),
    encodes d1 = encodes (projT1 (perm_handler MR1 MR2 Hperm d1)).
Proof.
  intros MR1 MR2 Hperm. 
  dependent induction Hperm; intros.
  + inversion d1.
  + destruct x as [T1 T2]. destruct d1 as [d1 | d1]; simp perm_handler.
    auto. cbn. specialize (IHHperm d1).
    destruct (perm_handler l1 l2 Hperm d1). auto.
  + destruct x as [T1 T2]. destruct y as [T3 T4].
    destruct d1 as [d1 | [d1 | d1] ]; simp perm_handler; auto.
    cbn. specialize (IHHperm d1). destruct (perm_handler l1 l2 Hperm d1). auto.
  + destruct l1; destruct l3; try (inversion d1; fail; auto).
    * exfalso. eapply perm_nil_cons2'. eapply perm_trans; eauto.
    * destruct s as [T1 T2]. destruct s0 as [T3 T4].
      destruct d1 as [d1 | d1]; simp perm_handler.
      -- specialize (IHHperm1 (inl d1)). 
         destruct (perm_handler (T1 && T2 :: l1) l2 Hperm1 (inl d1)) eqn : Heq1.
         setoid_rewrite Heq1.
         specialize (IHHperm2 ( x)).
         destruct (perm_handler l2 (T3 && T4 :: l3) Hperm2 x) eqn : Heq2.
         cbn in *. subst. destruct x0; auto.
         rewrite IHHperm1. auto. rewrite IHHperm1.
         auto.
      -- specialize (IHHperm1 (inr d1)). 
         destruct (perm_handler (T1 && T2 :: l1) l2 Hperm1 (inr d1)) eqn : Heq1.
         specialize (IHHperm2 ( x)).
         destruct (perm_handler l2 (T3 && T4 :: l3) Hperm2 x) eqn : Heq2.
         cbn in *. subst. destruct x0; auto.
         rewrite IHHperm1. auto. rewrite IHHperm1.
         auto.
Qed.

#[global] Instance valid_perm_handler MR1 MR2 (Hperm : perm MR1 MR2) :
  valid_handler (perm_handler _ _ Hperm).
Proof.
  red. intros; split.
  - apply valid_perm_handler_aux1; auto.
  - generalize dependent d1. dependent induction Hperm; intros.
    + inversion d1.
    + destruct x as [T1 T2]. destruct d1 as [d1 | d1]; simp perm_handler.
      auto. cbn. specialize (IHHperm d1).
      destruct (perm_handler l1 l2 Hperm d1). auto.
    + destruct x as [T1 T2]. destruct y as [T3 T4].
      destruct d1 as [d1 | [d1 | d1] ]; simp perm_handler; auto.
      cbn. specialize (IHHperm d1). destruct (perm_handler l1 l2 Hperm d1). auto.
    + destruct l1; destruct l3; try (inversion d1; fail; auto).
      * exfalso. eapply perm_nil_cons2'. eapply perm_trans; eauto.
      * destruct s as [T1 T2]. destruct s0 as [T3 T4].
        destruct d1 as [d1 | d1]; simp perm_handler.
        -- specialize (IHHperm1 (inl d1)). 
           match goal with |- projT2 (let 'd2 && f12 := ?x in _ ) ~= id =>
                             destruct x eqn : Heq1 end.
           match goal with | H : projT2 ?x ~= _ |- _ => destruct x eqn : Heq1' end.
           setoid_rewrite Heq1' in Heq1. injection Heq1. intros. subst.
           inj_existT. subst.
           match goal with |- projT2 (let 'd2 && f12 := ?x in _ ) ~= id =>
                             destruct x eqn : Heq2 end.
           specialize (IHHperm2 x).
           match goal with | H : projT2 ?x ~= _ |- _ => destruct x eqn : Heq2' end.
           injection Heq2. intros. subst. inj_existT. subst.
           cbn in IHHperm1, IHHperm2. simpl.
           cbn. cbn in *.
           eapply JMeq_id_comp; eauto.
           specialize (valid_perm_handler_aux1 _ _ Hperm1 (inl d1)) as Hd1.
           rewrite Heq1' in Hd1. auto.
           specialize (valid_perm_handler_aux1 _ _ Hperm2 x) as Hx.
           rewrite Heq2' in Hx. cbn in Hx. setoid_rewrite <- Hx.
           specialize (valid_perm_handler_aux1 _ _ Hperm1 (inl d1)) as Hd1.
           rewrite Heq1' in Hd1. auto.
       -- specialize (IHHperm1 (inr d1)). 
           match goal with |- projT2 (let 'd2 && f12 := ?x in _ ) ~= id =>
                             destruct x eqn : Heq1 end.
           match goal with | H : projT2 ?x ~= _ |- _ => destruct x eqn : Heq1' end.
           injection Heq1'. intros. subst.
           inj_existT. subst.
           match goal with |- projT2 (let 'd2 && f12 := ?x in _ ) ~= id =>
                             destruct x eqn : Heq2 end.
           specialize (IHHperm2 x0).
           match goal with | H : projT2 ?x ~= _ |- _ => destruct x eqn : Heq2' end.
           injection Heq2. intros. subst. inj_existT. subst.
           simpl. eapply JMeq_id_comp; eauto.
           specialize (valid_perm_handler_aux1 _ _ Hperm1 (inr d1)) as Hd1.
           rewrite Heq1 in Hd1. setoid_rewrite Hd1. auto.
           specialize (valid_perm_handler_aux1 _ _ Hperm1 (inr d1)) as Hd1.
           setoid_rewrite Hd1. setoid_rewrite Heq1. simpl.
           specialize (valid_perm_handler_aux1 _ _ Hperm2 x0) as Hx.
           rewrite Hx. rewrite Heq2'. auto.
Qed.

#[global] Instance valid_lift_handler MR1 MR2 :
  valid_handler (@lift_handler MR1 MR2).
Proof.
  split; intros.
  - induction MR1. simp lift_handler. auto.
    simp lift_handler. destruct (lift_handler MR1 d1).
    auto.
  - induction MR1. simp lift_handler. auto.
    simp lift_handler. destruct (lift_handler MR1 d1).
    auto.
Qed.

(* could be useful to relate these types 
   the relation could involve call_mrec
*)

(* this is ill typed and incorrect
Lemma call_mrec_cont_inv MR R t1 t2 : forall (xR : var R MR) (x : var (t1,t2) R) 
      (v : denote_type t1) d f,
    call_mrec x xR v = d && f ->
    f d = v.
*)

(* investigate if this is enough *)
Definition var_map_handler_rel {MR1 MR2 : mfix_ctx}
           (h : handler (denote_mrec_ctx (denote_mfix_ctx MR1)) 
                        (denote_mrec_ctx (denote_mfix_ctx MR2)))
           (vf : forall R, var R MR1 -> var R MR2) : Prop :=
  forall R t1 t2 (x : var (t1,t2) R) (xR : var R MR1 )(v : denote_type t1) d1 f1 d2 f2,
    call_mrec x xR v = (d1 && f1) ->
    h d1 = (d2 && f2) ->
    projT1 (call_mrec x (vf R xR) v) = d2.

Lemma mapE_perm_handler_call_term_aux:
  forall (t2 : vtype) (MR1 MR2 : mfix_ctx) (t0 : vtype) 
    (R : call_frame) (xR : var R MR1) (x : var (t0, t2) R) (r1 r2 : denote_type t0)
    h (vf : forall R, var R MR1 -> var R MR2),
    var_map_handler_rel h vf ->
    valid_handler h ->
    (mapE h (call_term x xR r1)) ≅ (call_term x (vf _ xR) r1).
Proof.
  unfold call_term. intros.
  destruct (call_mrec x xR r1) eqn : Heq1.
  destruct (call_mrec x (vf R xR) r1) eqn : Heq2.
  setoid_rewrite mapE_bind; auto.
  setoid_rewrite mapE_ret. setoid_rewrite bind_vis.
  setoid_rewrite mapE_vis. destruct (h x0) eqn : Heq3.
  specialize (H R t0 t2 x xR r1). eapply H in Heq3 as Heq4; eauto.
  rewrite Heq2 in Heq4. simpl in Heq4. subst.
  setoid_rewrite bind_vis. apply eqit_Vis.
  intros. setoid_rewrite bind_ret_l. apply eqit_Ret.
  specialize (call_mrec_encodes _ _ _ _ x (vf R xR) r1) as H1.
  rewrite Heq2 in H1.
  specialize (call_mrec_encodes _ _ _ _ x xR r1) as H2.
  rewrite Heq1 in H2. 
  specialize (call_mrec_cont _ _ _ _ x (vf R xR) r1) as H3.
  rewrite Heq2 in H3.
  specialize (call_mrec_cont _ _ _ _ x xR r1) as H4.
  rewrite Heq1 in H4. simpl in *.
  red in H0. specialize (H0 x0) as [H5 H6].
  rewrite Heq3 in H6.
  eapply JMeq_comp'; eauto.
Qed.

  

Arguments perm_handler {_ _}
.
Lemma perm_var_map_handler_rel MR1 MR2 (Hperm : perm MR1 MR2) : 
  var_map_handler_rel (perm_handler (perm_denote Hperm))
                      (fun _ x => perm_var x Hperm ).
Proof.
  red. dependent induction Hperm.
  - intros. inversion xR.
  - unfold perm_denote. Transparent perm_map. simpl perm_map.
    Opaque perm_map. intros.
    destruct d1 as [d1 | d1].
    + setoid_rewrite perm_handler_equation_5 in H0.
      injection H0. intros. subst. inj_existT. subst.
      dependent destruction xR.
      * simp perm_var. destruct (call_mrec x0 VarZ v) eqn : Heq1.
        match goal with |- projT1 ?t = _ => destruct t eqn : Heq2 end.
        simp call_mrec in Heq1. simp call_mrec in Heq2.
        destruct (call_mrec_call_frame x0 v).
        injection Heq1. injection Heq2. intros. subst. inj_existT.
        subst. injection H. intros. subst. auto.
      * simp call_mrec in H. destruct (call_mrec x0 xR v). discriminate.
   + setoid_rewrite perm_handler_equation_6 in H0.
     destruct (perm_handler (perm_map (perm_map Hperm)) d1) eqn : Heq1.
     dependent destruction xR.
     * simp call_mrec in H. destruct (call_mrec_call_frame x0 v); discriminate.
     * simp call_mrec in H. destruct (call_mrec x0 xR v) eqn : Heq2.
       setoid_rewrite Heq1 in H0.
       injection H. intros. subst. inj_existT. subst.
       simp perm_var. simp call_mrec.
       eapply IHHperm in Heq1; eauto. 
       destruct (call_mrec x0 (perm_var xR Hperm) v). simpl in *.
       subst. injection H0. auto.
  - unfold perm_denote. Transparent perm_map. simpl perm_map.
    Opaque perm_map. intros. destruct d1 as [d1 | [d1 | d1]].
    + setoid_rewrite perm_handler_equation_7 in H0. injection H0.
      intros. subst. inj_existT. subst. dependent destruction xR.
      2 : { simp call_mrec in H. destruct (call_mrec x0 xR v); discriminate. }
      simp call_mrec in H.
      destruct (call_mrec_call_frame x0 v) eqn : Heq1.
      simp perm_var. simp call_mrec. rewrite Heq1.
      injection H. intros. subst. auto.
    + setoid_rewrite perm_handler_equation_8 in H0.
      injection H0. intros. subst. inj_existT. subst.
      dependent destruction xR.
      { simp call_mrec in H. destruct (call_mrec_call_frame x0 v); discriminate. }
      simp call_mrec in H. dependent destruction xR.
      2 : { simp call_mrec in H. destruct ( call_mrec x0 xR v); discriminate. }
      simp call_mrec in H. 
      destruct (call_mrec_call_frame x0 v) eqn : Heq1. simp perm_var.
      simp call_mrec. rewrite Heq1. injection H. intros. subst. auto.
    + setoid_rewrite perm_handler_equation_9 in H0.
      dependent destruction xR.
      { simp call_mrec in H. destruct (call_mrec_call_frame x0 v); discriminate. }
      dependent destruction xR.
      { simp call_mrec in H. destruct (call_mrec_call_frame x0 v); discriminate. }
      simp call_mrec in H. simp perm_var. simp call_mrec.
      destruct (call_mrec x0 xR v) eqn : Heq1.
      injection H. intros. subst. inj_existT. subst.
      destruct (perm_handler (perm_map (perm_map Hperm)) d1) eqn : Heq2.
      eapply IHHperm in Heq2 as Heq3; eauto.
      destruct (call_mrec x0 (perm_var xR Hperm) v) eqn : Heq4.
      simpl. simpl in Heq2. subst. setoid_rewrite Heq2 in H0.
      simpl in H0. injection H0. intros. auto.
  - unfold perm_denote. Transparent perm_map. simpl perm_map.
    Opaque perm_map. intros. destruct l2.
    + specialize (perm_nil_cons2 _ _ Hperm1) as H'. subst.
      inversion xR.
    + destruct l1. inversion xR. destruct l3.
      inversion d2.
      setoid_rewrite perm_handler_equation_10 in H0.
      match goal with H : (let 'd2 && f12 := ?x in let 'd3 && f23 := ?y in _) = _  |- _ => 
                        destruct x eqn : Heq1 end.
      match goal with H : (let 'd2 && f12 := ?x in _) = _  |- _ => 
                        destruct x eqn : Heq2 end.
      injection H0. intros. subst. inj_existT. subst.
      setoid_rewrite perm_var_trans.
      eapply IHHperm1 in H as IH'; eauto.
      destruct (call_mrec x (perm_var xR Hperm1) v) eqn : Heq3.
      simpl in IH'. subst.
      eapply IHHperm2; eauto.
Qed.

(*key goal *)
Lemma mapE_perm_handler_call_term:
  forall (t2 : vtype) (MR1 MR2 : mfix_ctx) (Hperm : perm MR1 MR2) (t0 : vtype) 
    (R : call_frame) (xR : var R MR1) (x : var (t0, t2) R) (r1 r2 : denote_type t0),
    types_equiv t0 r1 r2 ->
    rutt (mfix_pre_equiv MR2) (mfix_post_equiv MR2) (types_equiv t2)
         (mapE (perm_handler  (perm_denote Hperm))
               (call_term x xR r1)) (call_term x (perm_var xR Hperm) r2).
Proof.
  intros t2 MR1 MR2 Hperm t0 R xR x.
  intros. erewrite mapE_perm_handler_call_term_aux; try eapply perm_var_map_handler_rel; eauto.
  2 : apply valid_perm_handler. cbn. unfold call_term.
  destruct (call_mrec x (perm_var xR Hperm) r1) eqn : Heq1.
  destruct (call_mrec x (perm_var xR Hperm) r2) eqn : Heq2.
  setoid_rewrite bind_trigger. apply rutt_Vis.
  eapply mfix_pre_call_mrec; eauto.
  intros. apply rutt_Ret. eapply mfix_post_equiv_types_equiv; eauto.
Qed.

Lemma lift_handler_rel MR1 MR2  : 
  var_map_handler_rel (@lift_handler MR1 MR2)
                      (fun _ x => weaken_var_l _ _ _ x).
Proof.
  red. revert MR2. induction MR1.
  - intros. simp weaken_var_l. simp lift_handler in H0. injection H0.
    intros. subst. setoid_rewrite H. auto.
  - intros. simp weaken_var_l. simp lift_handler in H0.
    setoid_rewrite call_mrec_equation_2.
    destruct (lift_handler MR1 d1) eqn : Heq1. 
    eapply IHMR1 in H as IH; eauto. 
    injection H0. intros. subst. inj_existT. subst.
    destruct (call_mrec x (weaken_var_l MR1 MR2 R xR) v) eqn : Heq2.
    setoid_rewrite Heq2. auto.
Qed.

Lemma mapE_lift_handler_call_term:
  forall (t2 : vtype) (MR1 MR2 : mfix_ctx)(t0 : vtype) 
    (R : call_frame) (xR : var R MR2) (x : var (t0, t2) R) (r1 r2 : denote_type t0),
    types_equiv t0 r1 r2 ->
    rutt (mfix_pre_equiv (MR1 ++ MR2)) (mfix_post_equiv (MR1 ++ MR2)) (types_equiv t2)
         (mapE (@lift_handler MR1 MR2)
               (call_term x xR r1)) (call_term x (weaken_var_l _ _ _ xR) r2).
Proof.
  intros t2 MR1 MR2 t0 R xR x.
  intros. erewrite mapE_perm_handler_call_term_aux; try eapply lift_handler_rel; eauto.
  2 : apply valid_lift_handler. cbn. unfold call_term.
  destruct (call_mrec x (weaken_var_l MR1 MR2 R xR) r1) eqn : Heq1.
  destruct (call_mrec x (weaken_var_l MR1 MR2 R xR) r2) eqn : Heq2.
  setoid_rewrite bind_trigger. apply rutt_Vis.
  eapply mfix_pre_call_mrec; eauto.
  intros. apply rutt_Ret. eapply mfix_post_equiv_types_equiv; eauto.
Qed.


Lemma call_term_bind_inv_aux1  : 
 forall (MR : mfix_ctx)
    (R0 : call_frame) (tin0 tout0 : vtype) (x0 : var (tin0, tout0) R0) (xR0 : var R0 MR)
    (vvin : denote_type tin0)
    (tin tout : vtype) (Rcall : call_frame)
    (xR : var Rcall MR) (x : var (tin, tout) Rcall) (vvcall : denote_type tin),
   projT1 (call_mrec x xR vvcall) = projT1 (call_mrec x0 xR0 vvin) ->
   var_eq xR xR0.
Proof.
  intros. generalize dependent xR0.
  dependent induction xR.
  - simp call_mrec. intros.
    dependent destruction xR0. constructor. simp call_mrec in H.
    destruct (call_mrec_call_frame x vvcall). destruct (call_mrec x0 xR0 vvin).
    discriminate.
  - intros. dependent destruction xR0.
    + simp call_mrec in H. destruct (call_mrec x xR vvcall). 
      destruct (call_mrec_call_frame x0 vvin). discriminate.
    + constructor. eapply IHxR with (x := x) (vvcall := vvcall).
      simp call_mrec in H.
      destruct (call_mrec x xR vvcall). destruct (call_mrec x0 xR0 vvin).
      injection H. intros. subst. auto.
Qed.

Lemma call_term_bind_inv_aux2 : 
 forall (MR : mfix_ctx)
    
    (tin tout : vtype) (Rcall : call_frame)
    (tin0 tout0 : vtype) (x0 : var (tin0, tout0) Rcall)
    (xR : var Rcall MR) (x : var (tin, tout) Rcall) (vvcall : denote_type tin) 
    (vvin : denote_type tin0),
   projT1 (call_mrec x xR vvcall) = projT1 (call_mrec x0 xR vvin) ->
   (var_eq x x0 * (vvin ~= vvcall))%type.
Proof.
  intros. generalize dependent x0. generalize dependent x.
  dependent induction xR.
  - intros. simp call_mrec in H.
    assert (projT1 (call_mrec_call_frame x vvcall) = projT1 (call_mrec_call_frame x0 vvin)).
    destruct (call_mrec_call_frame x vvcall). destruct (call_mrec_call_frame x0 vvin).
    injection H. intros. auto. clear H.
    generalize dependent x0. dependent induction x.
    + simp call_mrec_call_frame. intros.
      dependent destruction x0. simp call_mrec_call_frame in H0. injection H0.
      intros. subst. split; constructor. exfalso.
      simp call_mrec_call_frame in H0. destruct (call_mrec_call_frame x0 vvin).
      discriminate.
    + intros.
      dependent destruction x0.
      * simp call_mrec_call_frame in H0. destruct (call_mrec_call_frame x vvcall).
        discriminate.
      * destruct b. simp call_mrec_call_frame in H0.
        enough (var_eq x x0 * (vvin ~= vvcall)). destruct X. split; auto.
        constructor. auto.
        eapply IHx; eauto. 
        destruct (call_mrec_call_frame x vvcall).
        destruct (call_mrec_call_frame x0 vvin). injection H0. auto.
  - intros. eapply IHxR. simp call_mrec in H.
    destruct (call_mrec x xR vvcall).
    destruct (call_mrec x0 xR vvin). injection H. intros. subst.
    auto.
Qed.
