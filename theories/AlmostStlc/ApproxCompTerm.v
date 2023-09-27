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
Require Import Coq.Relations.Relation_Operators.
Import MonadNotation.
Local Open Scope monad_scope.
Require Export SemanticsFactsSeq.
Require Export CallMrecFacts.
Require Export SemanticsFactsSeq2.
Require Export SmallStepSeqFacts.
Require Import Lia.
Require Import Coq.Classes.Morphisms.
Require Export ClosingSubst.
Require Export LogicalApprox.
Require Export SubstCommute.



Inductive approx_comp_term {t MR} : forall (n : nat) (c1 c2 : comp t [] MR), Prop :=
  approx_comp_term_intro n c1 c2 : 
    (forall v1, eval_rel_stuck c1 (inl v1) -> eval_rel_stuck c2 (inl v1)) /\
    (forall tin tout Rcall (xR : var Rcall MR) (x : var (tin, tout) Rcall) 
         (vcall : closed_value tin) (E1 :eval_context t MR (inr (SmallStepSeq.callv xR x vcall) ) true) 
         (c1' : comp t [] MR),
  eval_rel_stuck c1 (inr c1') -> stuck_call c1' (SmallStepSeq.callv xR x vcall) E1 ->
  exists c2' E2, eval_rel_stuck c2 (inr c2') /\ stuck_call c2' (SmallStepSeq.callv xR x vcall) E2 /\
           forall vout n', n' < n -> approx_comp_term n' (subst_eval_context E1 vout) (subst_eval_context E2 vout)) -> approx_comp_term n c1 c2.

(*
Inductive approx_comp_term {t MR} : forall (c1 c2 : comp t [] MR), Prop :=
  approx_comp_term_intro c1 c2 : 
    (forall v1, eval_rel_stuck c1 (inl v1) -> eval_rel_stuck c2 (inl v1)) /\
    (forall tin tout Rcall (xR : var Rcall MR) (x : var (tin, tout) Rcall) 
         (vcall : closed_value tin) (E1 :eval_context t MR (inr (SmallStepSeq.callv xR x vcall) ) true) 
         (c1' : comp t [] MR),
  eval_rel_stuck c1 (inr c1') -> stuck_call c1' (SmallStepSeq.callv xR x vcall) E1 ->
  exists c2' E2, eval_rel_stuck c2 (inr c2') /\ stuck_call c2' (SmallStepSeq.callv xR x vcall) E2 /\
           forall vout, approx_comp_term (subst_eval_context E1 vout) (subst_eval_context E2 vout)) -> approx_comp_term c1 c2.
*)

Lemma approx_comp_approx_comp_term n t MR m (c1 c2 : comp t [] MR) :
  approx_comp_term n c1 c2 -> approx_comp n approx_val m c1 -> approx_comp n approx_val m  c2.
Proof.
  generalize dependent t. revert MR. 
  induction n as [ n IHn ] using (well_founded_induction lt_wf).
  intros MR t m c1 c2 Hc12 Hmc1.
  constructor. intros j Hj. inversion Hmc1. subst.
  specialize (H j Hj) as [Hret Hstuck].
  split.
  - intros. specialize (Hret _ H) as [v [Hv11 Hv12]]. clear Hstuck.
    exists v. inversion Hc12. subst. destruct H0 as [Hret _]. split; auto.
  - intros. specialize (Hstuck _ _ _ _ _ _ _ H).
    destruct Hstuck as [vcall [E [c' [HE1 [HE2 [HE3 HE4]]]]]].
    inversion Hc12. subst. destruct H0 as [_ Hstuck].
    eapply Hstuck in HE2; eauto. destruct HE2 as [c'' [E' [HE'1 [HE'2 HE'3]]]].
    exists vcall, E', c''. split; auto. split; auto. split; auto.
    intros. specialize (HE4 j'' vvret vret H0 H1).
    eapply IHn; eauto. lia. eapply HE'3. lia.
Qed.

Lemma approx_comp_term_refl n t MR (c : comp t [] MR) : 
  approx_comp_term n c c.
Proof.
  generalize dependent t. revert MR.
  induction n as [ n IHn ] using (well_founded_induction lt_wf).
  intros.
  constructor. split.
  auto. intros. eexists. eexists. split; eauto.
Qed.


Lemma approx_comp_term_trans n : forall t MR (c1 c2 c3 : comp t [] MR),
    approx_comp_term n c1 c2 -> approx_comp_term n c2 c3 ->
    approx_comp_term n c1 c3.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros. inversion H. subst. inversion H0. subst. clear H0 H.
  constructor. split.
  - destruct H1 as [Hret12 _]. destruct H2 as [Hret23 _].
    intros. eapply Hret12 in H. auto.
  - destruct H1 as [_ Hstuck12]. destruct H2 as [_ Hstuck23].
    intros. eapply Hstuck12 in H as H1; eauto. 
    destruct H1 as [c2' [E2 [H1 [H2 H3]]]].
    eapply Hstuck23 in H1 as H4; try apply H2.
    destruct H4 as [c3' [E3 [HE31 [HE32 HE33]]]].
    exists c3'. exists E3.
    split; [ | split]; eauto.
Qed.

Lemma approx_comp_term_step1 n t MR (c1 c2 : comp t [] MR) :
  step_rel c1 c2 -> approx_comp_term n c1 c2.
Proof.
  intros.
  constructor. split.
  - intros. dependent destruction H0.
    + enough (c2 = c0). subst. auto. dependent destruction H.
      dependent destruction H0. rewrite H in H0. injection H0. auto.
    + dependent destruction H. rewrite H in H0. discriminate.
  - intros. exists c1', E1. split; [ | split]; eauto.
    + dependent destruction H0.
      * enough (c2 = c0). subst. auto. dependent destruction H.
        dependent destruction H0. rewrite H in H0. injection H0. auto.
      * dependent destruction H. eapply stuck_call_stuck' in H0.
        rewrite H in H0. discriminate.
    + intros. apply approx_comp_term_refl.
Qed.

Lemma approx_comp_term_step2 n t MR (c1 c2 : comp t [] MR) :
  step_rel c1 c2 -> approx_comp_term n c2 c1.
Proof.
  intros. constructor. split.
  - intros. econstructor; eauto.
  - intros. exists c1', E1. split; [ | split]; eauto.
    econstructor; eauto. intros. apply approx_comp_term_refl.
Qed.

       
Lemma approx_comp_term_comp_call n t1 MR t2 (cbody : comp t2 [t1] MR) (varg : value t1 []) :
  approx_comp_term n (subst_comp_cons cbody varg) (comp_app (val_abs cbody) varg).
Proof.
  apply approx_comp_term_step2. constructor. unfold step.
  simp observe. cbn. simp step_eval_context. simp subst_eval_context.
  auto.
Qed.

Lemma lower_approx_comp_term n : forall n' t MR (c1 c2 : comp t [] MR),
    n' < n -> approx_comp_term n c1 c2 -> approx_comp_term n' c1 c2.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros. inversion H0. subst. destruct H1 as [Hret Hstuck].
  constructor. split; auto.
  intros. eapply Hstuck in H1; eauto. destruct H1 as [c2' [E2 [? [? ?]]]].
  eexists. eexists. split; [ | split]; eauto.
Qed.

Lemma approx_comp_term_let_cong n : forall t1 t2 MR 
       (c1 c1' : comp t1 [] MR) (c2 c2' : comp t2 [t1] MR),
    approx_comp_term n c1 c1' -> (forall v, approx_comp_term n (subst_comp_cons c2 v) (subst_comp_cons c2' v)) ->
    approx_comp_term n (comp_let c1 c2) (comp_let c1' c2').
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros. inversion H. subst. constructor. split; intros.
  - eapply eval_rel_stuck_let3 in H2. rename v1 into v2. destruct H2 as [v1 [Hv11 Hv12]].
    destruct H1 as [Hret1 _].
    eapply eval_rel_stuck_let1; eauto.
    specialize (H0 v1). inversion H0. subst. destruct H1 as [Hret2 _].
    auto.
  - eapply eval_rel_stuck_let4 in H2 as H2'.
    destruct H2' as [[c' Hc'] | [v1 [Hv11 Hv12]] ].
    + eapply eval_rel_stuck_let2 with (c2 := c2) in Hc' as Hc''.
      eapply eval_rel_stuck_inj in Hc'' as Heq; try apply H2. subst.
      inversion H. subst. destruct H4 as [Hret1 Hstuck1].
      dependent destruction H3.
      eapply Hstuck1 in Hc' as Hc'''; eauto.
      destruct Hc''' as [c'' [E2 [? [? ?]]]].
      eapply eval_rel_stuck_let2 with (c2 := c2') in H4 as ?.
      eexists. eexists.
      split; [ | split]; eauto. constructor. eauto.
      intros. simp subst_eval_context.
      eapply IHn; eauto. intros. eapply lower_approx_comp_term; eauto.
    + destruct H1 as [Hret1 Hstuck1]. eapply Hret1 in Hv11 as Hv13.
      specialize (H0 v1). inversion H0. subst.
      destruct H1 as [Hret2 Hstuck2]. eapply Hstuck2 in Hv12 as ?; eauto.
      destruct H1 as [c2'' [E2 [? [? ?]]]]. exists c2'', E2. split; [ | split]; auto.
      eapply eval_rel_stuck_let1; eauto.
Qed.
    
Lemma approx_comp_term_let_ret_r n t MR (c : comp t [] MR) :
  approx_comp_term n c (comp_let c (comp_ret (val_var VarZ))).
Proof.
  generalize dependent t. revert MR.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros.
  constructor. split.
  - intros. eapply eval_rel_stuck_let1; eauto.
    unfold subst_comp_cons. simp subst_comp. simp subst_var.
    apply eval_rel_stuck_val. unfold step. simp observe. auto.
  - intros. exists (comp_let c1' (comp_ret (val_var VarZ))), (ev_let E1 (comp_ret (val_var VarZ))).
    split; [ | split].
    + apply eval_rel_stuck_let2; auto.
    + constructor. auto.
    + intros. rewrite subst_eval_context_equation_2. 
      apply IHn. auto.
Qed.

Lemma approx_comp_term_let_ret_r' n t MR (c : comp t [] MR) :
  approx_comp_term n (comp_let c (comp_ret (val_var VarZ))) c.
Proof.
  generalize dependent t. revert MR.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros. constructor. split.
  - intros. eapply eval_rel_stuck_let3 in H. destruct H as [v1' [Hv1'1 Hv1'2]].
    unfold subst_comp_cons in Hv1'2. simp subst_comp in Hv1'2.
    simp subst_var in Hv1'2. dependent destruction Hv1'2; auto.
    exfalso. dependent destruction H.
  - intros. eapply eval_rel_stuck_let4 in H as H'.
    destruct H' as [[c' Hc'] | [v1' [Hv1'1 Hv1'2]]].
    + eapply eval_rel_stuck_let2 in Hc' as Hc''. 
      eapply eval_rel_stuck_inj in H; try eapply Hc''. subst.
      dependent destruction H0.
      eexists. eexists. split; [ | split]; eauto.
      intros. simp subst_eval_context.
    + unfold subst_comp_cons in Hv1'2. simp subst_comp in Hv1'2.
      simp subst_var in Hv1'2. dependent destruction Hv1'2;
      dependent destruction H1.
Qed.

Lemma approx_comp_term_let_assoc n : forall t1 t2 t3 MR 
      (c1 : comp t1 [] MR) (c2 : comp t2 [t1] MR) (c3 : comp t3 [t2] MR),
  approx_comp_term n 
                   (comp_let (comp_let c1 c2) c3) 
                   (comp_let c1 (comp_let c2 (weaken_r_comp _ c3))).
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf). 
  intros. constructor. split.
  - intros. rename v1 into v3. eapply eval_rel_stuck_let3 in H as H12.
    destruct H12 as [v2 [Hv21 Hv22]].
    eapply eval_rel_stuck_let3 in Hv21 as H1.
    destruct H1 as [v1 [Hv11 Hv12]].
    eapply eval_rel_stuck_let1; eauto. unfold subst_comp_cons.
    simp subst_comp. eapply eval_rel_stuck_let1; eauto.
    clear - Hv22. rewrite subst_comp_weaken_r. auto.
  - intros. rename c1' into cf'. rename E1 into Ef.
    eapply eval_rel_stuck_let4 in H as H'. 
    destruct H' as [ [c12 Hc12] | [v2 [Hv21 Hv22]] ].
    + eapply eval_rel_stuck_let4 in Hc12 as H'.
      destruct H' as [ [c1' Hc1'] | [v1 [Hv11 Hv12]] ].
      * eapply eval_rel_stuck_ex_call in Hc1' as Hcall.
        destruct Hcall as [t' [ca [E1 HE1]]].
        eapply stuck_call_let with (c2 := c2) in HE1 as HE1'.
        eapply stuck_call_let with (c2 := c3) in HE1'.
        eapply eval_rel_stuck_let2 with (c2 := c2) in Hc1' as Hc1''.
        eapply eval_rel_stuck_let2 with (c2 := c3) in Hc1''.
        eapply eval_rel_stuck_inj in H; try apply Hc1''. subst.
        eapply stuck_call_inj in H0; try apply HE1'; eauto. destruct H0 as [? [? ?]].
        subst.
        exists (comp_let c1' (comp_let c2 (weaken_r_comp [t2] c3))), (ev_let E1 (comp_let c2 (weaken_r_comp _ c3))). 
        split; [ | split].
        -- apply eval_rel_stuck_let2; auto.
        -- constructor. auto.
        -- intros. simp subst_eval_context.
      * exists (comp_let c12 c3).
        eapply eval_rel_stuck_ex_call in Hv12 as Hcall.
        destruct Hcall as [t' [ca [E1 HE1]]]. 
        eapply stuck_call_let with (c2 := c3) in HE1 as HE1'.
        eapply eval_rel_stuck_let2 with (c2 := c3) in Hv12 as Hv12'; eauto.
        assert (Hc123 : eval_rel_stuck (comp_let (comp_let c1 c2) c3) (inr (comp_let c12 c3))).
        eapply eval_rel_stuck_let2. eapply eval_rel_stuck_let1; eauto.
        eapply eval_rel_stuck_inj in Hc123 as Hc123';  try apply H. subst.
        eapply stuck_call_inj in H0; eauto. destruct H0 as [? [? ?]]. subst.
        exists (ev_let E1 c3).
        split; [ | split].
        -- eapply eval_rel_stuck_let1; eauto. unfold subst_comp_cons.
           simp subst_comp. rewrite subst_comp_weaken_r. auto.
        -- constructor. auto.
        -- intros. apply approx_comp_term_refl.
    + eapply eval_rel_stuck_let3 in Hv21 as H'. destruct H' as [v1 [Hv11 Hv12]].
      exists cf', Ef. split; [ | split].
      * eapply eval_rel_stuck_let1; eauto. unfold subst_comp_cons.
        simp subst_comp. rewrite subst_comp_weaken_r. auto.
        eapply eval_rel_stuck_let1; eauto.
      * auto.
      * intros. apply approx_comp_term_refl.
Qed.

Lemma approx_comp_term_let_assoc' n : forall t1 t2 t3 MR 
      (c1 : comp t1 [] MR) (c2 : comp t2 [t1] MR) (c3 : comp t3 [t2] MR),
  approx_comp_term n 
                   (comp_let c1 (comp_let c2 (weaken_r_comp _ c3)))
                   (comp_let (comp_let c1 c2) c3).
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf). 
  intros. constructor. split.
  - intros. rename v1 into v3. eapply eval_rel_stuck_let3 in H as H12.
    destruct H12 as [v2 [Hv21 Hv22]].
    unfold subst_comp_cons in Hv22. simp subst_comp in Hv22.
    rewrite subst_comp_weaken_r in Hv22.
    eapply eval_rel_stuck_let3 in Hv22 as H'.
    destruct H' as [v3' [Hv31 Hv32] ].
    eapply eval_rel_stuck_let1; eauto. eapply eval_rel_stuck_let1; eauto.
  - intros. rename c1' into cf'. rename E1 into Ef.
    eapply eval_rel_stuck_let4 in H as H'. 
    destruct H' as [ [c1' Hc1'] | [v1 [Hv11 Hv12]] ].
    + eapply eval_rel_stuck_let2 with (c2 := (comp_let c2 (weaken_r_comp [t2] c3))) in Hc1' as Hc1''.
      eapply eval_rel_stuck_inj in H as ?; try apply Hc1''; subst.
      eapply eval_rel_stuck_let2 with (c2 := c2) in Hc1' as Hc1'''.
      eapply eval_rel_stuck_let2 with (c2 := c3) in Hc1'''.
      eapply eval_rel_stuck_ex_call in Hc1' as Hcall.
      destruct Hcall as [t' [ca [E1 HE1]]].
      eapply stuck_call_let with (c2 := (comp_let c2 (weaken_r_comp [t2] c3))) in HE1 as HE1'.
      eapply stuck_call_inj in HE1' as ?; try apply H0. destruct H1 as [? [? ?]]; subst. 
      exists (comp_let (comp_let c1' c2) c3). eexists.
      split; auto. split. econstructor. econstructor. eauto.
      intros. simp subst_eval_context.
    + unfold subst_comp_cons in Hv12. simp subst_comp in Hv12.
      rewrite subst_comp_weaken_r in Hv12.
      eapply eval_rel_stuck_let4 in Hv12 as H'.
      destruct H' as [ [c2' Hc2']  | [v2 [Hv21 Hv22]]].
      * eapply eval_rel_stuck_let2 with (c2 := c3) in Hc2' as Hc2''.
        eapply eval_rel_stuck_inj in Hv12 as ?; try apply Hc2''; subst.
        dependent destruction H0. eexists. eexists.
        split; [ | split].
        -- eapply eval_rel_stuck_let2. eapply eval_rel_stuck_let1; eauto.
        -- econstructor. eauto.
        -- intros. simp subst_eval_context. eapply approx_comp_term_refl.
      * exists cf', Ef. split; [ | split].
        -- eapply eval_rel_stuck_let1; eauto. eapply eval_rel_stuck_let1; eauto.  
        -- auto.
        -- intros. apply approx_comp_term_refl.
Qed.

Lemma  approx_comp_term_mfix_ret:
  forall (t : vtype) (MR : mfix_ctx) (R1 : call_frame)
    (bodies : mfix_bodies [] MR R1 R1) (vvret : value t []) 
    (n : nat),
    approx_comp_term n (comp_mfix R1 bodies (comp_ret vvret)) (comp_ret vvret).
Proof.
  intros t MR R1 bodies vvret n.
  constructor. split.
  - intros. constructor. unfold step. simp observe.
    dependent destruction H.
    dependent destruction H. simp subst_eval_context in H0.
    simp step_brex in H0. dependent destruction H0; auto.
    dependent destruction H.
  - intros. dependent destruction H.
    + dependent destruction H. simp subst_eval_context in H0.
      simp step_bredex in H0. dependent destruction H0. dependent destruction H.
      dependent destruction H.
    + dependent destruction H.
Qed.

Lemma approx_comp_term_mfix_let:
  forall (t1 t2 t3 : vtype) (MR : mfix_ctx) (R1 : call_frame) (tin : vtype) (vcall : closed_value tin) 
    (R2 : call_frame) (x : var (tin, t3) R2) (xR : var R2 MR)
    (E : eval_context t1 (R1 :: MR) (inr (SmallStepSeq.callv (VarS (b := R1) xR) x vcall)) true) (c : comp t2 [t1] (R1 :: MR))
    (bodies : mfix_bodies [] MR R1 R1) (E' : eval_context t1 MR (inr (SmallStepSeq.callv xR x vcall)) true) 
    (vvret : value t3 []) (n : nat),
    approx_comp_term n (comp_mfix R1 bodies (comp_let (subst_eval_context E (comp_ret vvret)) c))
                     (comp_let (subst_eval_context E' (comp_ret vvret)) (comp_mfix R1 (weaken_r_bodies bodies) c)).
Proof.
  intros t1 t2 t3 MR R1 tin vcall R2 x xR E c bodies E' vvret n.
Admitted.
(* weird mismatch of *)
Lemma stuck_call_push_eval_context_mfix:
  forall (t : vtype) (R1 R2 : call_frame) (MR : mfix_ctx) (bodies : mfix_bodies [] MR R1 R1)
    (tin tout : vtype) (x : var (tin, tout) R2) (xR : var R2 MR)
    (vcall : closed_value tin)
    (E : eval_context t (R1 :: MR) (inr (SmallStepSeq.callv (VarS (b := R1) xR) x vcall)) true),
    exists E', 
    stuck_call
      (push_eval_context (inr (SmallStepSeq.callv (VarS xR) x vcall)) E (comp_mfix_map bodies)
                         (comp_call xR x vcall)) 
      (SmallStepSeq.callv xR x vcall)
      E' /\
      (forall vvret n, approx_comp_term n (comp_mfix R1 bodies (subst_eval_context E (comp_ret vvret)))  
                  (subst_eval_context E' (comp_ret vvret))).
Proof.
  intros.
  dependent induction E.
  - simp push_eval_context. exists ev_hole. split. constructor. intros. simp subst_eval_context.
    apply approx_comp_term_mfix_ret.
  - simp push_eval_context. simp subst_eval_context_ctx.
    specialize (IHE _ _ _ _ _ _ _ bodies _ eq_refl eq_refl JMeq_refl eq_refl JMeq_refl).
    destruct IHE as [E' [HE'1 HE'2]]. econstructor. split. econstructor. eauto.
    intros. simp subst_eval_context. unfold comp_mfix_map.
    apply approx_comp_term_mfix_let.
Qed.

