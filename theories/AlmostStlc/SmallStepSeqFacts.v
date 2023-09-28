Require Export TypedVar.
Require Export SyntaxSeq.
Require Export SmallStepSeq.
Require Export SemanticsFactsSeq.
Require Export SemanticsFactsSeq2.
Require Export ClosingSubst.
Import List.ListNotations.
Open Scope list_scope.
From Equations Require Import Equations Signature.
Require Import Coq.Program.Equality.
Require Import Lia.




Lemma step_ret t MR (v : closed_value t) :
  step (MR := MR) (comp_ret v) = inr v.
Proof.
  cbv. simp observe. auto.
Qed.


Lemma step_let1 t1 t2 MR (c1 c1' : comp t1 [] MR) (c2 : comp t2 [t1] MR) :
  step_rel c1 c1' ->
  step_rel (comp_let c1 c2) (comp_let c1' c2).
Proof.
  intros [?]. constructor. unfold step.
  simp observe. unfold step in H. destruct (SmallStepSeq.observe c); try destruct b;
    try discriminate.
  f_equal. destruct r.
  - simp step_eval_context. cbn. f_equal. simp subst_eval_context. injection H.
    intros. clear H. rewrite step_eval_context_equation_1 in H0.
    injection H0. intros. subst. clear H0. auto.
  - simp step_eval_context. cbn. injection H. intros. rewrite H0. auto.
Qed.


Lemma step_let2 t1 t2 MR (c1 : comp t1 [] MR) (c2 : comp t2 [t1] MR) (v1 : closed_value t1) :
  step c1 = (inr v1) -> step_rel (comp_let c1 c2) (subst_comp_cons c2 v1).
Proof.
  intros. econstructor. unfold step. simp observe. unfold step in H.
  destruct (SmallStepSeq.observe c1); try destruct b;
    try discriminate. cbn. simp step_eval_context. f_equal. simpl Monad.ret.
  simp step_bredex. simp subst_eval_context. injection H. intros. subst. auto.
Qed.

Equations num_lets {t Γ MR} (c : comp t Γ MR) : nat :=
  num_lets (comp_ret v) := 0;
  num_lets (comp_let c1 c2) := 1 + num_lets c1 + num_lets c2;
  num_lets (comp_match_nat vn c1 c2) := num_lets c1 + num_lets c2;
  num_lets (comp_succ vn) := 0;
  num_lets (comp_match_list vl c1 c2) := num_lets c1 + num_lets c2;
  num_lets (comp_split vp cs) := num_lets cs;
  num_lets (comp_app vf varg) := 0;
  num_lets (comp_call _ _ _) := 0;
  num_lets (comp_mfix R bodies c) := num_lets c;
  num_lets (comp_lift c) := num_lets c;
  num_lets (comp_perm _ c) := num_lets c.

Transparent num_lets.

Lemma num_lets_subst_comp MR t1 Γ1 t2 Γ2 (c : comp t1 (Γ1 ++ [t2] ++ Γ2) MR)
      (v : value t2 Γ2) :
  num_lets c = num_lets (subst_comp c v).
Proof.
  dependent induction c; simp subst_comp; simp num_lets; auto.
  - erewrite IHc1 with (v := v); eauto. f_equal.
    eapply IHc2 with (Γ1 := t1 :: Γ1); auto.
  - erewrite IHc1 with (v := v); eauto. f_equal.
    eapply IHc2 with (Γ1 := Nat :: Γ1); auto.
  - erewrite IHc1 with (v := v); eauto. f_equal.
    eapply IHc2 with (Γ1 := _ :: _ :: Γ1); auto.
  - eapply IHc with (Γ1 := _ :: _ :: Γ1); auto.
Qed.

(* remaining cases should be similarly easy *)

Lemma step_let3 t1 t2 MR (c1 c1' : comp t1 [] MR) (c2 : comp t2 [t1] MR) :
  step_rel (comp_let c1 c2) (comp_let c1' c2) ->
  step_rel c1 c1'.
Proof.
  intros. dependent destruction H. constructor. unfold step. unfold step in H.
  simp observe in H. destruct (SmallStepSeq.observe c1) eqn : Heqx; try destruct b;
    try discriminate.
  - destruct r; simp step_eval_context in H.
    + cbn in H. simp step_eval_context. cbn. simp subst_eval_context in H.
      injection H. intros. inj_existT. rewrite H0. auto.
    + cbn in H. destruct (step_eval_context b (inr c) E).
      injection H. intros. inj_existT. subst. auto.
      discriminate.
  - rename c into v.
    cbn in H. simp step_eval_context in H. cbn in H. simp subst_eval_context in H.
    simp step_bredex in H. injection H. intros. exfalso.
    assert (num_lets (subst_comp_cons c2 v) = num_lets (comp_let c1' c2)).
    rewrite H0. auto. simp num_lets in H1. 
    unfold subst_comp_cons in H1. 
    rewrite <- num_lets_subst_comp with (Γ1 := []) (t2 := t1) (Γ2 := []) in H1.
    clear - H1. assert (1 + num_lets c1' + num_lets c2 > num_lets c2). lia.
    rewrite H1 in H at 2. lia.
Qed.

Lemma observe_inr t MR (c : comp t [] MR) v :
  SmallStepSeq.observe c = inr v -> c = comp_ret v.
Proof.
  rename c into c1. intros Heqx.
  dependent destruction c1; simp observe in Heqx; try discriminate.
  + injection Heqx. intros. subst. auto.
  + destruct (SmallStepSeq.observe c1_1); try destruct b; discriminate.
  + dependent destruction vn; try inversion x. simp observe in Heqx.
    discriminate.
  + dependent destruction vn; try inversion x. simp observe in Heqx.
    discriminate.
  + dependent destruction vf; try inversion x. simp observe in Heqx.
    discriminate.
  + destruct (SmallStepSeq.observe c1); try destruct b; discriminate.
  + destruct (SmallStepSeq.observe c1); try destruct b; discriminate.
  + destruct (SmallStepSeq.observe c1); try destruct b; discriminate.
Qed.

Lemma step_let4 t1 t2 MR (c1 : comp t1 [] MR) (c2 : comp t2 [t1] MR) c3 :
  step_rel (comp_let c1 c2) c3 ->
  (exists v, c1 = comp_ret v /\ c3 = subst_comp_cons c2 v) \/ (exists c1', c3 = comp_let c1' c2).
Proof.
  intros H. dependent destruction H. unfold step in H.
  simp observe in H. destruct (SmallStepSeq.observe c1) eqn : Heqx; try destruct b.
  - destruct r; simp step_eval_context in H. cbn in H. injection H. intros. subst.
    simp subst_eval_context. right. eexists. eauto.
    cbn in H. injection H. intros. destruct (step_eval_context b (inr c) E).
    injection H0. intros. subst. right. eexists. eauto.
    discriminate.
  - left. apply observe_inr in Heqx. subst.
    exists c. split; auto. cbn in H. simp step_eval_context in H.
    simp subst_eval_context in H. simp step_bredex in H.
    injection H. intros. subst. eexists.
Qed.

Lemma step_let5 t1 t2 MR (c1 : comp t1 [] MR) (c2 : comp t2 [t1] MR) c3 :
  step_rel (comp_let c1 c2) c3 ->
  (exists v, c1 = comp_ret v /\ c3 = subst_comp_cons c2 v) \/ (exists c1', c3 = comp_let c1' c2 /\ step_rel c1 c1').
Proof.
  intros. eapply step_let4 in H as H'. destruct H'.
  - left. auto.
  - right. destruct H0 as [c1' Hc1']. 
    subst. eexists. split; auto. eapply step_let3; eauto.
Qed.


Lemma eval_rel_stuck_ex_call t MR (c1 c2 : comp t [] MR) :
  eval_rel_stuck c1 (inr c2) ->
  exists t' (ca : call_syn t' MR) (E : eval_context t MR (inr ca) true), stuck_call c2 ca E.
Proof.
  intros H. dependent induction H; eauto.
Qed.

Lemma stuck_call_inj t1 t2 t3 MR (c : comp t1 [] MR)
      (ca1 : call_syn t2 MR) (ca2 : call_syn t3 MR) E1 E2 :
  stuck_call c ca1 E1 -> stuck_call c ca2 E2 ->
  t2 = t3 /\ ca1 ~= ca2 /\ E1 ~= E2.
Proof.
  intros H. dependent induction H.
  - intros. dependent destruction H0.
    eapply IHstuck_call in H0. destruct H0 as [? [? ?]]. subst. auto.
  - intros. dependent destruction H. auto.
Qed.

Lemma eval_rel_stuck_inj t MR (c1 c2 c3 : comp t [] MR) :
  eval_rel_stuck c1 (inr c2) ->
  eval_rel_stuck c1 (inr c3) ->
  c2 = c3.
Proof.
  intro H. generalize dependent c3.
  dependent induction H.
  - intros. dependent destruction H1.
    + dependent destruction H. dependent destruction H1.
      rewrite H in H1. injection H1. intros. subst. eapply IHeval_rel_stuck in H2; eauto.
    + apply stuck_call_stuck' in H1. dependent destruction H.
      rewrite H in H1. discriminate.
  - intros. dependent destruction H0.
    + apply stuck_call_stuck' in H. dependent destruction H0.
      rewrite H in H0. discriminate.
    + auto.
Qed.


Lemma eval_rel_stuck_let1 t1 t2 MR (c1 : comp t1 [] MR) (c2 : comp t2 [t1] MR)
      (v1 : closed_value t1) (r : closed_value t2 + comp t2 [] MR) : 
  eval_rel_stuck c1 (inl v1) -> eval_rel_stuck (subst_comp_cons c2 v1) r ->
  eval_rel_stuck (comp_let c1 c2) r.
Proof.
  intros H. dependent induction H.
  - intros. specialize (IHeval_rel_stuck c2 v1 r eq_refl H1).
    econstructor. eapply step_let1; eauto. auto.
  - intros. eapply step_let2 with (c2 := c2) in H. econstructor; eauto.
Qed.

Lemma eval_rel_stuck_let2 t1 t2 MR (c1 c1' : comp t1 [] MR) (c2 : comp t2 [t1] MR) :
  eval_rel_stuck c1 (inr c1') -> eval_rel_stuck (comp_let c1 c2) (inr (comp_let c1' c2)).
Proof.
  intros H. dependent induction H.
  - econstructor. eapply step_let1; eauto. eauto.
  - eapply eval_rel_stuck_stuck. econstructor. eauto.
Qed.

Lemma eval_rel_stuck_let3 t1 t2 MR (c1 : comp t1 [] MR) (c2 : comp t2 [t1] MR) v2 :
  eval_rel_stuck (comp_let c1 c2) (inl v2) ->
  exists v1, eval_rel_stuck c1 (inl v1) /\ eval_rel_stuck (subst_comp_cons c2 v1) (inl v2).
Proof.
  intros H. dependent induction H.
  - eapply step_let5 in H as Hstep.
    destruct Hstep as [[v [Hv Hc2]] | [c1' [Hc1'1 Hc1'2]]].
    + subst. exists v. split. constructor; auto. unfold step. simp observe.
    + subst. specialize (IHeval_rel_stuck _ c1' _ _ eq_refl eq_refl).
      destruct IHeval_rel_stuck as [v1 [Hv11 Hv12]].
      exists v1. split; auto. econstructor; eauto.
  - unfold step in H. simp observe in H. 
    destruct (SmallStepSeq.observe c1); try destruct b; try discriminate.
Qed.

Lemma eval_rel_stuck_let4 t1 t2 MR (c1 : comp t1 [] MR) (c2 : comp t2 [t1] MR) c' :
  eval_rel_stuck (comp_let c1 c2) (inr c') ->
  (exists c'', eval_rel_stuck c1 (inr c'')) \/ (exists v1, eval_rel_stuck c1 (inl v1) /\ eval_rel_stuck (subst_comp_cons c2 v1) (inr c')). 
Proof.
  intros H. dependent induction H.
  - eapply step_let5 in H as Hstep.
    destruct Hstep as [[v [Hv Hc2]] | [c1' [Hc1'1 Hc1'2]]].
    + subst. right. exists v. split; auto. eapply eval_rel_stuck_val. unfold step.
      simp observe. auto.
    + subst. specialize (IHeval_rel_stuck _ _ _ _ eq_refl eq_refl).
      destruct IHeval_rel_stuck as [[c'' Hc''] | [v1 [Hv11 Hv12]] ].
      * left. exists c''. econstructor; eauto.
      * right. exists v1. split; auto. econstructor; eauto.
  - left. dependent destruction H. exists c1. eapply eval_rel_stuck_stuck; eauto.
Qed.

Lemma step_eval_context_exposed_call:
  forall (t1 t2 : vtype) (R : call_frame) (MR1 MR2 : mfix_ctx) (c : call_syn t2 MR2)
    (E : eval_context t1 (R :: MR1) (inr c) true), step_eval_context true (inr c) E = None.
Proof.
  intros t1 t2 R MR1 MR2 c E.
  dependent induction E; simp step_eval_context. auto.
  cbn. rewrite IHE; auto.
Qed.

Lemma step_mfix_eval_context t1 t2 R MR1 MR2 (r : bredex t2 MR2 + call_syn t2 MR2) b
      (E : eval_context t1 (R :: MR1) r b) (bodies : mfix_bodies [] MR1 R R) c' :
  step_eval_context b r E = Some c' ->
  step_eval_context _ r (ev_mfix b R bodies E) = Some (comp_mfix R bodies c').
Proof.
  generalize dependent c'. dependent induction E; destruct r; simp step_eval_context;
    intros; try discriminate.
  - cbn in *. intros. injection H. intros. simp subst_eval_context.
    simp subst_eval_context in H. injection H. intros. subst. auto.
  - cbn in H. injection H. intros. subst. simp subst_eval_context.
    cbn. auto.
  - cbn in H. simp step_eval_context in H.
    destruct (step_eval_context b (inr c0) E) eqn : HE; try discriminate.
    injection H. intros. subst. eapply IHE with (bodies := bodies) in HE as HE1; eauto.
    destruct b; simp step_eval_context.
    + assert (step_eval_context true (inr c0) E = None).
      eapply step_eval_context_exposed_call.
      rewrite HE in H0. discriminate.
    + cbn. rewrite HE. auto.
  - simp subst_eval_context. injection H. intros. subst. auto.
  - rewrite H. cbn. auto.
  - cbn. simp subst_eval_context. simp subst_eval_context in H. injection H.
    intros. subst. auto.
  - cbn. rewrite H. auto.
  - simp subst_eval_context. injection H. intros. subst. auto.
  - cbn. rewrite H; auto.
Qed.

Lemma step_mfix t R MR (bodies : mfix_bodies [] MR R R) (c c' : comp t [] (R :: MR)) : 
  step_rel c c' ->
  step_rel (comp_mfix _ bodies c) (comp_mfix _ bodies c').
Proof.
  intros. dependent destruction H. 
  constructor.
  unfold step in *. simp observe. destruct (SmallStepSeq.observe c); try destruct b;
    try discriminate.
  f_equal. injection H. intros.  eapply step_mfix_eval_context. auto.
Qed.

Lemma normalize_eval_context_callv (t1 t2 : vtype) R MR
      (ca : call_syn t2 (R :: MR))
      (E : eval_context t1 (R :: MR) (inr ca) true) :
  normalize_eval_context ca E = (ca && E).
Proof.
  dependent induction E. simp normalize_eval_context. auto.
  simp normalize_eval_context. erewrite IHE; eauto.
Qed.

Lemma observe_comp_bec_inr_stuck t1 t2 MR (c : comp t1 [] MR) (ca : call_syn t2 MR)
      (E : eval_context t1 MR (inr ca) true) :
  SmallStepSeq.observe c = inl (bec (inr ca) E) -> stuck_call c ca E.
Proof.
  generalize dependent t2. dependent induction c; simp observe; intros; try discriminate.
  - destruct (SmallStepSeq.observe c1) eqn : Heq1; try destruct b.
    + injection H. intros. subst. inj_existT. subst. inj_existT. subst.
      constructor. eapply IHc1; eauto.
    + injection H. intros. subst. inj_existT. discriminate.
  - dependent destruction vn; try inversion x.
    simp observe in H. injection H. intros. subst. inj_existT.
    discriminate.
  - dependent destruction vn; try inversion x.
    simp observe in H. injection H. intros. subst. inj_existT.
    discriminate.
  - dependent destruction vf; try inversion x.
    simp observe in H. injection H. intros. subst. inj_existT.
    discriminate.
  - injection H. intros. subst. inj_existT. subst.
     inj_existT. subst. constructor.
  - destruct (SmallStepSeq.observe c) eqn : Heq1; try destruct b.
    + injection H. intros. discriminate.
    + injection H. intros. subst. inj_existT. discriminate.
  - destruct (SmallStepSeq.observe c) eqn : Heq1; try destruct b.
    + injection H. intros. discriminate.
    + injection H. intros. subst. inj_existT. discriminate.
  - destruct (SmallStepSeq.observe c) eqn : Heq1; try destruct b.
    + injection H. intros. discriminate.
    + injection H. intros. subst. inj_existT. discriminate.
Qed.

Lemma step_mfix_inv t R MR (bodies : mfix_bodies [] MR R R) (c : comp t [] (R :: MR)) c' : 
  step_rel (comp_mfix R bodies c) c' ->
 (exists v, c = comp_ret v) \/ (exists c'', step_rel c c'' /\ c' = comp_mfix R bodies c'') \/
 (exists tin tout (x : var (tin, tout) R ) (vin : closed_value tin) E, stuck_call c  (SmallStepSeq.callv VarZ x vin) E /\
            c' = comp_mfix R bodies ((subst_eval_context E (subst_comp_cons (nth_body bodies x) vin)))) \/
 (exists tin tout R' (xR : var R' MR) (x : var (tin, tout) R') (vin : closed_value tin) E,
     stuck_call c (SmallStepSeq.callv (VarS xR) x vin) E /\
       c' = push_eval_context _ E (comp_mfix_map bodies) (comp_call xR x vin)).
Proof.
  intros. dependent destruction H. unfold step in H. simp observe in H.
  destruct (SmallStepSeq.observe c) eqn : Heqc; try destruct b; try destruct r.
  - simp step_eval_context in H. simp subst_eval_context in H.
    injection H. intros. subst. right. left. eexists. split; eauto.
    constructor. unfold step. rewrite Heqc. simp step_eval_context. auto.
  - simp step_eval_context in H. injection H. intros. 
    destruct b.
    + assert (MR' = R :: MR). 
      { clear - E. dependent induction E; eauto. }
      subst. (*now we know c is stuck on c0 maybe from Heqc? *)
      simp step_eval_context in H. rewrite normalize_eval_context_callv in H.
      destruct c0. cbn in *. dependent destruction xR.
      * simp var_eq_neq in H. injection H. intros. subst. right. right.
        left. simp var_eq_elim. repeat eexists.
        apply observe_comp_bec_inr_stuck. auto.
      * simp var_eq_neq in H. Transparent remove_var. cbn in H. Opaque remove_var. 
        apply observe_comp_bec_inr_stuck in Heqc. do 3 right.
        injection H. intros. subst. repeat eexists. auto.
    + simp step_eval_context in H0.
      right. left. simp step_eval_context in H. injection H. intros.
      destruct (step_eval_context false (inr c0) E) eqn : Heq; try discriminate.
      injection H1. intros. subst. eexists. split; eauto.
      constructor. unfold step. rewrite Heqc. rewrite Heq. auto.
  - clear H. left. rename c0 into v0. exists v0. apply observe_inr. auto.
Qed.

Lemma step_mfix_ret t R MR (bodies : mfix_bodies [] MR R R) (c : comp t [] (R :: MR)) v :
  step c = inr v ->
  step_rel (comp_mfix R bodies c) (comp_ret v).
Proof.
  intros. constructor. unfold step in *. simp observe.
  destruct (SmallStepSeq.observe c); try destruct b; try discriminate.
  cbn. simp step_eval_context. cbn. simp subst_eval_context.
  simp step_bredex. injection H. intros. subst. auto.
Qed.



Lemma step_focused_mfix_context_VarZ (t1 t2 t3 : vtype) R MR
      (x : var (t2, t3) R) (v : closed_value t2) (bodies : mfix_bodies [] MR R R)
      (E : eval_context t1 (R :: MR) (inr (SmallStepSeq.callv (VarZ (l := MR)) x v)) true) : 
  step_eval_context _ _ (ev_mfix _ R bodies E) =
    Some (comp_mfix R bodies (subst_eval_context E (subst_comp_cons (nth_body bodies x) v) )).
Proof.
  simp step_eval_context.
  rewrite normalize_eval_context_callv.
  cbn. simp var_eq_neq. simp var_eq_elim. auto.
Qed.

Lemma step_focused_mfix_context_neq_VarZ (t1 t2 t3 : vtype) R1 R2 MR
      (xR : var R2 MR) (x : var (t2, t3) R2) (v : closed_value t2) 
      (bodies : mfix_bodies [] MR R1 R1)
      (E : eval_context t1 (R1 :: MR) (inr (SmallStepSeq.callv (VarS (b := R1) xR) x v)) true) : 
  step_eval_context _ _ (ev_mfix _ _ bodies E) = Some (push_eval_context (inr (SmallStepSeq.callv 
                                  (VarS xR) x v)) E (comp_mfix_map bodies)
                      (comp_call xR x v)).
Proof.
  simp step_eval_context. rewrite normalize_eval_context_callv. simp var_eq_neq.
  Transparent remove_var. cbn. Opaque remove_var. auto.
Qed.

Lemma stuck_call_observe t1 t2 MR (c : comp t1 [] MR) (ca : call_syn t2 MR)
      (E : eval_context t1 MR (inr ca) true) :
  stuck_call c ca E -> SmallStepSeq.observe c = inl (bec _ E).
Proof.
  intros Hstuck. dependent induction Hstuck.
  - simp observe. rewrite IHHstuck. auto.
  - simp observe. auto.
Qed.

Lemma stuck_call_step_VarZ t1 t2 t3 R MR (c : comp t1 [] (R :: MR)) bodies
      (x : var (t2, t3) R) (v : closed_value t2) E :
  stuck_call c (SmallStepSeq.callv VarZ x v) E ->
  step_rel (comp_mfix R bodies c) 
           (comp_mfix R bodies (subst_eval_context E (subst_comp_cons (nth_body bodies x) v)) ).
Proof.
  intros. constructor. unfold step. apply stuck_call_observe in H.
  simp observe. rewrite H. rewrite step_focused_mfix_context_VarZ. auto.
Qed.

Lemma stuck_call_step_neq_VarZ t1 t2 t3 R1 R2 MR (c : comp t1 [] (R1 :: MR)) bodies
      (xR : var R2 MR) (x : var (t2, t3) R2) (v : closed_value t2) E :
  stuck_call c (SmallStepSeq.callv (VarS xR) x v) E ->
  step_rel (comp_mfix R1 bodies c)
           (push_eval_context _ E (comp_mfix_map bodies) (comp_call xR x v)).
Proof.
  intros. constructor. unfold step. apply stuck_call_observe in H.
  simp observe. rewrite H. rewrite step_focused_mfix_context_neq_VarZ.
  auto.
Qed.

Lemma eval_rel_stuck_stuck_call_step t1 R MR (c1 c2 : comp t1 [] (R :: MR)) c3 r bodies :
  eval_rel_stuck c1 (inr c2) ->
  step_rel (comp_mfix R bodies c2) c3 ->
  eval_rel_stuck c3 r ->
  eval_rel_stuck (comp_mfix R bodies c1) r.
Proof.
  intros Hstuck. dependent induction Hstuck.
  - intros. econstructor. eapply step_mfix; eauto. eapply IHHstuck; eauto.
  - intros. econstructor; eauto.
Qed.

Lemma eval_rel_stuck_mfix_stuck_call_VarZ t1 t2 t3 R MR (c1 c2 : comp t1 [] (R :: MR)) r bodies
      (x : var (t2, t3) R) (v : closed_value t2) E :
  eval_rel_stuck c1 (inr c2) ->
  stuck_call c2 (SmallStepSeq.callv VarZ x v) E ->
  eval_rel_stuck 
    (comp_mfix R bodies (subst_eval_context E (subst_comp_cons (nth_body bodies x) v))) r ->
  eval_rel_stuck (comp_mfix R bodies c1) r.
Proof.
  intros. eapply eval_rel_stuck_stuck_call_step; eauto.
  eapply stuck_call_step_VarZ. auto.
Qed.

Lemma eval_rel_stuck_mfix_stuck_call_neq_VarZ t1 t2 t3 R1 R2 MR (c1 c2 : comp t1 [] (R1 :: MR)) r bodies
      (xR : var R2 MR) (x : var (t2, t3) R2) (v : closed_value t2) E :
  eval_rel_stuck c1 (inr c2) ->
  stuck_call c2 (SmallStepSeq.callv (VarS xR) x v) E ->
  eval_rel_stuck (push_eval_context _ E (comp_mfix_map bodies) (comp_call xR x v)) r ->
  eval_rel_stuck (comp_mfix R1 bodies c1) r.
Proof.
  intros. eapply eval_rel_stuck_stuck_call_step; eauto.
  eapply stuck_call_step_neq_VarZ. auto.
Qed.


Lemma eval_rel_stuck_mfix_ret t R MR (c : comp t [] (R :: MR)) bodies v :
  eval_rel_stuck c (inl v) ->
  eval_rel_stuck (comp_mfix R bodies c) (inl v).
Proof.
  intros Heval. dependent induction Heval.
  - econstructor. eapply step_mfix; eauto. eapply IHHeval; eauto.
  - econstructor. eapply step_mfix_ret; eauto. apply eval_rel_stuck_val.
    unfold step. simp observe. auto.
Qed.
(*
Lemma eval_rel_stuck_mfix_stuck t R MR (c : comp t [] (R :: MR)) bodies c' : 
  *)


Lemma push_eval_context_comp_call_stuck t tin tout R1 R2 MR
      (xR : var R2 MR) (x : var (tin, tout) R2) (vin : closed_value tin) 
      (E : eval_context t (R1 :: MR) (inr (SmallStepSeq.callv (VarS xR) x vin)) true) f : 
      exists E', stuck_call (push_eval_context _ E f (comp_call xR x vin)) (SmallStepSeq.callv xR x vin) E'.
Proof.
  dependent induction E.
  - simp push_eval_context. eexists. econstructor.
  - simp push_eval_context.
    specialize (IHE _ _ _ _ _ _ _ _ eq_refl eq_refl JMeq_refl eq_refl JMeq_refl f).
    destruct IHE. eexists. econstructor. eauto.
Qed.

(*
set (push_eval_context (inr (SmallStepSeq.callv (VarS xR) x vin)) E1 (comp_mfix_map bodies) (comp_call xR x vin)) as c'.
        (* may want to lift to a lemma *)
        assert (exists E, stuck_call c' ((SmallStepSeq.callv xR x vin))  E).
        { unfold c'.
          clear. dependent induction E1.
          - simp push_eval_context. eexists. econstructor.
          - specialize (IHE1 _ _ _ _ _ _ bodies _ _ eq_refl eq_refl JMeq_refl eq_refl JMeq_refl).
            destruct IHE1 as [E' HE']. simp push_eval_context. eexists.
            econstructor. eauto.
        }
        dest

*)


Inductive mfix_eval_ind t R MR (bodies : mfix_bodies [] MR R R) :
  forall (c1 : comp t [] (R :: MR)) (c2 : comp t [] MR), Prop := 
 | mei_stuck tin tout R' (xR : var R' MR) (x : var (tin, tout) R') (vin : closed_value tin) E c1:
   stuck_call c1 (SmallStepSeq.callv (VarS xR) x vin) E ->
   mfix_eval_ind t R MR bodies c1 (push_eval_context _ E (comp_mfix_map bodies) (comp_call xR x vin))
 | mei_body tin tout (x : var (tin, tout) R) (vin : closed_value tin) E c1 c2 :
   stuck_call c1 (SmallStepSeq.callv VarZ x vin) E ->
   mfix_eval_ind t R MR bodies (subst_eval_context E (subst_comp_cons (nth_body bodies x) vin)) c2 ->
   mfix_eval_ind t R MR bodies c1 c2
 | mei_step c1 c1' c2 :
   step_rel c1 c1' ->
   mfix_eval_ind t R MR bodies c1' c2 ->
   mfix_eval_ind t R MR bodies c1 c2.


Lemma eval_rel_stuck_inr_mfix_eval_ind t R MR (bodies : mfix_bodies [] MR R R) c1 c2 :
  eval_rel_stuck (t := t) (comp_mfix R bodies c1) (inr c2) -> mfix_eval_ind _ _ _ bodies c1 c2.
Proof.
  intros Heval.
  (* something odd is going on here*)
  dependent induction Heval.
  - apply step_mfix_inv in H as H'.
    destruct H' as [? | [? | [? | ?]]].
    + destruct H0. subst.
      dependent destruction H. simp subst_eval_context in Heval.
      simp step_bredex in Heval. dependent destruction Heval.
      dependent destruction H. inversion H.
    + destruct H0 as [c1' [Hc1'1 Hc1'2]]. subst.
      eapply mei_step; eauto.
    + destruct H0 as [tin [tout [x [vin [E [HE1 HE2]]]]]].
      subst. eapply mei_body; eauto.
    + destruct H0 as [tin [tout [R' [xR [x [vin [E [HE1 HE2]]]]]]]].
      subst. clear IHHeval. dependent destruction Heval.
      * specialize (push_eval_context_comp_call_stuck _ _ _ _ _ _ xR x vin E (comp_mfix_map bodies))
                   as [E' HE'].
        apply stuck_call_stuck' in HE'. dependent destruction H. rewrite HE' in H.
        discriminate.
      * constructor; auto.
  - dependent induction H.
Qed.

Lemma mfix_eval_ind_eval_rel_stuck_inr t R MR (bodies : mfix_bodies [] MR R R) c1 c2 :
  mfix_eval_ind _ _ _ bodies c1 c2 -> eval_rel_stuck (t := t) (comp_mfix R bodies c1) (inr c2).
Proof.
  intros Heval. induction Heval.
  - specialize push_eval_context_comp_call_stuck with (E := E) (f := comp_mfix_map bodies) 
      as [E' HE'].
    econstructor. eapply  stuck_call_step_neq_VarZ.
    eauto. eapply eval_rel_stuck_stuck. eauto.
  - econstructor; eauto. eapply stuck_call_step_VarZ. auto.
  - econstructor; eauto. eapply step_mfix; eauto.
Qed.
(*
Scheme Equality for vtype.
*)
(*
#[local] Instance dec_eq_vtype : EqDec vtype.
Proof.
  red. intros x. induction x.
  - intros y. destruct y; auto; right; intro; discriminate.
  - intros y. destruct y; auto; try (right; intro; discriminate).
    specialize (IHx y). destruct IHx; subst; auto. right. intro.
    injection H. auto.
  - admit.
  - intros y. destruct y; auto; try (right; intro; discriminate).
    specialize (IHx1 y1). specialize (IHx2 y2).
    destruct IHx1; destruct IHx2; subst; auto.
#[local] Instance uip_mfix_ctx : UIP mfix_ctx.
Proof.
  apply eqdec_uip. constructor.
Admitted.
*)

(* either need to develop the mutually recursive eqdec instance on vtype/mfix_ctx

*)
(*
Inductive push_eval_context_context : forall {t1 t2 MR1 MR2} (r : bredex t2 MR1 + call_syn t2 MR1)
          (E : eval_context t1 MR1 r true)
          (f : forall t Γ, comp t Γ MR1 -> comp t Γ MR2)
          (E' : eval_context t2 MR2 r true), eval_context t1 MR2 r true -> Prop := 
| pecc_hole t1 MR1 r (E : eval_context t1 MR1 r true) f  :
  @push_eval_context_context t1 t1 MR1 MR1 r ev_hole f E E
| pecc_let t1 t2 t3 MR1 MR2 r E1 c2 f E' E1' :
  @push_eval_context_context t1 t3 MR1 MR2 r E1 f E' E1' ->
  push_eval_context_context (t1 := t2) r (ev_let E1 c2) f E' (ev_let E1' (f _ [_] c2))

.

Lemma push_eval_context_context_ex : forall t1 t2 MR1 MR2 (r : bredex t2 MR1 + call_syn t2 MR1)
          (E : eval_context t1 MR1 r true)
          (f : forall t Γ, comp t Γ MR1 -> comp t Γ MR2)
          (E' : eval_context t2 MR2 r true),
    exists E'', @push_eval_context_context t1 t2 MR1 MR2 r E f E' E''.
Proof.
  intros t1 t2 MR1 MR2 r E. dependent induction E.
  - intros. exists E'. eapply pecc_hole. econstructor. *)
(*
Equations push_eval_context_context {t1 t2 MR1 MR2} (r : bredex t2 MR1 + call_syn t2 MR1)
          (E : eval_context t1 MR1 r true)
          (f : forall t Γ, comp t Γ MR1 -> comp t Γ MR2)
          (E' : eval_context t2 MR2 r true) : eval_context t1 MR2 r true :=
  push_eval_context_context r ev_hole f E' := E';
  push_eval_context_context r (ev_let E1 c2) f E' := 
    ev_let (push_eval_context_context r E1 f E') (f _ [_] c2).
    comp_let (push_eval_context r E1 f c) (f _ [_] c2).
*)


(* need to figure *)
(*
  what if I just relate this to observe in some way

  stuck_call c ca E -> ...

*)
