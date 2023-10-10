
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
Require Import Lia.
Require Import ITree.Basics.HeterogeneousRelations.
Require Import Coq.Classes.Morphisms.

Local Open Scope entree_scope.

From Paco Require Import paco.


Variant entree_step {E R} `{EncodedType E} (t1 t2 : entree E R) : Prop :=
  | step_intro : t1 ≅ Tau t2 -> entree_step t1 t2.


Inductive multi_step {E R} `{EncodedType E} : nat -> entree E R -> entree E R -> Prop :=
  | multi_step0 t1 t2 : t1 ≅ t2 -> multi_step 0 t1 t2
  | multi_stepS t1 t2 t3 n : multi_step n t2 t3 -> entree_step t1 t2 -> multi_step (S n) t1 t3.

Lemma entree_step_eutt {E R} `{EncodedType E} (t1 t2 : entree E R) : 
  entree_step t1 t2 -> t1 ≈ t2.
Proof.
  intros [Ht12]. rewrite Ht12, tau_eutt. reflexivity.
Qed.

#[global] Instance entree_step_proper {E R} `{EncodedType E} :
  Proper (eq_itree (E := E) (R1 := R) eq ==> eq_itree eq ==> Basics.flip Basics.impl) entree_step.
Proof.
  repeat intro. inversion H2. subst. constructor. rewrite H0, H3.
  pstep. constructor. left. symmetry in H1. auto.
Qed.

#[global] Instance multi_step_proper {E R} `{EncodedType E} :
  Proper (eq ==> eq_itree (E := E) (R1 := R) eq ==> eq_itree eq ==> Basics.flip Basics.impl) multi_step.
Proof.
  repeat intro. subst. generalize dependent x0. generalize dependent x1. induction H3; intros.
  - constructor. rewrite H1, H0, <- H2. reflexivity.
  - rewrite <- H1 in H0. destruct H0. rewrite H0 in H1.  econstructor. eapply IHmulti_step; eauto.
    reflexivity. constructor. auto.
Qed.

Lemma multi_step_eutt {E R} `{EncodedType E} n (t1 t2 : entree E R) :
  multi_step n t1 t2 -> t1 ≈ t2.
Proof.
  intros Hn. induction Hn. rewrite H0. reflexivity. 
  destruct H0. rewrite H0, tau_eutt. auto.
Qed.

Lemma multi_step_eq_itree_r {E R} `{EncodedType E} n (t1 t2 t3 : entree E R) :
  multi_step n t1 t2 -> multi_step n t1 t3 -> t2 ≅ t3.
Proof.
  revert t1 t2 t3. induction n.
  - intros. dependent destruction H0. rewrite H0 in H1. dependent destruction H1.
    auto.
  - intros. dependent destruction H0.
    dependent destruction H1. dependent destruction H2.
    dependent destruction H3. rewrite H1 in H3.
    apply eqit_inv_Tau in H3. rewrite <- H3 in H2. eauto.
Qed.

Lemma eutt_ret_multi_step {E R} `{EncodedType E} (t : entree E R) (r : R) :
  t ≈ ret r -> exists n, multi_step n t (ret r).
Proof.
  cbn. intros Hret. punfold Hret. red in Hret.
  cbn in *. remember (observe t) as ot. generalize dependent t. remember (RetF r) as x.
  hinduction Hret before r; intros; try inversion Heqx.
  - subst. apply simpobs in Heqot.  exists 0. constructor.
    symmetry. auto.
  - specialize (IHHret H0 t1 eq_refl). destruct IHHret as [n Hn].
    exists (S n). apply simpobs in Heqot. rewrite <- Heqot. rewrite H0 in Hn. 
    econstructor; eauto. constructor. reflexivity.
Qed.

Lemma multi_step_add {E R} `{EncodedType E} (t1 t2 t3 : entree E R) n m : 
  multi_step n t1 t2 -> multi_step m t2 t3 -> multi_step (n + m) t1 t3.
Proof.
  intros Hn. revert m. generalize dependent t3. induction Hn.
  - simpl. setoid_rewrite H0. auto.
  - cbn. intros t4 m Ht4. apply IHHn in Ht4. econstructor; eauto.
Qed.

Ltac remember_eq_itree t1 n :=
  let H1 := fresh in
  let H2 := fresh "Heq" in
  remember t1 as n eqn : H1; assert (H2 : t1 ≅ n); try (subst; reflexivity); clear H1.

Lemma multi_step_bind E R1 R2 `{EncodedType E} (t t': entree E R1) (k : R1 -> entree E R2) n :
  multi_step n t t' ->
  multi_step n (bind t k) (bind t' k).
Proof.
  generalize dependent t. generalize dependent t'. revert k.
  induction n.
  - intros. dependent destruction H0. rewrite H0.
    constructor. reflexivity.
  - intros. dependent destruction H0. dependent destruction H1.
    rewrite H1. setoid_rewrite bind_tau. econstructor. eauto. constructor.
    reflexivity.
Qed.

Lemma multi_step_ret_bind_inv E R1 R2 `{EncodedType E} (t : entree E R1) (k : R1 -> entree E R2) s n : 
      multi_step n (x <- t;; k x) (ret s) -> 
      exists m1 m2 r, m1 + m2 = n /\ multi_step m1 t (ret r) /\ multi_step m2 (k r) (ret s).
Proof.
  remember_eq_itree (x <- t;; k x) t0.
  intros Hn. dependent induction Hn.
  - rewrite H0 in Heq. exists 0, 0. destruct (eq_itree_case t) as [[r Hr] | [[t' Ht'] | [e [k' Hek]] ]].
    + setoid_rewrite Hr. exists r. split; auto. split.
      constructor. reflexivity.
      constructor. rewrite Hr in Heq. setoid_rewrite bind_ret_l in Heq. auto.
    + rewrite Ht' in Heq. setoid_rewrite bind_tau in Heq. pinversion Heq; inversion CHECK.
    + rewrite Hek in Heq. setoid_rewrite bind_vis in Heq. pinversion Heq.
  - destruct H0. rewrite H0 in Heq.
    destruct (eq_itree_case t) as [[r Hr] | [[t' Ht'] | [e [k' Hek]] ]].
    + exists 0, (S n), r. split; auto. split. constructor. auto.
      rewrite Hr in Heq. setoid_rewrite bind_ret_l in Heq. econstructor; eauto.
      constructor. auto.
    + rewrite Ht' in Heq. setoid_rewrite bind_tau in Heq.  apply eqit_inv_Tau in Heq.
      eapply IHHn in Heq; eauto. destruct Heq as [m1 [m2 [r [Hm [Hstep Hk]]]]].
      exists (S m1), m2, r. split. lia. split; auto. econstructor; eauto. constructor; auto.
    + rewrite Hek in Heq. clear - Heq. setoid_rewrite bind_vis in Heq. pinversion Heq.
      inversion CHECK.
Qed.

Lemma multi_step_vis_bind_inv E R1 R2 `{EncodedType E} (t : entree E R1) (k1 : R1 -> entree E R2)
      (e : E) (k2 : encodes e -> entree E R2) n :
  multi_step n (x <- t;; k1 x) (Vis e k2) ->
  (exists m1 m2 r, m1 + m2 = n /\ multi_step m1 t (ret r) /\ multi_step m2 (k1 r) (Vis e k2)) \/
  (exists k1', multi_step n t (Vis e k1') /\ forall x, y <- k1' x;; k1 y ≅ k2 x).
Proof.
  remember_eq_itree (x <- t;; k1 x) t0.
  intros Hn. dependent induction Hn.
  - rewrite H0 in Heq.
    destruct (eq_itree_case t) as [[r Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
    + rewrite Hr in Heq. setoid_rewrite bind_ret_l in Heq. left. exists 0, 0, r.
      split. auto. split; constructor; auto.
    + exfalso. rewrite Ht' in Heq. setoid_rewrite bind_tau in Heq. pinversion Heq; inversion CHECK.
    + rewrite Hek in Heq. setoid_rewrite bind_vis in Heq.
      assert (e = e'). pinversion Heq. subst. auto. subst.
      specialize (eqit_Vis_inv _ _ _ _ _ _ Heq) as Heqk. right.
      exists k'. split; auto. constructor. auto.
  - destruct H0. rewrite H0 in Heq.
    destruct (eq_itree_case t) as [[r Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
    + rewrite Hr in Heq. setoid_rewrite bind_ret_l in Heq.
      left. exists 0, (S n), r. split. auto. split. constructor. auto.
      econstructor; eauto. constructor. auto.
    + rewrite Ht' in Heq. setoid_rewrite bind_tau in Heq.
      apply eqit_inv_Tau in Heq. eapply IHHn in Heq; eauto.
      destruct Heq as [ [m1 [m2 [r [Hm [Hstep1 Hstep2]]]] ] | [k1' [Hstep Heq] ]].
      * left. exists (S m1), m2, r. split. lia. split; auto.
        econstructor; eauto. constructor. auto.
      * right. exists k1'. split; auto.
        econstructor; eauto. constructor. auto.
    + rewrite Hek in Heq. setoid_rewrite bind_vis in Heq.
      pinversion Heq. inversion CHECK.
Qed.

Lemma multi_step_mapE_inv_ret D1 D2 R `{EncodedType D1} `{EncodedType D2}
      (h : handler D1 D2) t (r : R) j : 
  valid_handler h ->
  multi_step j (mapE h t) (ret r) ->
  multi_step j t (ret r).
Proof.
  intros H1 H2. remember (mapE h t) as x.
  assert (x ≅ mapE h t). subst. reflexivity. clear Heqx.
  remember (ret r) as y.
  assert (y ≅ ret r). subst. reflexivity. clear Heqy.
  generalize dependent y. generalize dependent x. generalize dependent t.
  induction j.
  - intros. rewrite H3, H4 in H2. constructor.  dependent destruction H2.
    destruct (eq_itree_case t) as [[r' Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
    + setoid_rewrite Hr in H2. setoid_rewrite mapE_ret in H2.
      apply eqit_Ret_inv in H2.
      subst. auto.
    + rewrite Ht', mapE_tau in H2. pinversion H2. inversion CHECK.
    + rewrite Hek, mapE_vis in H2. destruct (h e'). pinversion H2.
  - intros. rewrite H3, H4 in H2. clear H3 H4. dependent destruction H2.
    destruct (eq_itree_case t) as [[r' Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
    + rewrite Hr in H3. setoid_rewrite mapE_ret in H3.
      dependent destruction H3. pinversion H3. inversion CHECK.
    + rewrite Ht', mapE_tau in H3. dependent destruction H3.
      apply eqit_inv_Tau in H3. econstructor; eauto.
      eapply IHj with (t := t'); eauto. symmetry. auto.
      reflexivity. constructor. auto.
    + rewrite Hek, mapE_vis in H3. destruct (h e').
      dependent destruction H3. pinversion H3. inversion CHECK.
Qed.

Lemma multi_step_mapE_vis D1 D2 R `{EncodedType D1} `{EncodedType D2}
      (h : handler D1 D2) t e (k : _ -> entree D1 R) j :
  valid_handler h ->
  multi_step j t (Vis e k) ->
  multi_step j (mapE h t) (let 'd' && f := h e in Vis d' (fun x : encodes d' => mapE h (k (f x)))).
Proof.
  intros.
  remember (Vis e k) as y.
  assert (y ≅ Vis e k). subst. reflexivity.
  clear Heqy.
  generalize dependent y. generalize dependent t. generalize dependent e.
  induction j.
  - intros. dependent destruction H2. rewrite H2, H3.
    constructor. rewrite mapE_vis. reflexivity.
  - intros. dependent destruction H2. dependent destruction H3.
    rewrite H3, mapE_tau. econstructor. eauto.
    constructor. reflexivity.
Qed.

Lemma multi_step_mapE_inv_vis D1 D2 R `{EncodedType D1} `{EncodedType D2}
      (h : handler D1 D2) t e (k : _ -> entree D1 R) j : 
  valid_handler h ->
  multi_step j (mapE h t) (let 'd' && f := h e in Vis d' (fun x : encodes d' => mapE h (k (f x)))) ->
  exists e' k', multi_step j t (Vis e' k').
Proof.
  intros H1 H2. remember (mapE h t) as x.
  assert (x ≅ mapE h t). subst. reflexivity. clear Heqx.
  remember ((let 'd' && f := h e in Vis d' (fun x : encodes d' => mapE h (k (f x))))) as y.
  assert (y ≅ (let 'd' && f := h e in Vis d' (fun x : encodes d' => mapE h (k (f x))))).
  subst. reflexivity. clear Heqy. generalize dependent x. generalize dependent y.
  generalize dependent e.
  generalize dependent t. induction j.
  - intros. rewrite H3, H4 in H2. dependent destruction H2. clear H3 H4.
    destruct (h e) as [d g] eqn : Heq.
    destruct (eq_itree_case t) as [[r' Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
    + setoid_rewrite Hr in H2. setoid_rewrite mapE_ret in H2.
      pinversion H2.
    + rewrite Ht', mapE_tau in H2. pinversion H2. inversion CHECK.
    + rewrite Hek, mapE_vis in H2. destruct (h e') eqn : Heq'.
      assert (x0 = d).
      pinversion H2. auto. subst. 
      eexists. eexists. constructor. eauto.
  - intros. rewrite H3, H4 in H2. clear H3 H4.
    destruct (h e) as [d g] eqn : Heq.
    destruct (eq_itree_case t) as [[r' Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
    + setoid_rewrite Hr in H2. setoid_rewrite mapE_ret in H2.
      dependent destruction H2. dependent destruction H3.
      pinversion H3. inversion CHECK.
    + rewrite Ht', mapE_tau in H2. dependent destruction H2.
      dependent destruction H3. apply eqit_inv_Tau in H3. symmetry in H3.
      eapply IHj with (e := e) in H2; eauto.
      * setoid_rewrite Ht'. destruct H2 as [e' [k' Hek']].
        exists e', k'. econstructor; eauto. constructor. reflexivity.
      * rewrite Heq. reflexivity.
    + rewrite Hek in H2.
      dependent destruction H2.
      dependent destruction H3.
      clear - H3. rewrite mapE_vis in H3.
      destruct (h e'). pinversion H3. inversion CHECK.
Qed.

Lemma multi_step_mapE_inv_vis' D1 D2 R `{EncodedType D1} `{EncodedType D2}
      (h : handler D1 D2) t e e' (k : _ -> entree D1 R) k' j : 
  valid_handler h ->
  multi_step j (mapE h t) (let 'd' && f := h e in Vis d' (fun x : encodes d' => mapE h (k (f x)))) ->
  multi_step j t (Vis e' k') ->
  projT1 (h e) = projT1 (h e').
Proof.
  intros. apply multi_step_eutt in H2.
  apply multi_step_eutt in H3.
  rewrite H3 in H2. rewrite mapE_vis in H2.
  destruct (h e). destruct (h e'). cbn.
  pinversion H2. auto.
Qed.

Lemma JMeq_mapE_aux:
  forall A B C (MR1 MR2 : mfix_ctx)
    (h : handler (denote_mrec_ctx (denote_mfix_ctx MR1)) (denote_mrec_ctx (denote_mfix_ctx MR2)))
    (e' : denote_mrec_ctx (denote_mfix_ctx MR1)) (d :A -> B)
    (e0 : C -> A) (k' : A -> entree (denote_mrec_ctx (denote_mfix_ctx MR1)) B)
    (a : A),
    valid_handler h ->
    (forall x : C, mapE h (k' (e0 x)) ≅ Ret (d (e0 x))) ->
    A = B -> d ~= (@id B) -> A = C -> e0 ~= (@id A) -> eqit eq false false (k' a) (Ret (d a)).
Proof.
  intros. subst. subst. unfold id in *.
  specialize (H0 a).
  destruct (eq_itree_case (k' a)) as [[r' Hr] | [[t' Ht'] | [e'' [k'' Hek]] ]].
  - setoid_rewrite Hr in H0. setoid_rewrite mapE_ret in H0. apply eqit_Ret_inv in H0.
    subst. auto.
  - rewrite Ht', mapE_tau in H0. pinversion H0. inversion CHECK.
  - rewrite Hek, mapE_vis in H0. destruct (h e''). pinversion H0.
Qed.

Lemma mapE_perm_handler_call_term_aux':
  forall (t2 : vtype) (MR1 MR2 : mfix_ctx) (t0 : vtype) 
    (R : call_frame) (yR : var R MR2) (x : var (t0, t2) R) (r1 r2 : denote_type t0)
    h (vf : forall R, var R MR1 -> var R MR2) t,
    var_map_handler_rel h vf ->
    valid_handler h ->
    (mapE h t) ≅ (call_term x yR r1) ->
    exists xR, t ≅ call_term x xR r1 /\ vf _ xR = yR.
Proof.
  intros. unfold call_term in *.
  destruct (call_mrec x yR r1) eqn : Heq1. setoid_rewrite bind_trigger in H1.
  destruct (eq_itree_case t) as [[r' Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
  rewrite Hr in H1. setoid_rewrite mapE_ret in H1. pinversion H1.
  rewrite Ht', mapE_tau in H1. pinversion H1. inversion CHECK.
  setoid_rewrite Hek. rewrite Hek, mapE_vis in H1.
  destruct (h e') eqn : Heq2. assert (x1 = x0). pinversion H1. auto.
  subst.
  specialize (call_extract _ (e')) as [R2 [xR [tin' [tout' [y [vvin' Hvvin']]]] ]].

  red in H.
  destruct (call_mrec y xR vvin') eqn : Heq3. cbn in Hvvin'. subst.
  eapply H in Heq2 as ?; eauto.
  assert (projT1 (call_mrec y (vf R2 xR) vvin') = projT1 (call_mrec x yR r1)). subst.
  rewrite Heq1. auto.
  eapply call_term_bind_inv_aux1 in H3 as ?. apply var_eq_surj in H4 as ?. subst.
  apply var_eq_eq in H4. subst. exists xR.
  eapply call_term_bind_inv_aux2 in H3 as ?. destruct H2.
  apply var_eq_surj in v as ?. injection X. intros. subst. subst.
  apply var_eq_eq in v. subst. rewrite Heq3. split; auto.
  setoid_rewrite bind_trigger. apply eqit_Vis. intros.
  specialize (H0 e') as H'. destruct H'. rewrite Heq2 in H4. cbn in H4.
  clear H3 X.
  specialize (call_mrec_encodes _ _ _ _ x xR vvin') as Henc1.
  specialize (call_mrec_cont _ _ _ _ x xR vvin') as Henc2.
  rewrite Heq3 in Henc1, Henc2.
  rewrite Heq2 in H2. cbn in H2.
  eapply JMeq_mapE_aux with (e0 := e); eauto.
  intros. eapply eqit_Vis_inv in H1. rewrite H1. apply eqit_Ret.
  symmetry. 
  specialize (call_mrec_encodes _ _ _ _ x (vf _ xR) vvin') as Henc3.
  specialize (call_mrec_cont _ _ _ _ x (vf _ xR) vvin') as Henc4.
  rewrite Heq1 in Henc3, Henc4.
  eapply JMeq_comp'; eauto.
Qed.

Lemma mapE_call_term_inv:
  forall (tin tout : vtype) (R : call_frame) (MR1 MR2 : mfix_ctx) (xR : var R MR1) (vvin : denote_type tin)
    (h : handler (denote_mrec_ctx (denote_mfix_ctx MR1)) (denote_mrec_ctx (denote_mfix_ctx MR2)))
    (vf : forall R0 : call_frame, var R0 MR1 -> var R0 MR2)
    (t : entree (denote_mrec_ctx (denote_mfix_ctx MR1)) (denote_type tout)) (x : var (tin, tout) R),
    mapE h t ≅ call_term x (vf R xR) vvin ->
    var_map_handler_rel h vf ->
    valid_handler h -> (forall (R0 : call_frame) (x0 y : var R0 MR1), vf R0 x0 = vf R0 y -> x0 = y) -> t ≅ call_term x xR vvin.
Proof.
  intros tin tout R MR1 MR2 xR vvin h vf t x H Hhf Hh Hinj.
  assert (mapE h t ≅ mapE h (call_term x xR vvin)).
  erewrite mapE_perm_handler_call_term_aux; eauto. Locate mapE_perm_handler_call_term_aux. clear H.
  rename H0 into Hmap.
  unfold call_term in *. destruct (call_mrec x xR vvin) eqn : HeqxR.
  setoid_rewrite bind_trigger. setoid_rewrite bind_trigger in Hmap.
  setoid_rewrite mapE_vis in Hmap.
  destruct (h x0) eqn : Heqx0. 
  assert ( Vis x1 (fun x : encodes x1 => mapE h (ret (d (e x)))) ≅ Vis x1 (fun x => ret (d (e x)))).
  apply eqit_Vis. intros. setoid_rewrite mapE_ret. reflexivity.
  rewrite H in Hmap. clear H.
  destruct (eq_itree_case t) as [[r' Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
  + rewrite Hr in Hmap. setoid_rewrite mapE_ret in Hmap. pinversion Hmap.
  + rewrite Ht', mapE_tau in Hmap. pinversion Hmap. inversion CHECK.
  + rewrite Hek, mapE_vis in Hmap.
    destruct (h e') eqn : Heqe'. rewrite Hek.
    assert (x1 = x2). pinversion  Hmap. auto.
    subst x1.
    assert (e' = x0). 
    { 
      eapply Hhf in HeqxR as ?; eauto. specialize (H Heqx0).
      clear Hmap. subst x2.
      specialize (call_extract _ (e')) as [R2 [yR [tin' [tout' [y [vvin' Hvvin']]]] ]].
      subst e'. enough (projT1 (call_mrec y yR vvin') = projT1 (call_mrec x xR vvin)).
      rewrite HeqxR in H; auto.
      assert (projT1 (h (projT1 (call_mrec y yR vvin')) ) = projT1 (call_mrec y (vf _ yR) vvin')).
      { red in Hhf. destruct (h (projT1 (call_mrec y yR vvin'))) eqn : ?.  erewrite Hhf; eauto.
        Unshelve. 2 : apply (projT2 (call_mrec y yR vvin')). destruct (call_mrec y yR vvin').
        auto.
      } rewrite Heqe' in H. simpl in H.
      eapply call_term_bind_inv_aux1 in H as ?. apply var_eq_surj in H0 as ?.
      subst R2. apply var_eq_eq in H0.
      assert (xR = yR). eapply Hinj. auto.
      subst.
      eapply call_term_bind_inv_aux2 in H as ?. destruct H1.
      apply var_eq_surj in v as ?. injection X. intros. subst.
      subst. apply var_eq_eq in v. subst. auto.
    }
    subst x0. apply eqit_Vis. intros.
    assert (forall x, mapE h (k' (e0 x)) ≅ ret (d (e x))).
    intros. eapply eqit_Vis_inv in Hmap; eauto.
    specialize (call_mrec_encodes _ _ _ _ x xR vvin) as Henc1.
    specialize (call_mrec_cont _ _ _ _ x xR vvin) as Henc2. rewrite HeqxR in Henc1, Henc2.
    cbn in *. rewrite Heqx0 in Heqe'. inj_existT. subst.
    specialize (Hh e') as H'. destruct H' as [Henc3 Henc4]. rewrite Heqx0 in Henc3, Henc4.
    cbn in *. eapply JMeq_mapE_aux; eauto.
Qed.



Lemma multi_step_call_term_bind_ex tin tout R MR (xR : var R MR) (x : var (tin, tout) R) (vvin : denote_type tin)
      S (k : _ -> mtree _ S) t n :
  multi_step n t (bind (call_term x xR vvin) k) ->
  exists t', t ≅ bind t' k /\ multi_step n t' (call_term x xR vvin).
Proof.
  revert k t. induction n.
  - intros. dependent destruction H. exists (call_term x xR vvin).
    split; auto. constructor. reflexivity.
  - intros. dependent destruction H. dependent destruction H1. 
    eapply IHn in H as [t' [Ht'1 Ht'2]]. exists (Tau t').
    rewrite H0. setoid_rewrite bind_tau. split. pstep. constructor. auto.
    econstructor. eauto. econstructor. pstep. constructor. left.
    enough (t' ≅ t'); auto. reflexivity.
Qed.

Lemma id_eq_inv A B (Heq1 : A = B) (Heq2 : B = A) (a : A) :
  id_eq Heq2 (id_eq Heq1 a) = a.
Proof.
  subst. dependent destruction Heq2. simp id_eq. auto.
Qed.
(* A : encodes x0
   B : denote_type tout
   C : encodes e'

*)
Lemma multi_step_mapE_call_term_bind_ex_aux1:
  forall A B C (e : A -> C) (d : A -> B)
    (H1' : C = B) (a : A), 
    A = B -> e ~= (@id C) -> d ~= (@id B) ->
    id_eq H1' (e a) = d a.
Proof.
  intros. subst. simp id_eq. auto.
Qed.
(*
A : encodes x0
B : encodes e'
C : denote_type tout
*)
Lemma multi_step_mapE_call_term_bind_ex_aux2:
  forall A B C (e : A -> B ) (x1 : C)
    (Henc2 : C = A) (H1 : C = B), 
    e ~= (@id B) -> 
    e (id_eq Henc2 x1) = id_eq H1 x1.
Proof.
  intros. subst. simp id_eq. auto.
Qed.
          
(*
A : encodes x0
B : denote_type tout
*)

Lemma multi_step_mapE_call_term_bind_ex_aux3:
  forall A B (d  : A -> B)
    (x1 : B) (Henc2 : B = A), 
    d ~= (@id B) ->
    d (id_eq Henc2 x1) = x1.
Proof.
  intros. subst. simp id_eq. auto.
Qed.

Lemma multi_step_mapE_call_term_bind_ex tin tout R MR1 MR2 yR (x : var (tin, tout) R) (vvin : denote_type tin)
      S (k : _ -> mtree (denote_mfix_ctx MR2) S) (t : mtree (denote_mfix_ctx MR1) S) (h : handler _ _) 
       (vf : forall R0, var R0 MR1 -> var R0 MR2) n :
  var_map_handler_rel h vf -> valid_handler h ->
  multi_step n (mapE h t) (bind (call_term x yR vvin) k) ->
  exists (t' : mtree _ _) (k' : _ -> mtree _ _), 
    t ≅ bind t' k' /\ multi_step n (mapE h t') (call_term x yR vvin) /\ (forall x, k x ≅ mapE h (k' x)).
Proof.
  revert k t. induction n.
  - intros k t H H0 H2. subst. dependent destruction H2. 
    destruct (eq_itree_case t) as [[r' Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
    + rewrite Hr in H2. setoid_rewrite mapE_ret in H2. unfold call_term in H2.
      destruct (call_mrec x yR vvin). setoid_rewrite bind_trigger in H2.
      setoid_rewrite bind_vis in H2. pinversion H2.
    + exfalso. rewrite Ht', mapE_tau in H2. unfold call_term in H2.
      destruct (call_mrec x yR vvin). setoid_rewrite bind_trigger in H2.
      setoid_rewrite bind_vis in H2. pinversion H2. inversion CHECK.
    + specialize (call_mrec_encodes _ _ _ _ x yR vvin) as Henc1.
      (* need a function from denote_type tout to encode e'*)
      rewrite Hek, mapE_vis in H2.
      destruct (h e') eqn : Heqhe'. unfold call_term in H2.
      destruct (call_mrec x yR vvin) eqn : Heqcall.
      setoid_rewrite bind_trigger in H2. setoid_rewrite bind_vis in H2.
      assert (x1 = x0). pinversion H2. auto.
      subst. 
      assert (denote_type tout = encodes e').
      { red in H0. specialize (H0 e') as H1. destruct H1. rewrite Heqhe' in H1. cbn in H1.
        rewrite H1. specialize (call_mrec_encodes _ _ _ _ x yR vvin) as Henc2.
        rewrite Heqcall in Henc2. setoid_rewrite Henc2. auto.
      } assert (H1' : encodes e' = denote_type tout). rewrite H1. auto.
      exists (Vis e' (fun x => ret (id_eq H1' x))).
      exists (fun x => k' (id_eq H1 x)).
      split; [ | split].
      * rewrite Hek. setoid_rewrite bind_vis. apply eqit_Vis. 
        intros. setoid_rewrite bind_ret_l. rewrite id_eq_inv.
        reflexivity.
      * constructor. rewrite mapE_vis. rewrite Heqhe'.
        unfold call_term. rewrite Heqcall. setoid_rewrite bind_trigger.
        apply eqit_Vis. intros. rewrite mapE_ret. apply eqit_Ret.
        specialize (call_mrec_encodes _ _ _ _ x yR vvin) as Henc2.
        specialize (call_mrec_cont _ _ _ _ x yR vvin) as Henc3.
        rewrite Heqcall in Henc2, Henc3. cbn in Henc2, Henc3.
        specialize (H0 e') as ?. rewrite Heqhe' in H3. cbn in H3.
        destruct H3.
        eapply multi_step_mapE_call_term_bind_ex_aux1; eauto.
      * intros. specialize (call_mrec_encodes _ _ _ _ x yR vvin) as Henc2.
        rewrite Heqcall in Henc2. cbn in Henc2. symmetry in Henc2.
        eapply eqit_Vis_inv with (a := id_eq Henc2 x1) in H2. symmetry.
        assert (e (id_eq Henc2 x1) = id_eq H1 x1).
        specialize (H0 e'). destruct H0. rewrite Heqhe' in H3. cbn in H3.
        eapply multi_step_mapE_call_term_bind_ex_aux2; eauto.
        assert (d (id_eq Henc2 x1) = x1).
        eapply multi_step_mapE_call_term_bind_ex_aux3.
        specialize (call_mrec_cont _ _ _ _ x yR vvin) as Henc3.
        rewrite Heqcall in Henc3. auto.
        rewrite H3, H4 in H2. rewrite H2. setoid_rewrite bind_ret_l. 
        reflexivity.
  - intros. dependent destruction H1. dependent destruction H3. 
    destruct (eq_itree_case t) as [[r' Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
    + rewrite Hr in H2. setoid_rewrite mapE_ret in H2. pinversion H2. inversion CHECK.
    + rewrite Ht', mapE_tau in H2. apply eqit_inv_Tau in H2. rewrite <- H2 in H1.
      eapply IHn in H1; eauto. destruct H1 as [t'' [k'' [? [? ?]]]].
      setoid_rewrite Ht'. exists (Tau t''), k''. setoid_rewrite bind_tau.
      split. pstep. constructor. auto. split; auto. setoid_rewrite mapE_tau.
      econstructor. eauto. constructor. reflexivity.
    + rewrite Hek, mapE_vis in H2. destruct (h e'). pinversion H2. inversion CHECK.
Qed.
(*
Lemma multi_step_mapE_call_term_inv tin tout R S MR1 MR2 (xR : var R MR1) (yR : var R MR2) (x : var (tin, tout) R) (vvin : denote_type tin) t (k : _ -> mtree _ S)
      h (vf : forall R0, var R0 MR1 -> var R0 MR2) n : 
  (forall R0 (x y: var R0 MR1), vf _ x = vf _ y -> x = y) ->
  var_map_handler_rel h vf -> valid_handler h ->
  vf R xR = yR ->
  multi_step n (mapE h t) (bind (call_term x yR vvin) k) ->
  exists k', multi_step n t (bind (call_term x xR vvin) k').
*)

(* this is hideous, may need to add a continuation to bind to
   get that lemma by combining this with 
   multi_step_vis_bind_inv
   actually that does not give us what we want 

   but I think what I do what is derivable from bind metatheory and this
   gross lemma

  t ->j bind call k -> exists t1 k,
  t ≅ bind t1 k /\ t1 -> j call ?

 *)
(*
Lemma 
  mapE h t ≅ call_term x yR vvin ->
  exists xR, t ≅ call_term 
*)
Lemma multi_step_mapE_call_term_inv tin tout R MR1 MR2 (yR : var R MR2) (x : var (tin, tout) R) (vvin : denote_type tin) t 
      h (vf : forall R0, var R0 MR1 -> var R0 MR2) n : 
  (forall R0 (x y: var R0 MR1), vf _ x = vf _ y -> x = y) ->
  var_map_handler_rel h vf -> valid_handler h ->
  multi_step n (mapE h t) (call_term x yR vvin) ->
  exists xR, multi_step n t (call_term x xR vvin) /\ vf R xR = yR.
Proof.
  intros Hinj Hhf Hh Hstep. subst.
  remember (mapE h t) as xt.
  assert (xt ≅ mapE h t). subst. reflexivity.
  remember ((call_term x yR vvin)) as yt.
  assert (yt ≅ (call_term x yR vvin)). subst. reflexivity.
  clear Heqyt Heqxt.
  generalize dependent x. generalize dependent t.
  generalize dependent xt. generalize dependent yt.
  induction n.
  - intros. dependent destruction Hstep. rewrite H1, H0 in H.
    clear H0 H1. eapply mapE_perm_handler_call_term_aux' in H as ?; eauto.
    destruct H0 as [xR [H1 H2]]. subst. exists xR. split; auto.
    constructor. auto.
  - intros. dependent destruction Hstep.
    dependent destruction H. rewrite H in H0.
    destruct (eq_itree_case t) as [[r' Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
    + rewrite Hr in H0. setoid_rewrite mapE_ret in H0. pinversion H0. inversion CHECK.
    + rewrite Ht', mapE_tau in H0. apply eqit_inv_Tau in H0. eapply IHn in Hstep; eauto.
      destruct Hstep as [xR [Hstep HxR]]. subst. exists xR.
      split; auto. rewrite Ht'. econstructor. eauto. constructor. reflexivity.
    + rewrite Hek, mapE_vis in H0. destruct (h e'). pinversion H0. inversion CHECK.
Qed.

Lemma multi_step_mapE_call_term_inv' tin tout R S MR1 MR2 (yR : var R MR2) (x : var (tin, tout) R) (vvin : denote_type tin) t (k : _ -> mtree _ S)
      h (vf : forall R0, var R0 MR1 -> var R0 MR2) n : 
  (forall R0 (x y: var R0 MR1), vf _ x = vf _ y -> x = y) ->
  var_map_handler_rel h vf -> valid_handler h ->
  multi_step n (mapE h t) (bind (call_term x yR vvin) k) ->
  exists xR k', multi_step n t (bind (call_term x xR vvin) k') /\ vf R xR = yR /\ (forall x, k x ≅ mapE h (k' x)).
Proof.
  intros Hinj Hvf Hh Hstep. eapply multi_step_mapE_call_term_bind_ex in Hstep as Hstep'; eauto.
  destruct Hstep' as [t' [k' [Ht'1 [Ht'2 Ht'3]]]].
  eapply multi_step_mapE_call_term_inv in Ht'2; eauto. destruct Ht'2 as [xR [Ht'4 HxR]].
  subst. exists xR. exists k'. split; [ | split]; eauto.
  rewrite Ht'1. apply multi_step_bind; eauto.
Qed.

Lemma multi_step_perm_inv S tin tout R MR1 MR2 (Hperm : perm MR1 MR2) 
      (yR : var R MR2) (x : var (tin, tout) R) (vvin : denote_type tin) t 
      (k : _ -> mtree _ S) n : 
  multi_step n (map_perm _ _ (perm_denote Hperm)  t) (bind (call_term x yR vvin) k) ->
  exists xR k', multi_step n t (bind (call_term x xR vvin) k') /\ perm_var xR Hperm = yR /\ 
             (forall x, k x ≅ map_perm  _ _ (perm_denote Hperm) (k' x)).
Proof.
  intros. eapply multi_step_mapE_call_term_inv' in H; try eapply perm_var_map_handler_rel with (Hperm := Hperm); try apply valid_perm_handler; 
    try apply perm_var_inj; eauto.
Qed.



Lemma multi_step_lift_inv S tin tout R MR1 MR2
      (yR : var R (MR1 ++ MR2)) (x : var (tin, tout) R) (vvin : denote_type tin) t 
   (k : _ -> mtree _ S) n : 
  multi_step n (mapE (lift_handler _) t) (bind (call_term x yR vvin) k) ->
  exists xR k', multi_step n t (bind (call_term x xR vvin) k') /\ 
             weaken_var_l _ _ _ xR = yR /\
             (forall x, k x ≅ mapE (lift_handler _) (k' x)).
Proof.
  intros. eapply multi_step_mapE_call_term_inv' in H;
    try eapply lift_handler_rel; try apply valid_lift_handler; eauto.
  intros. eapply weaken_var_l_inj; eauto.
Qed.
