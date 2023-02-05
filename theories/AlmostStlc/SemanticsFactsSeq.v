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

Notation call_syn := SmallStepSeq.call.
(* bottoms out in exposed contexts *)
Inductive covered_in {t2 MR2} (ca : call_syn t2 MR2) 
  : forall t1 MR1 (b : bool) 
          (E : eval_context t1 MR1 (inr ca) b),  Prop :=
  (* need three base cases, one for each handler style context *)
  | covered_in_mfix_base t MR1 R
                    (bodies : mfix_bodies nil MR1 R R)
                    (E : eval_context t (R :: MR1) (inr ca) true) : 
    covered_in ca t _ _ (ev_mfix true R bodies E)

  | covered_in_perm_base t MR1 MR2 (Hperm : perm MR1 MR2)
                    (E : eval_context t MR1 (inr ca) true) :
    covered_in ca t MR2 _ (ev_perm true Hperm E)
  | covered_in_lift_base t MR1 MR2
                    (E : eval_context t MR2 (inr ca) true) : 
    covered_in ca t (MR1 ++ MR2) _ (ev_lift true E)
  | covered_in_let b t1 t2 MR1 (E : eval_context t1 MR1 (inr ca) b)
                   (c : comp t2 (t1 :: nil) MR1) : 
    covered_in ca t1 MR1 b E ->
    covered_in ca t2 MR1 b (ev_let E c)
  | covered_in_mfix t MR1 R
                    (bodies : mfix_bodies nil MR1 R R)
                    (E : eval_context t (R :: MR1) (inr ca) false) : 
    covered_in ca t (R :: MR1) false E ->
    covered_in ca t _ false (ev_mfix false R bodies E)

  | covered_in_perm t MR1 MR2 (Hperm : perm MR1 MR2)
                    (E : eval_context t MR1 (inr ca) false) :
    covered_in ca t MR1 false E ->
    covered_in ca t MR2 false (ev_perm false Hperm E)
  | covered_in_lift t MR1 MR2
                    (E : eval_context t MR2 (inr ca) false) : 
    covered_in ca t MR2 false E ->
    covered_in ca t (MR1 ++ MR2) false (ev_lift false E)
  .
Arguments covered_in {_ _} (_) {_ _ _}.

(* need to be a bit more general, allow for an MR1 but force b = false *)
Lemma covered_in_intro t1 t2 MR1 MR2 (ca : call_syn t2 MR2) (E : eval_context t1 MR1 (inr ca) false) : 
  covered_in ca E.
Proof.
  dependent induction E; try (destruct b; constructor; auto).
  constructor. apply IHE; auto.
Qed.

Lemma covered_in_step t1 t2 MR1 MR2 b (ca : call_syn t2 MR2) (E : eval_context t1 MR1 (inr ca) b) :
  covered_in ca E -> exists c, step_eval_context b (inr ca) E = Some c.
Proof.
  intros H. dependent induction H; simp step_eval_context.
  - destruct (normalize_eval_context ca E). destruct x. eexists. eauto.
  - destruct (normalize_eval_context ca E). destruct x. eexists. eauto.
  - destruct (normalize_eval_context ca E). destruct x. eexists. eauto.
  - destruct IHcovered_in. simp step_eval_context.
    rewrite H0. eexists. cbn. reflexivity.
  - destruct IHcovered_in.
    rewrite H0. eexists. reflexivity.
  - destruct IHcovered_in.
    rewrite H0. eexists. reflexivity.
  - destruct IHcovered_in.
    rewrite H0. eexists. reflexivity.
Qed.
(* if MR is empty then ca must be covered_in E 
   if ca is covered 
*)

Lemma progress_boxed_eval_context (t1 t2 : vtype) b (MR : mfix_ctx) (r : bredex t2 MR + call_syn t2 MR) (E : eval_context t1 nil r b) : 
  exists c, step_eval_context b r E = Some c.
Proof.
  destruct r.
  - simp step_eval_context. eexists. eauto.
  - apply covered_in_step. 
    enough (b = false). subst; apply covered_in_intro.
    dependent induction E; auto.
    destruct c. inversion xR.
    eauto.
Qed.

Theorem progress_step (t : vtype) (c : comp t nil nil) :
  (exists c', step c = inl (Some c')) \/ (exists v, step c = inr v).
Proof.
  unfold step. destruct (SmallStepSeq.observe c); eauto.
  destruct b. left.
  specialize progress_boxed_eval_context with (E := E) as [c' Hc'].
  rewrite Hc'. eexists. reflexivity.
Qed.

Equations var_map_weaken {Γ2} Γ1 (f : forall t, var t Γ1 -> var t Γ2) (hyps : denote_ctx Γ2) : denote_ctx Γ1 :=
  var_map_weaken [] f hyps := tt;
  var_map_weaken (t1 :: Γ1) f hyps :=
    (index_ctx (f t1 VarZ) hyps, var_map_weaken Γ1 (fun t x => f t (VarS x))  hyps).
Arguments var_map_weaken {_ _}.

Lemma index_weaken:
  forall (t : vtype) (Γ : ctx) (x : var t Γ) (Γ2 : ctx) (f : forall t' : vtype, var t' Γ -> var t' Γ2) (hyps : denote_ctx Γ2),
    index_ctx (f t x) hyps = index_ctx x (var_map_weaken f hyps).
Proof.
  intros t Γ x Γ2 f hyps.
  revert f hyps. induction Γ. inversion x. intros.
  dependent destruction x.
  - simp var_map_weaken. simp index_ctx. auto.
  - simp var_map_weaken. simp index_ctx. setoid_rewrite <- IHΓ.
    auto.
Qed.

Lemma var_map_weaken_skip:
  forall (t1 : vtype) (Γ Γ2 : ctx) (f : forall t' : vtype, var t' Γ -> var t' Γ2) (hyps : denote_ctx Γ2) (v : denote_type t1),
    var_map_weaken (var_map_skip f) (v, hyps) = (v, var_map_weaken f hyps).
Proof.
  intros t1 Γ Γ2 f hyps.
  intros. simp var_map_weaken. simp index_ctx.
  (* try to finish this, then write down desirata for type equiv*)
  enough (var_map_weaken (fun (t : vtype) (x : var t Γ) => var_map_skip f t (VarS x)) (v, hyps) = var_map_weaken f hyps). subst. rewrite H. auto.
  simp var_map_weaken.
  generalize dependent v.  generalize dependent f.
  generalize dependent hyps.
  induction Γ.
  - intros. cbn in hyps. simp var_map_weaken. auto.
  - intros. specialize (IHΓ hyps (fun (t : vtype) (x : var t Γ) => f t (VarS x)) v). 
    simp var_map_skip in IHΓ.
    simp var_map_weaken. simp var_map_skip.
    rewrite <- IHΓ. simp index_ctx. auto.
Qed.

Lemma ctx_equiv_var_map_weaken:
  forall (Γ1 Γ2 : ctx) (f : forall t' : vtype, var t' Γ1 -> var t' Γ2) (hyps1 hyps2 : denote_ctx Γ2),
    ctx_equiv Γ2 hyps1 hyps2 -> ctx_equiv Γ1 (var_map_weaken f hyps1) (var_map_weaken f hyps2).
Proof.
  intros Γ1 Γ2 f hyps1 hyps2. generalize dependent Γ2.
  induction Γ1.
  - intros. red. auto.
  - intros Γ2 f hyps1 hyps2 Hhyps. simp var_map_weaken. split; simpl; auto.
    apply types_equiv_index_ctx. auto.
Qed.

(* comp_value_mutind *)
Lemma comp_val_bodies_map : 
  (forall t Γ1 MR (c : comp t Γ1 MR), forall Γ2 (f : forall t', var t' Γ1 -> var t' Γ2) 
  (hyps1 hyps2 : denote_ctx Γ2) (Hhyps : ctx_equiv Γ2 hyps1 hyps2),
  rutt (mfix_pre_equiv MR) (mfix_post_equiv MR) (types_equiv t) 
       (denote_comp (comp_map c f) hyps1) (denote_comp c (var_map_weaken f hyps2)) ) /\
  (forall t Γ1 (v : value t Γ1) MR Γ2  (f : forall t', var t' Γ1 -> var t' Γ2) 
  (hyps1 hyps2 : denote_ctx Γ2) (Hhyps : ctx_equiv Γ2 hyps1 hyps2),
      rutt (mfix_pre_equiv MR) (mfix_post_equiv MR) (types_equiv t) 
           (denote_value (MR := MR) (val_map v f) hyps1) (denote_value v (var_map_weaken f hyps2))) /\
  (forall Γ1 MR R R' (bodies : mfix_bodies Γ1 MR R R') Γ2 (f : forall t', var t' Γ1 -> var t' Γ2) 
      (arg1 arg2 : denote_call_frame R') (Harg : call_frame_pre_equiv R' arg1 arg2)
      (hyps1 hyps2 : denote_ctx Γ2) (Hhyps : ctx_equiv Γ2 hyps1 hyps2),
      rutt (mfix_pre_equiv (R :: MR)) (mfix_post_equiv (R :: MR)) (call_frame_post_equiv R' arg1 arg2) 
           (denote_bodies (bodies_map bodies f) hyps1 arg1) (denote_bodies bodies (var_map_weaken f hyps2) arg2)).
Proof.
  apply comp_value_mutind; intros; auto.
  - rewrite val_map_equation_1. repeat rewrite denote_value_equation_1. 
    apply rutt_Ret. reflexivity.
  - rewrite val_map_equation_2. repeat rewrite denote_value_equation_2. 
    apply rutt_Ret. constructor.
  - rewrite val_map_equation_3. repeat rewrite denote_value_equation_3. 
    eapply rutt_bind; eauto. intros. eapply rutt_bind; eauto. intros.
    apply rutt_Ret. constructor; auto.
  - rewrite val_map_equation_4. repeat rewrite denote_value_equation_4.
    repeat (eapply rutt_bind; eauto; intros).
    apply rutt_Ret. constructor; auto.
  - rewrite val_map_equation_5. repeat rewrite denote_value_equation_5.
    apply rutt_Ret. simp types_equiv.
    intros g h Hgh. rewrite <- var_map_weaken_skip. 
    apply H. constructor; auto.
  - rewrite val_map_equation_6. repeat rewrite denote_value_equation_6.
    apply rutt_Ret. rewrite <- index_weaken.
    apply types_equiv_index_ctx. auto.
  - simp comp_map. simp denote_comp.
  - simp comp_map. simp denote_comp. 
    eapply rutt_bind; eauto. intros. rewrite <- var_map_weaken_skip.
    eapply H0. constructor; auto.
  - simp comp_map. simp denote_comp.
    eapply rutt_bind; eauto. intros. simp types_equiv in H2. subst r2.
    destruct r1; auto. rewrite <- var_map_weaken_skip with (t1 := Nat).
    eapply H1. constructor; auto. reflexivity.
  - simp comp_map. simp denote_comp.
    eapply rutt_bind; eauto. intros. simp types_equiv in H2.
    dependent destruction H2; eauto.
    rewrite <- var_map_weaken_skip with (t1 := List t1).
    setoid_rewrite <- var_map_weaken_skip with (t1 := t1) (Γ2 := List t1 :: Γ2)
                                       (v := b) 
                                       (f := var_map_skip f)
                                       (hyps := (l2, hyps2)).
    apply H1. repeat split; auto.
  - simp comp_map. simp denote_comp. 
    eapply rutt_bind; eauto. intros. simp types_equiv in H1.
    dependent destruction H1. destruct r1. destruct r2.
    rewrite <- var_map_weaken_skip with (t1 := t2).
    setoid_rewrite <- var_map_weaken_skip with (t1 := t1) (Γ2 := t2 :: Γ2)
                                              (v := d1)
                                              (f := var_map_skip f)
                                              (hyps := (d2, hyps2)).
    apply H0. repeat split; auto.
  - simp comp_map. simp denote_comp. 
    do 2 (eapply rutt_bind; eauto; intros).
  - simp comp_map. simp denote_comp.
    eapply rutt_bind; eauto. intros. unfold call_term.
    (* maybe can write a better reasoning principle that encloses this *)
    destruct (call_mrec x xR r1) as [c1 f1] eqn : Heq1.
    destruct (call_mrec x xR r2) as [c2 f2] eqn : Heq2. 
    setoid_rewrite bind_trigger. apply rutt_Vis.
    eapply mfix_pre_call_mrec; eauto.
    intros. apply rutt_Ret. eapply mfix_post_equiv_types_equiv; eauto.
  - simp comp_map. simp denote_comp. 
    eapply interp_mrec_rutt; eauto.
  - simp comp_map. simp denote_comp. 
    apply mapE_rutt. eapply rutt_mon; try eapply H; 
      intros; try eapply mfix_pre_equiv_lift_handler; try eapply mfix_post_equiv_lift_handler; eauto.
  - simp comp_map. simp denote_comp.
    apply mapE_rutt. eapply rutt_mon; try eapply H;
      intros; try eapply mfix_pre_equiv_perm_handler; try eapply mfix_post_equiv_perm_handler;
      eauto.
  - contradiction.
  - rewrite bodies_map_equation_2.
    rewrite call_frame_pre_equiv_equation_2 in Harg.
    dependent destruction Harg; simp denote_bodies.
    + setoid_rewrite denote_bodies_equation_2.
      rewrite <- var_map_weaken_skip. 
      eapply rutt_mon; try eapply H; eauto.
      intros. constructor; auto. split; auto.
    + setoid_rewrite denote_bodies_equation_3.
      eapply rutt_mon; try eapply H0; eauto.
      intros; constructor; auto.
Qed.

Lemma comp_map_correct t Γ1 Γ2 MR (c : comp t Γ1 MR) (f : forall t', var t' Γ1 -> var t' Γ2) 
  hyps1 hyps2 : ctx_equiv Γ2 hyps1 hyps2 ->
                  rutt (mfix_pre_equiv MR) (mfix_post_equiv MR) (types_equiv t) 
                       (denote_comp (comp_map c f) hyps1) (denote_comp c (var_map_weaken f hyps2)).
Proof.
  intros. destruct comp_val_bodies_map. auto.
Qed.

Lemma val_map_correct t Γ1 Γ2 MR (v : value t Γ1) (f : forall t', var t' Γ1 -> var t' Γ2) 
  (hyps1 hyps2 : denote_ctx Γ2) (Hhyps : ctx_equiv Γ2 hyps1 hyps2) :
      rutt (mfix_pre_equiv MR) (mfix_post_equiv MR) (types_equiv t) 
           (denote_value (MR := MR) (val_map v f) hyps1) (denote_value v (var_map_weaken f hyps2)).
Proof.
  intros. destruct comp_val_bodies_map as [ ? [? ?] ]; auto.
Qed.

Lemma bodies_map_correct Γ1 Γ2 MR R R' (bodies : mfix_bodies Γ1 MR R R') (f : forall t', var t' Γ1 -> var t' Γ2) 
      (arg1 arg2 : denote_call_frame R') (Harg : call_frame_pre_equiv R' arg1 arg2)
      (hyps1 hyps2 : denote_ctx Γ2) (Hhyps : ctx_equiv Γ2 hyps1 hyps2) :
      rutt (mfix_pre_equiv (R :: MR)) (mfix_post_equiv (R :: MR)) (call_frame_post_equiv R' arg1 arg2) 
           (denote_bodies (bodies_map bodies f) hyps1 arg1) (denote_bodies bodies (var_map_weaken f hyps2) arg2).
Proof.
  intros. destruct comp_val_bodies_map as [ ? [? ?] ]; auto.
Qed.

Equations insert_ctx {t Γ2} Γ1 (v : denote_type t) (hyps : denote_ctx (Γ1 ++ Γ2) ) : 
  denote_ctx (Γ1 ++ [t] ++ Γ2) :=
  insert_ctx [] v hyps := (v,hyps);
  insert_ctx (t1 :: Γ1) v (v1, hyps) := (v1, insert_ctx Γ1 v hyps).
Arguments insert_ctx {_ _ _}.
Equations apply_middle {t Γ2 T} Γ1 (f : denote_ctx (Γ1 ++ [t] ++ Γ2 ) -> T) (v : denote_type t) 
  (hyps : denote_ctx (Γ1 ++ Γ2) ) : T :=
  apply_middle [] f v hyps := f (v,hyps);
  apply_middle (t1 :: Γ1) f v (x,hyps) :=
    apply_middle Γ1 (fun hyps' => f (x,hyps') ) v hyps.
Arguments apply_middle {_ _ _ _}.

Equations hyps_app {Γ2} Γ1 (hyps1 : denote_ctx Γ1) (hyps2 : denote_ctx Γ2) : denote_ctx (Γ1 ++ Γ2) :=
  hyps_app [] _ hyps2 := hyps2;
  hyps_app _ (v, hyps1) hyps2 := (v, hyps_app _ hyps1 hyps2).
Arguments hyps_app {_ _}.
Notation "h1 +++ h2" := (hyps_app h1 h2) (at level 30).
(* subst_var *)

Definition denote_ctx_single {t} (v : denote_type t) : denote_ctx [t] := (v, tt).

Theorem denote_value_terminates t Γ (v : value t Γ) (hyps : denote_ctx Γ) : 
  exists vv : denote_type t, (forall MR, denote_value (MR := MR) v hyps ≈ ret vv).
Proof.
  induction v.
  - eexists; setoid_rewrite denote_value_equation_1; eauto. reflexivity.
  - eexists; setoid_rewrite denote_value_equation_2; eauto. reflexivity.
  - setoid_rewrite denote_value_equation_3; eauto.
    specialize (IHv1 hyps) as [vv1 Hvv1].
    specialize (IHv2 hyps) as [vv2 Hvv2].
    eexists. intros.
    rewrite Hvv1. setoid_rewrite bind_ret_l.
    rewrite Hvv2. setoid_rewrite bind_ret_l. reflexivity.
  - setoid_rewrite denote_value_equation_4; eauto.
    specialize (IHv1 hyps) as [vv1 Hvv1].
    specialize (IHv2 hyps) as [vv2 Hvv2].
    eexists. intros.
    rewrite Hvv1. setoid_rewrite bind_ret_l.
    rewrite Hvv2. setoid_rewrite bind_ret_l. reflexivity.
  - eexists. setoid_rewrite denote_value_equation_5. reflexivity.
  - eexists. setoid_rewrite denote_value_equation_6. reflexivity.
Qed.

Lemma denote_value_ret_equiv:
  forall (t : vtype) (MR : mfix_ctx) (Γ : ctx) (v : value t Γ) (hyps1 hyps2 : denote_ctx Γ)
    (vv1 vv2 : denote_type t),
    ctx_equiv Γ hyps1 hyps2 ->
    denote_value (MR := MR) v hyps1 ≈ ret vv1 ->
    denote_value (MR := MR) v hyps2 ≈ ret vv2 ->
    types_equiv t vv1 vv2.
Proof.
  intros t MR Γ2 v.
  specialize (types_equiv_value_refl _ _ MR v) as Hv.
  intros hyps1 hyps2 vv1 vv2 Hhyps. specialize (Hv _ _ Hhyps).
  red in Hv. intros Hvv1 Hvv2. rewrite Hvv1, Hvv2 in Hv.
  apply rutt_inv_Ret in Hv. auto.
Qed.

Lemma ctx_equiv_hyps_app Γ1 Γ2 : 
  forall (hyps11 hyps12 : denote_ctx Γ1) 
    (hyps21 hyps22 : denote_ctx Γ2),
    ctx_equiv Γ1 hyps11 hyps12 ->
    ctx_equiv Γ2 hyps21 hyps22 ->
    ctx_equiv (Γ1 ++ Γ2) (hyps11 +++ hyps21) (hyps12 +++ hyps22).
Proof.
  revert Γ2. induction Γ1.
  - intros. destruct hyps11. destruct hyps12. simp hyps_app.
  - intros Γ2 [v1 hyps11] [v2 hyps12] hyps21 hyps22 H1 H2.
    simp hyps_app. simpl ctx_equiv in H1. destruct H1.
    constructor; eauto.
Qed.

Lemma index_ctx_equiv Γ (hyps1 hyps2 : denote_ctx Γ) :
  (forall t (x : var t Γ), index_ctx x hyps1 = index_ctx x hyps2) -> hyps1 = hyps2.
Proof.
  revert hyps1 hyps2. induction Γ; intros.
  - destruct hyps1. destruct hyps2. auto.
  - destruct hyps1 as [v1 hyps1]. destruct hyps2 as [v2 hyps2].
    enough (v1 = v2 /\ hyps1 = hyps2).
    destruct H0. subst. auto.
    split.
    + specialize (H a VarZ). simp index_ctx in H.
    + apply IHΓ.
      intros. specialize (H t (VarS x)). simp index_ctx in H.
Qed.

Equations weaken_denote_ctx Γ1 Γ2 (hyps : denote_ctx (Γ1 ++ Γ2)) : denote_ctx Γ2 :=
  weaken_denote_ctx nil _ hyps := hyps;
  weaken_denote_ctx (t :: Γ1) Γ2 (_, hyps) := weaken_denote_ctx Γ1 Γ2 hyps.

Arguments var_map_weaken {_} (_).
Lemma var_map_weaken_hyps (Γ1 Γ2 : ctx) (hyps : denote_ctx (Γ1 ++ Γ2)) :
  var_map_weaken Γ2 (weaken_var_l Γ1 Γ2) hyps = weaken_denote_ctx Γ1 Γ2 hyps.
Proof.
  generalize dependent Γ2.
  induction Γ1; simpl.
  - intros. simp weaken_denote_ctx.
    induction Γ2; simp var_map_weaken. destruct hyps. auto.
    destruct hyps as [v hyps]. simp weaken_var_l.
    simp index_ctx. 
    erewrite index_ctx_equiv. eauto.
    intros t x. dependent destruction x.
    simp index_ctx. auto. simp index_ctx.
    rewrite <- index_weaken. simp weaken_var_l.
    simp index_ctx. auto.
  - intros Γ2 [v hyps]. simp weaken_denote_ctx.
    rewrite <- IHΓ1. clear IHΓ1.
    apply index_ctx_equiv. intros t x. 
    setoid_rewrite <- index_weaken. simp weaken_var_l.
    simp index_ctx. auto.
Qed.

Lemma var_map_weaken_single_hyps:
  forall (t : vtype) (Γ : ctx) (hyps : denote_ctx (t :: Γ)),
    var_map_weaken _ (weaken_var_l [t] _) hyps = snd hyps.
Proof.
  setoid_rewrite var_map_weaken_hyps.
  intros. destruct hyps as [v hyps]. 
  simp weaken_denote_ctx. auto.
Qed.

(* not sure how to correctly write the inductive hyp because it is 
   dependent, might be easier if subst was  *)

Lemma subst_var_correct t u Γ1 Γ2 MR (v : value t Γ2) (x : var u (Γ1 ++ [t] ++ Γ2 ) ) : 
  forall (hyps11 hyps12 : denote_ctx Γ1) (hyps21 hyps22 : denote_ctx Γ2) 
    (Hhyps1 : ctx_equiv _ hyps11 hyps12) (Hhyps2 : ctx_equiv _ hyps21 hyps22) vv,
    denote_value (MR := MR) v hyps21 ≈ ret vv ->
    rutt (mfix_pre_equiv MR) (mfix_post_equiv MR) (types_equiv u)
         (denote_value (val_var x) (hyps11 +++ ((denote_ctx_single vv) +++ hyps21) ) )
         (denote_value (subst_var Γ1 Γ2 v x) (hyps12 +++ hyps22) ).
Proof.
  revert x v. generalize dependent Γ2. 
  induction Γ1.
  - simpl app. intros Γ2 x v [] [] hyps21 hyps22 _ Hhyps2 vv Hvv. simp hyps_app.
    dependent destruction x.
    + simp subst_var. setoid_rewrite denote_value_equation_6. 
      setoid_rewrite hyps_app_equation_2.
      setoid_rewrite index_ctx_equation_1.
      destruct (denote_value_terminates _ _ v hyps22) as [vv' Hvv'].
      rewrite Hvv'. apply rutt_Ret. eapply denote_value_ret_equiv; eauto.
    + setoid_rewrite hyps_app_equation_2. setoid_rewrite denote_value_equation_6.
      simp hyps_app. 
      setoid_rewrite index_ctx_equation_2. destruct Γ2.
      * inversion x.
      * simp subst_var. setoid_rewrite denote_value_equation_6.
        apply rutt_Ret. apply types_equiv_index_ctx. auto.
  - simpl app. intros Γ2 x v hyps11 hyps12 hyps21 hyps22 Hhyps1 Hhyps2 vv Hvv.
    dependent destruction x.
    + simp subst_var. setoid_rewrite denote_value_equation_6. clear IHΓ1.
      apply rutt_Ret. destruct hyps11. destruct hyps12. red in Hhyps1. dependent destruction Hhyps1.
      simp hyps_app.
    + simp subst_var. red in Hhyps1. dependent destruction Hhyps1.
      eapply IHΓ1 with (x := x) in Hvv; eauto. 
      setoid_rewrite denote_value_equation_6. 
      setoid_rewrite denote_value_equation_6 in Hvv. 
      destruct hyps11 as [t0 hyps11]. simp hyps_app. simp index_ctx.
      simpl snd in Hvv. rewrite Hvv.
      clear Hvv. unfold weaken_l_value_single,weaken_l_value.
      assert (Hhyps' : ctx_equiv ((a :: Γ1) ++ Γ2) (hyps12 +++ hyps22) (hyps12 +++ hyps22)).
      {
        apply ctx_equiv_hyps_app; auto. 
        transitivity ((t0,hyps11)); eauto. constructor; auto.
        symmetry. auto. symmetry. auto.
        constructor; auto.
        transitivity hyps21; auto. symmetry. auto.
      }
      rewrite val_map_correct with (hyps2 := hyps12 +++ hyps22); auto.
      enough (var_map_weaken _ (weaken_var_l [a] (Γ1 ++ Γ2)) (hyps12 +++ hyps22) =
                snd hyps12 +++ hyps22).
      setoid_rewrite H.
      apply types_equiv_value_refl; auto. 
      destruct hyps12 as [v1 hyps12].
      simpl. apply ctx_equiv_hyps_app; auto.
      etransitivity; eauto. symmetry. auto.
      etransitivity; eauto. symmetry. auto.
      rewrite var_map_weaken_single_hyps.
      destruct hyps12. simp hyps_app.
      auto.
Qed.

(* further generalize hyps stuff *)
Lemma subst_correct_aux_prod :
  (forall u Γ MR (c : comp u Γ MR) Γ1 t Γ2 (v : value t Γ2) 
     (hyps11 hyps12 : denote_ctx Γ1) (hyps21 hyps22 : denote_ctx Γ2) vv (c' : comp u (Γ1 ++ [t] ++ Γ2) MR) ,
      ctx_equiv Γ1 hyps11 hyps12 ->
      ctx_equiv Γ2 hyps21 hyps22 ->
      Γ = Γ1 ++ [t] ++ Γ2 ->
      c ~= c' ->
      (forall MR, denote_value (MR := MR) v hyps21 ≈ ret vv) ->
      comp_equiv_rutt (denote_comp (subst_comp c' v) (hyps11 +++ hyps21))
                      (denote_comp c' (hyps12 +++ ((denote_ctx_single vv) +++ hyps22)) )) /\
  (forall u Γ (v0 : value u Γ) MR Γ1 t Γ2 (v : value t Γ2)
     (hyps11 hyps12 : denote_ctx Γ1) (hyps21 hyps22 : denote_ctx Γ2) vv 
     (v0' : value u (Γ1 ++ [t] ++ Γ2)),
      ctx_equiv Γ1 hyps11 hyps12 ->
      ctx_equiv Γ2 hyps21 hyps22 ->
      Γ = Γ1 ++ [t] ++ Γ2 ->
      v0 ~= v0' ->
      (forall MR, denote_value (MR := MR) v hyps21 ≈ ret vv) ->
      comp_equiv_rutt (MR := MR) (denote_value (subst_value v0' v) (hyps11 +++ hyps21) )
                      (denote_value v0' (hyps12 +++ ((denote_ctx_single vv) +++ hyps22))) ) /\
  (forall Γ MR R R' (bodies : mfix_bodies Γ MR R R') Γ1 t Γ2 (v : value t Γ2)
     (hyps11 hyps12 : denote_ctx Γ1) (hyps21 hyps22 : denote_ctx Γ2) vv 
     (bodies' : mfix_bodies (Γ1 ++ [t] ++ Γ2) MR R R')
     (arg1 arg2 : denote_call_frame R') (Harg : call_frame_pre_equiv R' arg1 arg2),
      ctx_equiv Γ1 hyps11 hyps12 ->
      ctx_equiv Γ2 hyps21 hyps22 ->
      Γ = Γ1 ++ [t] ++ Γ2 ->
      bodies ~= bodies' ->
      (forall MR, denote_value (MR := MR) v hyps21 ≈ ret vv) ->
      rutt (mfix_pre_equiv (R :: MR)) (mfix_post_equiv (R :: MR)) 
           (call_frame_post_equiv R' arg1 arg2)  
           (denote_bodies (subst_bodies bodies' v) (hyps11 +++ hyps21) arg1 )
           (denote_bodies bodies' (hyps12 +++ ((denote_ctx_single vv) +++ hyps22)) arg2 )
)
.
Proof.
  eapply comp_value_mutind; intros; subst.
  - setoid_rewrite subst_value_equation_1.
    setoid_rewrite denote_value_equation_1. apply rutt_Ret.
    reflexivity.
  - setoid_rewrite subst_value_equation_2.
    setoid_rewrite denote_value_equation_2. apply rutt_Ret.
    constructor.
  - setoid_rewrite subst_value_equation_3.
    setoid_rewrite denote_value_equation_3. red.
    eapply rutt_bind; eauto. eapply H; eauto.
    intros. eapply rutt_bind; eauto. eapply H0; eauto.
    intros. apply rutt_Ret.
    constructor; auto.
  - setoid_rewrite subst_value_equation_4.
    setoid_rewrite denote_value_equation_4.
    eapply rutt_bind. eapply H; eauto.
    intros. eapply rutt_bind. eapply H0; eauto.
    intros. apply rutt_Ret. constructor; auto.
  - setoid_rewrite subst_value_equation_5.
    setoid_rewrite denote_value_equation_5.
    apply rutt_Ret. simp types_equiv.
    intros x y Hxy.
    specialize (H (t1 :: Γ1) t Γ2 v (x, hyps11) (y, hyps12) hyps21 hyps22 vv). 
    assert (ctx_equiv (t1 :: Γ1) (x, hyps11) (y, hyps12)).
    constructor; auto.
    specialize (H cbody H2 H1 eq_refl JMeq_refl H4).
    simp hyps_app in H. rewrite H.
    apply types_equiv_comp_refl. cbn.
    constructor. etransitivity; eauto. symmetry. auto.
    simpl. apply ctx_equiv_hyps_app.
    etransitivity; eauto. symmetry. auto.
    unfold denote_ctx_single. simp hyps_app.
    cbn. constructor; auto.
    2 : etransitivity; eauto; symmetry; auto.
    simpl. 
    eapply denote_value_ret_equiv with 
      (v := v) (hyps1 := hyps21) (hyps2 := hyps21); eauto.
    etransitivity; eauto; symmetry; auto.
  - setoid_rewrite subst_value_equation_6.
    specialize (H3 MR).
    eapply subst_var_correct with (x := x)in H3 as H4; eauto.
    assert (Hsubst : comp_equiv_rutt (MR := MR)
              (denote_value (subst_var Γ1 Γ2 v x) (hyps11 +++ hyps21))
              (denote_value (subst_var Γ1 Γ2 v x) (hyps12 +++ hyps22))).
    { apply types_equiv_value_refl. apply ctx_equiv_hyps_app; auto. }
    rewrite Hsubst. rewrite <- H4.
    apply types_equiv_value_refl.
    apply ctx_equiv_hyps_app; auto.
    apply ctx_equiv_hyps_app; auto. constructor; auto.
    2 : constructor. simpl.
    eapply denote_value_ret_equiv with (hyps1 := hyps21) (hyps2 := hyps21); eauto.
    etransitivity; eauto. symmetry; auto.
  - setoid_rewrite subst_comp_equation_1. 
    setoid_rewrite denote_comp_equation_1. eauto.
  - setoid_rewrite subst_comp_equation_2.
    setoid_rewrite denote_comp_equation_2.
    eapply rutt_bind; eauto. eapply H; eauto.
    intros. setoid_rewrite <- hyps_app_equation_2.
    specialize (H0 (t1 :: Γ1)). eapply H0; eauto.
    constructor; auto.
  - setoid_rewrite subst_comp_equation_3. 
    setoid_rewrite denote_comp_equation_3.
    eapply rutt_bind. eapply H; eauto.
    intros. simp types_equiv in H4. subst r2. destruct r1.
    eapply H0; eauto.
    specialize (H1 (Nat :: Γ1) t0 Γ2 v (r1, hyps11) (r1, hyps12) ). 
    setoid_rewrite hyps_app_equation_2 in H1. eapply H1; eauto.
    constructor; auto. reflexivity.
 - setoid_rewrite subst_comp_equation_4.
   setoid_rewrite denote_comp_equation_4.
   eapply rutt_bind. eapply H; eauto. intros.
   simp types_equiv in H4. dependent destruction H4.
   eapply H0; eauto. clear H. clear H0.
   specialize (H1 (t1 :: List t1 :: Γ1) t Γ2 v (a, (l1, hyps11)) (b, (l2, hyps12))).
   repeat setoid_rewrite hyps_app_equation_2 in H1.
   setoid_rewrite hyps_app_equation_1 in H1. setoid_rewrite hyps_app_equation_2.
   setoid_rewrite hyps_app_equation_1.
   eapply H1; eauto. repeat constructor; auto.
 - setoid_rewrite subst_comp_equation_5.
   setoid_rewrite denote_comp_equation_5.
   eapply rutt_bind. eapply H; eauto. intros.
   destruct r1 as [v1 v2]. destruct r2 as [v3 v4].
   simp types_equiv in H3. dependent destruction H3.
   cbn in fst_rel. cbn in snd_rel.
   clear H.
   specialize (H0 (t1 :: t2 :: Γ1) t Γ2 v (v1, (v2, hyps11)) (v3, (v4, hyps12)) ).
   repeat setoid_rewrite hyps_app_equation_2 in H0. 
   setoid_rewrite hyps_app_equation_1 in H0.
   setoid_rewrite hyps_app_equation_2. setoid_rewrite hyps_app_equation_1. 
   eapply H0; auto. repeat constructor; auto.
 - setoid_rewrite subst_comp_equation_6.
   setoid_rewrite denote_comp_equation_6.
   eapply rutt_bind; eauto. eapply H; eauto.
   intros. eapply rutt_bind. eapply H0; eauto. intros. 
   simp types_equiv in H3.
 - setoid_rewrite subst_comp_equation_7.
   setoid_rewrite denote_comp_equation_7.
   eapply rutt_bind. eapply H; eauto.
   intros. unfold call_term.
   destruct (call_mrec x xR r1) as [c1 f1] eqn : Heq1.
   destruct (call_mrec x xR r2) as [c2 f2] eqn : Heq2. 
   setoid_rewrite bind_trigger. apply rutt_Vis.
   eapply mfix_pre_call_mrec; eauto.
   intros. apply rutt_Ret. eapply mfix_post_equiv_types_equiv; eauto.
 - setoid_rewrite subst_comp_equation_8.
   setoid_rewrite denote_comp_equation_8.
   eapply interp_mrec_rutt
     with (RPreInv := call_frame_pre_equiv R)
          (RPostInv := call_frame_post_equiv R);
     intros; try eapply H0; eauto.
 - setoid_rewrite subst_comp_equation_9.
   setoid_rewrite denote_comp_equation_9.
   apply mapE_rutt.
   eapply rutt_mon; try eapply H; eauto.
   intros; eapply mfix_pre_equiv_lift_handler; eauto.
   intros; eapply mfix_post_equiv_lift_handler; eauto.
 - setoid_rewrite subst_comp_equation_10.
   setoid_rewrite denote_comp_equation_10.
   apply mapE_rutt.
   eapply rutt_mon; try eapply H; eauto.
   intros; eapply mfix_pre_equiv_perm_handler; eauto.
   intros; eapply mfix_post_equiv_perm_handler; eauto.
 - inversion arg1.
 - rewrite call_frame_pre_equiv_equation_2 in Harg.
   rewrite subst_bodies_equation_2.
   dependent destruction Harg.
   + setoid_rewrite denote_bodies_equation_2.
     setoid_rewrite <- hyps_app_equation_2.
     specialize (H (t1 :: Γ1) t Γ2 v (a1, hyps11) (a2, hyps12)).
     specialize (H hyps21 hyps22 vv body).
     assert (Hahyps : ctx_equiv (t1 :: Γ1) (a1, hyps11) (a2, hyps12)).
     constructor; auto.
     specialize (H Hahyps H3 eq_refl JMeq_refl H5).
     eapply rutt_mon; try eapply H; eauto.
     intros. constructor; auto.
   + setoid_rewrite denote_bodies_equation_3.
     eapply rutt_mon; try eapply H0; eauto.
     intros. constructor; auto.
     Unshelve. eauto.
Qed.

Theorem subst_comp_correct t u Γ1 Γ2 MR (c : comp u (Γ1 ++ [t] ++ Γ2) MR) (v : value t Γ2)
        (hyps11 hyps12 : denote_ctx Γ1) (hyps21 hyps22 : denote_ctx Γ2) vv :
  ctx_equiv Γ1 hyps11 hyps12 ->
  ctx_equiv Γ2 hyps21 hyps22 ->
  (forall MR, denote_value (MR := MR) v hyps21 ≈ ret vv) ->
  comp_equiv_rutt (denote_comp (subst_comp c v) (hyps11 +++ hyps21))
                  (denote_comp c (hyps12 +++ ((denote_ctx_single vv) +++ hyps22)) ).
Proof.
  destruct subst_correct_aux_prod as [H _].
  intros. eapply H; eauto.
Qed.

Theorem subst_correct0 t u Γ MR (c : comp u (t :: Γ) MR) (v : value t Γ) : 
  forall (hyps1 hyps2 : denote_ctx Γ) vv,
    ctx_equiv Γ hyps1 hyps2->
    (forall MR, denote_value (MR := MR) v hyps1 ≈ ret vv) ->
    comp_equiv_rutt 
      (denote_comp (subst_comp_cons c v) hyps1)
                (denote_comp c (vv, hyps2)).
Proof.
  intros. 
  specialize subst_comp_correct with 
    (Γ1 := []) (Γ2 := Γ) 
    (hyps11 := tt) (hyps12 := tt)
    as Hsubst. 
  setoid_rewrite hyps_app_equation_1 in Hsubst.
  setoid_rewrite hyps_app_equation_2 in Hsubst.
  setoid_rewrite hyps_app_equation_1 in Hsubst. 
  eapply Hsubst; eauto. constructor.
Qed.

Theorem subst_correct1 t u Γ MR (c : comp u (t :: Γ) MR) (v : value t Γ) : 
  forall (hyps1 hyps2 : denote_ctx Γ) vv,
    ctx_equiv Γ hyps1 hyps2->
    comp_equiv_rutt (denote_value (MR := MR) v hyps1) (ret vv) ->
    comp_equiv_rutt 
      (denote_comp (subst_comp_cons c v) hyps1)
                (denote_comp c (vv, hyps2)).
Proof.
  intros hyps1 hyps2 vv Hhyps Hvv. red in Hvv.
  specialize (denote_value_terminates _ _ v hyps1) as [vv' Hvv'].
  assert (Hvs : types_equiv t vv vv').
  {
    rewrite Hvv' in Hvv. apply rutt_inv_Ret in Hvv. symmetry. auto.
  }
  assert (Hvv'' : comp_equiv_rutt (denote_comp (subst_comp_cons c v) hyps1) 
                                  (denote_comp c (vv', hyps2))).
  eapply subst_correct0; eauto.
  rewrite Hvv''. apply types_equiv_comp_refl.
  symmetry in Hvs. constructor; auto.
  etransitivity; eauto. symmetry. auto.
Qed.

(* write another variant where we know denote_value v hyps1 rutt ret vv
   could use some rutt rewrite reasoning principles
*)
Theorem subst_correct t u Γ MR (c : comp u (t :: Γ) MR) (v : value t Γ) : 
  forall (hyps1 hyps2 : denote_ctx Γ),
    ctx_equiv Γ hyps1 hyps2->
    comp_equiv_rutt 
      (denote_comp (subst_comp_cons c v) hyps1)
                (vv <- denote_value v hyps2;; denote_comp c (vv, hyps2)).
Proof.
  intros.
  specialize (denote_value_terminates _ _ v hyps2) as [vv Hvv].
  red.
  assert (Hvveq : types_equiv t vv vv).
  {
    eapply denote_value_ret_equiv with (hyps1 := hyps2) (hyps2 := hyps2); eauto.
    etransitivity; eauto. symmetry. auto.
  }
  rewrite Hvv. setoid_rewrite bind_ret_l.
  eapply subst_correct0 with (c := c) in Hvv as Hvv'. eauto. 2: symmetry; eauto.
  specialize types_equiv_comp_refl with (c := c) as Hc.
  specialize types_equiv_comp_refl with (c := subst_comp_cons c v) as Hsubstc.
  specialize (Hsubstc _ _ H). rewrite Hsubstc.
  assert (Hhyps : ctx_equiv (t :: Γ) (vv, hyps2) (vv, hyps1) ).
  constructor; auto; symmetry; auto.
  symmetry in H. specialize (Hc _ _ Hhyps).
  rewrite Hc.
  apply subst_correct0; auto.
  Unshelve. eauto.
Qed.

