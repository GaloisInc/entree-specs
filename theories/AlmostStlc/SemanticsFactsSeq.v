Require Export TypedVar.
Require Export SyntaxSeq.
Require Export SmallStepSeq.
Require Export DenotationFacts.
Require Export DenotationSeq.
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
  | covered_in_mfix_base t MR1 R (xR : var R MR1) 
                    (bodies : mfix_bodies nil MR1 R)
                    (E : eval_context t MR1 (inr ca) true) : 
    covered_in ca t _ _ (ev_mfix true xR bodies E)

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
  | covered_in_mfix t MR1 R (xR : var R MR1) 
                    (bodies : mfix_bodies nil MR1 R)
                    (E : eval_context t MR1 (inr ca) false) : 
    covered_in ca t MR1 false E ->
    covered_in ca t _ false (ev_mfix false xR bodies E)

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
(*
Fixpoint equiv_type (t : type) : denote_type t -> denote_type t -> Prop :=
  match t with 
  | Nat => eq
  | Pair t1 t2 => fun '(v1, v2) '(v3, v4) => equiv_type t1 v1 v3 /\ equiv_type t2 v2 v4
  | Arrow t1 
*)

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

(* comp_value_mutind *)
Lemma comp_val_bodies_map : 
  (forall t Γ1 MR (c : comp t Γ1 MR), forall Γ2 (f : forall t', var t' Γ1 -> var t' Γ2) 
  (hyps : denote_ctx Γ2),
  denote_comp (comp_map c f) hyps ≈ denote_comp c (var_map_weaken f hyps) ) /\
  (forall t Γ1 (v : value t Γ1) MR Γ2  (f : forall t', var t' Γ1 -> var t' Γ2) 
  (hyps : denote_ctx Γ2),
  denote_value (MR := MR) (val_map v f) hyps ≈ denote_value v (var_map_weaken f hyps)) /\
  (forall Γ1 MR R (bodies : mfix_bodies Γ1 MR R) Γ2 (f : forall t', var t' Γ1 -> var t' Γ2) 
      (arg : denote_call_frame R)
      (hyps : denote_ctx Γ2),
  denote_bodies (bodies_map bodies f) hyps arg ≈ denote_bodies bodies (var_map_weaken f hyps) arg).
Proof.
  apply comp_value_mutind; intros; auto.
  - rewrite val_map_equation_1. repeat rewrite denote_value_equation_1. 
    reflexivity.
  - rewrite val_map_equation_2. repeat rewrite denote_value_equation_2. reflexivity.
  - rewrite val_map_equation_3. repeat rewrite denote_value_equation_3. rewrite H.
    setoid_rewrite H0. reflexivity.
  - rewrite val_map_equation_4. repeat rewrite denote_value_equation_4.
    rewrite H. setoid_rewrite H0. reflexivity.
  - rewrite val_map_equation_5. repeat rewrite denote_value_equation_5.
    apply eqit_Ret. admit.
  - rewrite val_map_equation_6. repeat rewrite denote_value_equation_6.
    apply eqit_Ret. apply index_weaken.
  - simp comp_map. simp denote_comp.
  - simp comp_map. simp denote_comp. rewrite H. setoid_rewrite H0.
    simp var_map_weaken.
    assert (forall v : denote_type t1, var_map_weaken (var_map_skip f) (v, hyps) = (v, var_map_weaken f hyps)). apply var_map_weaken_skip; auto.
    eapply eqit_bind. reflexivity. intros. subst. rewrite H1. reflexivity.
  - simp comp_map. simp denote_comp.
    rewrite H.
    eapply eqit_bind. reflexivity. intros. subst.
    destruct u2; eauto. eapply H0.
    rewrite H1. rewrite var_map_weaken_skip. reflexivity.
  - simp comp_map. simp denote_comp.
    rewrite H. eapply eqit_bind. reflexivity.
    intros. subst. destruct u2. eapply H0.
    simp var_map_skip. 
    specialize var_map_weaken_skip with (t1 := List t1) (v := u2) as H2.
    rewrite <- H2.
    specialize var_map_weaken_skip with (v := d) (Γ2 := List t1 :: Γ2) 
      (hyps := (u2, hyps) ) (f := var_map_skip f) as H3.
    setoid_rewrite <- H3. 
    simp var_map_weaken. simp index_ctx. simp var_map_skip.
    simp index_ctx. simp var_map_weaken.
    admit. (* maybe there are better abstractions and lemmas for reasoning *)
  - simp comp_map. simp denote_comp. rewrite H.
    eapply eqit_bind. reflexivity. intros. subst. destruct u2.
    (* similar to previous *) admit.
  - simp comp_map. simp denote_comp. rewrite H.
    eapply eqit_bind. reflexivity. intros. subst.
    rewrite H0. reflexivity.
  - simp comp_map. simp denote_comp. rewrite H. reflexivity.
  - simp comp_map. simp denote_comp. setoid_rewrite H0.
    (* think carefully about the relation here and might need another
       properness for interp *)
    admit.
Admitted.

Lemma comp_map_correct t Γ1 Γ2 MR (c : comp t Γ1 MR) (f : forall t', var t' Γ1 -> var t' Γ2) 
  (hyps : denote_ctx Γ2) :
  denote_comp (comp_map c f) hyps ≈ denote_comp c (var_map_weaken f hyps).
Proof.
  intros. destruct comp_val_bodies_map. auto.
Qed.

Lemma val_map_correct t Γ1 Γ2 MR (v : value t Γ1) (f : forall t', var t' Γ1 -> var t' Γ2) 
  (hyps : denote_ctx Γ2) :
  denote_value (MR := MR) (val_map v f) hyps ≈ denote_value v (var_map_weaken f hyps).
Proof.
  intros. destruct comp_val_bodies_map as [ ? [? ?] ]. auto.
Qed.

Lemma bodies_map_correct Γ1 Γ2 MR R (bodies : mfix_bodies Γ1 MR R) (f : forall t', var t' Γ1 -> var t' Γ2) 
      (arg : denote_call_frame R)
      (hyps : denote_ctx Γ2) : 
  denote_bodies (bodies_map bodies f) hyps arg ≈ denote_bodies bodies (var_map_weaken f hyps) arg.
Proof.
  intros. destruct comp_val_bodies_map as [ ? [? ?] ]. auto.
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




Lemma subst_correct_aux t u Γ1 Γ2 MR (c : comp u (Γ1 ++ [t] ++ Γ2) MR)  : 
  forall (v : value t Γ2) (hyps1 : denote_ctx Γ1) (hyps2 : denote_ctx Γ2) v',
    denote_value (MR := MR) v hyps2 ≈ ret v' ->
    denote_comp (subst_comp c v) (hyps1 +++ hyps2) ≈
                denote_comp c (insert_ctx v' (hyps1 +++ hyps2)).
Proof.
  (* need dependent induction for compm value and subst,
     will need reasoning principles for subst_var, and all of the weakings,
     which means reasoning principle for comp_map
*)
  dependent induction c.
Admitted.

Theorem subst_correct t u Γ MR (c : comp u (t :: Γ) MR) (v : value t Γ) : 
  forall (hyps : denote_ctx Γ) v',
    denote_value (MR := MR) v hyps ≈ ret v' ->
    denote_comp (subst_comp_cons c v) hyps ≈
                denote_comp c (v', hyps).
Proof.
  intros. specialize (subst_correct_aux t u nil Γ MR c v tt _ _ H) as Heq.
  simp hyps_app in Heq.
Qed.
