Require Export TypedVar.
Require Export SyntaxSeq.
Require Export SmallStepSeq.
Open Scope list_scope.
From Equations Require Import Equations Signature.
Require Import Coq.Program.Equality.
Require Import ExtLib.Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

(* bottoms out in exposed contexts *)
Inductive covered_in {t2 MR2} (ca : call t2 MR2) 
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
Lemma covered_in_intro t1 t2 MR1 MR2 (ca : call t2 MR2) (E : eval_context t1 MR1 (inr ca) false) : 
  covered_in ca E.
Proof.
  dependent induction E; try (destruct b; constructor; auto).
  constructor. apply IHE; auto.
Qed.

Lemma covered_in_step t1 t2 MR1 MR2 b (ca : call t2 MR2) (E : eval_context t1 MR1 (inr ca) b) :
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

Lemma progress_boxed_eval_context (t1 t2 : vtype) b (MR : mfix_ctx) (r : bredex t2 MR + call t2 MR) (E : eval_context t1 nil r b) : 
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
  unfold step. destruct (observe c); eauto.
  destruct b. left.
  specialize progress_boxed_eval_context with (E := E) as [c' Hc'].
  rewrite Hc'. eexists. reflexivity.
Qed.

(*
  dependent induction E; destruct r; try (simp step_eval_context; eexists; eauto; fail).
  - inversion c. inversion xR. 
  - simp step_eval_context.
    specialize (IHE E eq_refl JMeq_refl). destruct IHE as [c' Hc].
    rewrite Hc. cbn. eexists. eauto.
  - simp step_eval_context.
    assert (MR1 = R :: nil).
    {
      destruct xR; simp remove in x0; subst; auto.
      discriminate.
    }
    subst. clear x0. 

    dependent destruction x.
    assert (xR = VarZ).
    { clear - xR. dependent destruction xR. auto. inversion xR. }
    subst. simp remove in x0.
    apply JMeq_eq in x. subst.
    clear x0. 
    destruct b.
    + specialize step_eval_context_equation_4 with (bodies := bodies) (E := E) 
        (xR := VarZ) as Heq. destruct (normalize_eval_context c E).
      destruct x. 
      match goal with Heq : _ = ret ?x |- _ => set x as c0 end.
      exists c0. auto.
    + eexists. specialize step_eval_context_equation_5 with (bodies := bodies) (E := E) 
        (xR := VarZ) as Heq. 
      (* need a stronger inductive hypothesis, maybe a logical relation
       should encode the idea of a handled call_frame
       *)
      admit.
  - assert (MR1 = nil).
    { clear - Hperm. dependent induction Hperm. auto. eapply IHHperm1. auto. }
    subst. specialize (IHE E eq_refl JMeq_refl).
    destruct IHE as [c0 Hc0]. destruct b. simp step_eval_context; subst; cbn.
    + destruct (normalize_eval_context c E). destruct x. eexists. reflexivity.
    + simp step_eval_context. rewrite Hc0. cbn. eexists. eauto.
  - (* stop here for now, tomorrow finish this progress lemma, and use it 
       to prove the full progress theorem (show be trivial),
       also see if you can write the denotation function,

       and maybe get started on lemmas that substitution is like denoting 
       the argument and the open term separately and then composing the functions,
       

       then start working on 
     *)
*)
