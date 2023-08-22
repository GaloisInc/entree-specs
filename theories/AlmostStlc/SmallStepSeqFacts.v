Require Export TypedVar.
Require Export SyntaxSeq.
Require Export SmallStepSeq.
Require Export SemanticsFactsSeq.
Import List.ListNotations.
Open Scope list_scope.
From Equations Require Import Equations Signature.
Require Import Coq.Program.Equality.

Lemma step_ret t MR (v : closed_value t) :
  step (MR := MR) (comp_ret v) = inr v.
Proof.
  cbv. simp observe. auto.
Qed.


Lemma step_let t1 t2 MR (c1 c1' : comp t1 [] MR) (c2 : comp t2 [t1] MR) :
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

(* probably the most complicated one
   covered_in SemanticsFactsSeq.v might be a useful abstraction
   keep an eye out for counter example,
   maybe it evaluates in a different order than you are thinking
   figure out what the boolean in step_eval_context is

   still pretty confident it should be true, but should also consider
   what related property might be true
*)
Locate step_eval_context.
Lemma step_mfix t R MR (bodies : mfix_bodies [] MR R R) (c c' : comp t [] (R :: MR)) : 
  step_rel c c' ->
  step_rel (comp_mfix _ bodies c) (comp_mfix _ bodies c').
Proof.
  intros [?]. constructor. unfold step in *.
  simp observe. destruct (SmallStepSeq.observe c0); try destruct b; try discriminate.
  f_equal. destruct r; simp step_eval_context.
  - cbn. f_equal. injection H. clear H. intros.
    simp step_eval_context in H.
    cbn in H. injection H. intros. subst; auto.
  - injection H. clear H. intros. clear c c' c0. rename c'0 into c.
    destruct b.
    + simp step_eval_context. admit.
    + simp step_eval_context. cbn. rewrite H. auto.
    dependent induction E.
    + simp step_eval_context in H. discriminate.
    + simp step_eval_context in H. cbn in H.
      destruct (step_eval_context b (inr c1) E) eqn : Heq.
      * injection H. clear H. intros. subst.
        eapply IHE with (bodies := bodies) in Heq; eauto.
        destruct b.
        -- simp step_eval_context in Heq. simp step_eval_context.
           admit.
    destruct b.
    + simp step_eval_context. 
      simp step_eval_context in H.
      dependent destruction E.
      * simp step_eval_context in H. discriminate.
      * simp normalize_eval_context. simp step_eval_context in H.
        cbn in H. specialize (IHE c1 MR R bodies).

injection H. clear H. intros. dependent induction E.
      * simp step_eval_context in H. discriminate.
      * simp normalize_eval_context. simp step_eval_context in H.
        cbn in H.

      admit.
    + injection H. intros. rewrite H0. auto.
Admitted.
