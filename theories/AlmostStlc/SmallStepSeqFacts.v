Require Export TypedVar.
Require Export SyntaxSeq.
Require Export SmallStepSeq.
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
  simp observe. unfold step in H. destruct (observe c); try destruct b;
    try discriminate.
  f_equal. destruct r.
  - simp step_eval_context. cbn. f_equal. simp subst_eval_context. injection H.
    intros. clear H. rewrite step_eval_context_equation_1 in H0.
    injection H0. intros. subst. clear H0. auto.
  - simp step_eval_context. cbn. injection H. intros. rewrite H0. auto.
Qed.
