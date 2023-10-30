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
Require Import Coq.Classes.Morphisms.
Require Export ClosingSubst.
Require Export LogicalApprox.
Require Export Compatibility.
Require Export RuttFacts.
Require Export ContextEquiv.

(* do compatibility lemmas first, one compatibility for each typing derivation  *)

Theorem fundamental_theorem_adequacy_mutind : 
  (forall t Γ MR (c : comp t Γ MR), comp_rel (denote_comp c) c) /\
  (forall t Γ (v : value t Γ) MR, val_rel (MR := MR) (denote_value v) v) /\
  (forall Γ MR R1 R2 (bodies : mfix_bodies Γ MR R1 R2), bodies_rel (denote_bodies bodies) bodies).
Proof.
  apply comp_value_mutind; intros.
  - apply const_compat.
  - apply nil_compat.
  - apply cons_compat; auto.
  - apply pair_compat; auto.
  - apply inl_compat; auto.
  - apply inr_compat; auto.
  - apply abs_compat; auto.
  - apply var_compat; auto.
  - specialize (H MR). apply ret_compat in H. eauto.
  - eapply let_compat in H; eauto. unfold comp_bind in H. eauto.
  - eapply match_nat_compat in H0; eauto. eauto.
  - specialize (H MR). eapply succ_compat in H. eauto.
  - eapply match_list_compat in H0; eauto. eauto.
  - eapply split_compat in H0; eauto. eauto.
  - specialize (H MR). eapply match_sum_compat in H; eauto. eauto.
  - specialize (H0 MR). eapply app_compat in H0; eauto.
    eauto.
  - specialize (H MR). eapply call_compat with (xR := xR) (x := x) in H; eauto.
  - eapply mfix_compat in H; eauto. eauto.
  - specialize (H0 MR). eapply tfix_compat in H0; eauto. eapply H0.
  - eapply lift_compat with (MR1 := MR1) in H; eauto.
  - eapply perm_compat with (Hperm := Hperm) in H; eauto.
  - apply mfix_bodies_nil_compat.
  - apply mfix_bodies_cons_compat; auto.
Qed.


Lemma adequacy_aux : forall (c : comp Nat [] []) (n : nat),
    comp_equiv (denote_comp c) (denote_value (val_const n)) ->
    eval_rel c (val_const n).
Proof.
  destruct fundamental_theorem_adequacy_mutind as [Had _].
  intros. 
  specialize (Had _ _ _ c). red in Had. red in H.
  specialize (H tt tt I). simp denote_comp in H.
  apply rutt_ret_eutt in H. simp types_equiv in H.
  apply eutt_ret_multi_step in H as [j Hj].
  specialize (Had (S j) tt tt (closing_subst_approx_nil _)).
  inversion Had. subst.
  assert (Hj' : j < S j). lia. 
  specialize (H j Hj'). destruct H as [Hret _].
  specialize (Hret n Hj). destruct Hret as [n' [Heval Happrox]].
  assert (Hj'' : S j - j = 1). lia. rewrite Hj'' in Happrox.
  red in n'. dependent destruction n'; try inversion x.
  rewrite approx_val_equation_2 in Happrox. subst n0.
  simp close_comp in Heval. apply eval_rel_stuck_eval_rel.
  auto.
Qed.

Lemma adequacy t Γ MR (c1 c2 : comp t Γ MR) : 
  comp_equiv (denote_comp c1) (denote_comp c2) ->
  context_equiv c1 c2.
Proof.
  intros Hden C n.
  assert (Hden' : comp_equiv 
                    (denote_comp (subst_comp_context C c1))
                    (denote_comp (subst_comp_context C c2))).
  eapply subst_comp_context_proper; eauto.
  remember (subst_comp_context C c1) as c1'.
  remember (subst_comp_context C c2) as c2'. clear Heqc1' Heqc2' Hden c1 c2.
  specialize (Hden' tt tt I).
  split; intros Hstep; apply adequacy_aux.
  - red. intros [] [] _. etransitivity. symmetry. eauto. apply eval_stable. auto.
  - red. intros [] [] _. etransitivity. eauto. apply eval_stable; auto.
Qed.


