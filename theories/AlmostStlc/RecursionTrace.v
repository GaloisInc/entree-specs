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

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Tacs
     Basics.HeterogeneousRelations
     Eq.Paco2.

Section RecursionTrace.

Context (D E : Type) `{EncodedType D} `{EncodedType E}.
Context (bodies : forall (d : D), entree (D + E) (encodes d)).

(* this is a little messy *)
Inductive recursion_trace {A : Type} : 
  entree (D + E) A -> list D -> entree E A -> Prop := 
  | recursion_trace_ret_in t vv : t ≈ ret vv -> recursion_trace t [] (ret vv)
  | recursion_trace_inr_in t (e : E) k1 k2  : 
    t ≈ (Vis (inr e) k1) -> (forall x, interp_mrec bodies (k1 x) ≈ interp_mrec bodies (k2 x)) -> 
    recursion_trace t [] (Vis e (fun vv => (interp_mrec bodies (k2 vv))))
  | recursion_trace_inl_in t1 (d : D) k1 t2 l t3: 
    t1 ≈ (Vis (inl d) k1) ->
    t2 ≈ (bind (bodies d) k1) ->
    recursion_trace t2 l t3 ->
    recursion_trace t1 (d :: l) t3

.


Instance recursion_trace_eutt A : Proper (eutt eq ==> eq ==> eq ==> Basics.flip Basics.impl) (@recursion_trace A).
Proof.
  repeat intro. subst. generalize dependent x.
  induction H4.
  - constructor. rewrite H2. auto.
  - intros. econstructor. rewrite H3. eauto. auto.
  - intros. econstructor; eauto. rewrite H3. auto.
Qed.

Lemma recursion_trace_ret R (t : entree (D + E) R) r: 
  interp_mrec bodies t ≈ ret r ->
  exists (l : list D), recursion_trace t l (ret r).
Proof.
  intros Hret. punfold Hret. red in Hret.
  cbn in Hret. remember (RetF r) as y.
  remember (observe (interp_mrec bodies t)) as x.
  assert (go _ _ x ≅ interp_mrec bodies t). subst. rewrite <- entree_eta. reflexivity.
  clear Heqx. generalize dependent H1. revert t.
  hinduction Hret before bodies; intros; inv Heqy.
  - unfold interp_mrec in H1.
    destruct (observe t) eqn : Heq; try destruct e.
    + setoid_rewrite interp_mrec_ret in H1. apply eqit_Ret_inv in H1. subst.
      symmetry in Heq. apply simpobs in Heq. exists []. constructor. rewrite Heq. reflexivity.
    + setoid_rewrite interp_mrec_tau in H1. pinversion H1. inv CHECK.
    + setoid_rewrite interp_mrec_vis_inl in H1. pinversion H1; inv CHECK.
    + setoid_rewrite interp_mrec_vis_inr in H1. pinversion H1; inv CHECK.
  - unfold interp_mrec in H1. destruct (observe t) eqn : Heq; try destruct e.
    + setoid_rewrite interp_mrec_ret in H1. pinversion H1; inv CHECK. inv CHECK0.
    + setoid_rewrite interp_mrec_tau in H1. specialize (IHHret r eq_refl t0). 
      assert (t1 ≅ interp_mrec bodies t0). pinversion H1; try inv CHECK; try inv CHECK0.
      apply REL. rewrite <- entree_eta in IHHret. apply IHHret in H2.
      destruct H2 as [l Hl]. exists l. symmetry in Heq. apply simpobs in Heq.
      rewrite <- Heq. rewrite tau_eutt. auto.
    + setoid_rewrite interp_mrec_vis_inl in H1.
      assert (t1 ≅ (interp_mrec bodies (x <- bodies d;; k x))).
      pinversion H1; try inv CHECK; try inv CHECK0. auto.
      specialize (IHHret r eq_refl (x <- bodies d;; k x)).
      rewrite <- entree_eta in IHHret. specialize (IHHret H2).
      destruct IHHret as [l Hl].
      exists (d :: l). eapply recursion_trace_inl_in; eauto. 2 : reflexivity.
      symmetry in Heq. apply simpobs in Heq. rewrite Heq. reflexivity.
    + setoid_rewrite interp_mrec_vis_inr in H1. pinversion H1. inv CHECK0.
Qed.


Lemma recursion_trace_vis R (t : entree (D + E) R) e k :
  interp_mrec bodies t ≈ Vis e (fun x => interp_mrec bodies (k x)) ->
  exists (l : list D), recursion_trace t l (Vis e (fun x => interp_mrec bodies (k x))).
Proof.
  intros Hvis. punfold Hvis. red in Hvis.
  cbn in Hvis. remember (VisF e (fun x => interp_mrec bodies (k x))) as y.
  remember (observe (interp_mrec bodies t)) as x.
  assert (go _ _ x ≅ interp_mrec bodies t). subst. rewrite <- entree_eta. reflexivity.
  clear Heqx. generalize dependent H1. revert t.
  hinduction Hvis before bodies; intros; inv Heqy.
  - inj_existT. subst. unfold interp_mrec in H1.
    destruct (observe t) eqn : Heq; try destruct e.
    + setoid_rewrite interp_mrec_ret in H1. pinversion H1.
    + setoid_rewrite interp_mrec_tau in H1. pinversion H1. inv CHECK.
    + setoid_rewrite interp_mrec_vis_inl in H1. pinversion H1; inv CHECK.
    + pclearbot. setoid_rewrite interp_mrec_vis_inr in H1. exists []. 
      symmetry in Heq. apply simpobs in Heq. rewrite <- Heq.
      assert (e0 = e). pinversion H1. auto. subst. 
      econstructor. reflexivity. intros.
      eapply eqit_Vis_inv in H1. Unshelve. 2: auto. rewrite <- H1. apply REL.
  - unfold interp_mrec in H1. destruct (observe t) eqn : Heq; try destruct e0.
    + setoid_rewrite interp_mrec_ret in H1. pinversion H1; inv CHECK. inv CHECK0.
    + setoid_rewrite interp_mrec_tau in H1. specialize (IHHvis e k eq_refl t0). 
      assert (t1 ≅ interp_mrec bodies t0). pinversion H1; try inv CHECK; try inv CHECK0.
      apply REL. rewrite <- entree_eta in IHHvis. apply IHHvis in H2.
      destruct H2 as [l Hl]. exists l. symmetry in Heq. apply simpobs in Heq.
      rewrite <- Heq. rewrite tau_eutt. auto.
    + setoid_rewrite interp_mrec_vis_inl in H1.
      assert (t1 ≅ (interp_mrec bodies (x <- bodies d;; k0 x))).
      pinversion H1; try inv CHECK; try inv CHECK0. auto.
      specialize (IHHvis e k eq_refl (x <- bodies d;; k0 x)).
      rewrite <- entree_eta in IHHvis. specialize (IHHvis H2).
      destruct IHHvis as [l Hl].
      exists (d :: l). eapply recursion_trace_inl_in; eauto. 2 : reflexivity.
      symmetry in Heq. apply simpobs in Heq. rewrite Heq. reflexivity.
    + setoid_rewrite interp_mrec_vis_inr in H1. pinversion H1. inv CHECK0.
Qed.

End RecursionTrace.


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
(* did I already prove this somewhere else?*)
