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
Require Export SemanticsFactsSeq.
Require Export CallMrecFacts.
Require Export SemanticsFactsSeq2.

Definition context_equiv {t} (c1 c2 : comp t [] []) :=
  forall b (r : bredex t [] + call_syn t []) (E : eval_context Nat [] r b) (n : nat),
    eval_rel (subst_eval_context E c1) (val_const n) <-> eval_rel (subst_eval_context E c2) (val_const n).
(*
Equations type_inj (t : type) (v : denote_type t) : closed_value t
*)

(*
Lemma types_equiv_eval_rel : 
  forall t MR (v1 v2 : closed_value t) (c : comp t [] MR),
    comp_equiv_rutt (denote_value v1 tt) (denote_value v2 tt) ->
    comp_equiv_rutt (denote_comp c tt) (denote_value v1 tt) -> eval_rel c v2.

(* need to give this more thought *)
Lemma equiv_value_eval_rel:
  forall (v : nat) (c : comp Nat [] []),
    comp_equiv_rutt (denote_comp c tt) (denote_value (val_const v) tt) -> eval_rel c (val_const v).
Proof.
  intros v c. revert v. dependent induction c; simp denote_comp.
  - intros. dependent destruction v; try inversion x.
    setoid_rewrite denote_value_equation_1 in H.
Abort.
 *)
Lemma subst_eval_context_proper:
  forall (t1 t2 : vtype) MR1 MR2 (c1 c2 : comp t1 [] MR2) (b : bool) (r : bredex t1 MR2 + call_syn t1 MR2)
    (E : eval_context t2 MR1 r b),
    comp_equiv_rutt (denote_comp c1 tt) (denote_comp c2 tt) ->
    comp_equiv_rutt (denote_comp (subst_eval_context E c1) tt)
                    (denote_comp (subst_eval_context E c2) tt).
Proof.
  intros t1 t2 MR1 MR2 c1 c2 b r E.
  revert c1 c2. dependent induction E; simp denote_comp; intros.
  - simp subst_eval_context. simp denote_comp. eapply IHE in H; eauto.
    eapply rutt_bind; eauto. intros. apply types_equiv_comp_refl.
    repeat constructor; auto.
  - simp subst_eval_context. simp denote_comp.
    eapply IHE in H; eauto. 
    eapply interp_mrec_rutt with 
        (RPreInv := call_frame_pre_equiv _)
        (RPostInv := call_frame_post_equiv _); intros; eauto.
    eapply types_equiv_mfix_bodies_refl. constructor. auto.
  - simp subst_eval_context. simp denote_comp.
    eapply IHE in H as IHE'; eauto. eapply mapE_rutt.
    eapply rutt_mon; try eapply IHE'; auto.
        apply mfix_pre_equiv_perm_handler.
        apply mfix_post_equiv_perm_handler.
  - simp subst_eval_context. simp denote_comp.
    eapply IHE in H as IHE'; eauto. eapply mapE_rutt.
    eapply rutt_mon; try eapply IHE'; auto.
        apply mfix_pre_equiv_lift_handler.
        apply mfix_post_equiv_lift_handler.
Qed.





(* this doesn't feel quite right *)
Lemma comp_equiv_value_eval:
  forall (t : vtype) (MR : mfix_ctx) (c : comp t [] MR) (v : closed_value t),
    comp_equiv_rutt (denote_comp c tt) (denote_value v tt) -> 
    exists (v' : closed_value t), comp_equiv_rutt (MR := MR) (denote_value v tt) (denote_value v' tt) -> eval_rel c v'.
Proof.
  intros t MR c v Hv. dependent induction c.
  - intros. exists v. intros. constructor. cbv. simp observe. auto.
  - intros. 
    (* might need to be more general and might need a different ind hyp,
       the problem is I don't know how to generalize this further because taking
       a step only seems to make sense for closed terms,
       could be more general if I went relational, but I want
       to try to find a different solution before biting that bullet

       I could possibly generalize by putting in an assumption that
       hypotheses all have corresponding values (stronger condition than in logical relation)

       could rely on folding substitution multiple times

       or could maybe generalize 

     *)
    specialize (IHc1 c1 eq_refl JMeq_refl).
Abort.


(* do we need lem, I think no because we have evidence tha denote_comp c is ret *)
Theorem adequacy : forall t (c1 c2 : comp t [] []),
    comp_equiv_rutt (denote_comp c1 tt) (denote_comp c2 tt) ->
    context_equiv c1 c2.
Proof.
  intros t c1 c2 Hden b r E v.
  assert (Hden' : comp_equiv_rutt (denote_comp (subst_eval_context E c1) tt)
                                  (denote_comp (subst_eval_context E c2) tt)).
  apply subst_eval_context_proper. auto.
  remember (subst_eval_context E c1) as c1'.
  remember (subst_eval_context E c2) as c2'.
  clear Heqc1' Heqc2'.
  split; intros Hc1.
  - generalize dependent c2'. clear - Hden Hc1.
    induction Hc1.
    + intros. apply IHHc1. apply step_stable in H.
      symmetry in H. etransitivity; eauto.
    + intros. apply step_stable2 in H.
      assert (Hv : comp_equiv_rutt (denote_comp c2' tt) (denote_value v0 tt) ).
      etransitivity; eauto. symmetry. auto. clear - Hv.
      red in Hv.
      (* my concern is that the inductive hyp may require *) 
      assert ((exists v', eval_rel c2' v') \/ ~ exists v', eval_rel c2' v').
      admit. (* classical reasoning *)
      destruct H.
      * destruct H as [v' Hv']. 
        red in v0, v'. dependent destruction v0; try inversion x.
        dependent destruction v'; try inversion x.
        enough (n = n0); subst; auto.
        apply eval_stable in Hv'.
        rewrite denote_value_equation_1 in Hv, Hv'.
        assert (comp_equiv_rutt (t := Nat) (MR := []) (ret n) (ret n0)).
        etransitivity; eauto. symmetry. auto.
        apply rutt_inv_Ret in H. simp types_equiv in H.
      * red in v0. dependent destruction v0; try inversion x.
        rewrite denote_value_equation_1 in Hv.
        exfalso. red in H.
        (* this seems like the best hope *)
        enough ((denote_comp c2' tt) ≈ EnTree.spin ).
        red in Hv. rewrite H0 in Hv. admit.
        eapply H. exists (val_const n).
        apply eval_stable in H.

(* transform H into evidence  that denote_comp c2' is spin,
           this contradicts Hv
         *) admit.
      (* maybe need that if denote_comp c tt = ret v then eval
         i get the feeling this might be easier to do with 
         relational, maybe also might be easier with lem 

         show the connect

       *)

        
      (* may be its own lemma *)
      constructor 2.
      apply  observe_inr_comp_ret.
      (* need to think this through carefully *)
      admit.
    remember ()
    generalize dependent c2.  dependent induction Hc1; intros.
    + specialize (IHHc1 b t c1 c2 Hden r E).
    
(* will need a logical relation for proving the last piece of adequacy, *)
