
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

(* do compatibility lemmas first, one compatibility for each typing derivation  *)

Theorem fundamental_theorem_adequacy :
  forall n,
  (forall (t : vtype) (Γ : ctx) (MR : mfix_ctx) (c : comp t Γ MR) (ρ : closing_subst Γ) (hyps : denote_ctx Γ), 
      closing_subst_approx n Γ hyps ρ-> approx_comp n approx_val (denote_comp c hyps)  (close_comp Γ ρ c) 
  ) /\
  (forall (t : vtype) (Γ : ctx) (v : value t Γ) (ρ : closing_subst Γ) (hyps : denote_ctx Γ), 
      closing_subst_approx n Γ hyps ρ -> forall vv MR, comp_equiv_rutt (ret vv) (denote_value (MR := MR) v hyps) -> approx_val n t vv (close_value Γ ρ v)) /\
  (forall (Γ : ctx) (MR : mfix_ctx) (R1 R2 : call_frame) (bodies : mfix_bodies Γ MR R1 R2) (ρ : closing_subst Γ) (hyps : denote_ctx Γ), 
      closing_subst_approx n Γ hyps ρ -> 
      log_rel_bodies_step n (denote_bodies bodies hyps) (close_bodies Γ ρ bodies)).
Proof.
  intros n. induction n as [ n IHn ] using (well_founded_induction lt_wf).
  (*
  destruct n.
  {
    split. 2 : split.
    all : intros.
    - constructor. intros. lia.
    - simp approx_val. auto.
    - simp log_rel_bodies_step.
      dependent induction bodies.
      simp log_rel_bodies_step. simp close_bodies. admit.
      admit. (* this should hold, but the relation is in a very sketchy state right now,
                so don't bother*)
  } *) (*
  assert (IHnc : forall y, y < n -> 
          (forall (t : vtype) (Γ : ctx) (MR : mfix_ctx) (c : comp t Γ MR) (ρ : closing_subst Γ)
           (hyps : denote_ctx Γ),
         closing_subst_approx y Γ hyps ρ ->
         approx_comp y approx_val (denote_comp c hyps) (close_comp Γ ρ c) )).
  { intros m Hm. apply IHn in Hm. tauto. }
  assert (IHnv : forall y, y < n -> 
         (forall (t : vtype) (Γ : ctx) (v : value t Γ) (ρ : closing_subst Γ) (hyps : denote_ctx Γ),
          closing_subst_approx y Γ hyps ρ ->
         forall (vv : denote_type t) (MR : mfix_ctx),
         comp_equiv_rutt (MR := MR) (denote_value v hyps) (ret vv) -> approx_val y t vv (close_value Γ ρ v))).
  { intros m Hm. apply IHn in Hm. intros. eapply Hm; eauto. symmetry. apply H0. }
  assert (IHnbodies : forall y, y < n -> 
         (forall (Γ : ctx) (MR : mfix_ctx) (R1 R2 : call_frame) (bodies : mfix_bodies Γ MR R1 R2)
           (ρ : closing_subst Γ) (hyps : denote_ctx Γ),
         closing_subst_approx y Γ hyps ρ ->
         log_rel_bodies_step y (denote_bodies bodies hyps) (close_bodies Γ ρ bodies))).
  { intros m Hm. apply IHn in Hm. tauto. }
  clear IHn.
  apply comp_value_mutind; intros; auto.
  - rewrite denote_value_equation_1 in H0. apply rutt_inv_Ret in H0.
    simp types_equiv in H0. subst.
    (* show that close_value (val_const) is val_const *) admit.
 - rewrite denote_value_equation_2 in H0. apply rutt_inv_Ret in H0.
   inversion H0. subst.
   (*show close_value val_nil is val_nil *) admit.
 - rewrite denote_value_equation_3 in H2. 
   admit.
 - rewrite denote_value_equation_4 in H2. destruct vv as [vv1 vv2].
   (* wts close_value commutes with val_pair *) admit.
 - rewrite denote_value_equation_5 in H1. apply rutt_inv_Ret in H1.
   rename vv into f.
   rewrite close_value_abs.
   (* there is another reasoning principle I need here *)
   destruct n; simp approx_val; auto. intros vv v m' Hm' Hvv Hv.
   apply lower_approx_comp_aux3; auto.  
   specialize (IHnc m' Hm'). Locate close_comp_app. Locate close_comp. (* do these functions need to be separately defined does one subsume the other? *)
   assert (subst_comp_cons (close_comp_app (Γ1 := [t1]) ρ cbody) v = close_comp (t1 :: Γ) (v,ρ) cbody ).
   (* admitted lemma *)
   rewrite subst_comp_const_close. simp close_comp. auto.
   rewrite H2.
   simp types_equiv in H1.   
   specialize (H1 vv vv Hvv).
   rewrite H1.
   eapply IHnc. constructor; auto.
   eapply lower_closing_subst_approx; eauto.
 - rewrite denote_value_equation_6 in H0.
   apply rutt_inv_Ret in H0.
   clear - H H0. rewrite H0. clear H0. dependent induction x.
   + destruct ρ as [v ρ]. destruct hyps as [vv0 hyps]. dependent destruction H. simp index_ctx.
     simp close_value. unfold subst_value_cons. simp subst_value. admit.
   + destruct ρ as [v ρ]. destruct hyps as [vv0 hyps]. simp index_ctx.
     (* should just write a lemma about close_value *)
     simp close_value. (* subst_value_cons (var (VarS x)) x = var x*)
     admit.
   (* this makes sense but lets put it in a separate lemma 
   dependent induction H. inversion x.
   dependent destruction x.
   + simp close_value. unfold subst_value_cons. rewrite subst_value_equation_6. simp subst_var.
     simp index_ctx in H1. rewrite H1. admit.
   + simp close_value. simp index_ctx in H1. rewrite H1. unfold subst_value_cons. simp subst_value.

   dependent induction x.
   + destruct ρ as [vv0 ρ]. simp close_value. rename l into Γ. (* need to induct on Γ*) admit.
   + destruct  ρ as [vv0 ρ]. simp close_value.

   admit. admit. *)
 - rewrite denote_comp_equation_1. constructor. intros. split.
   + intros. exists (close_value Γ ρ v). symmetry in H2. eapply H in H0; eauto.
     split. admit. (* prove close_comp commutes with comp_ret *)
     eapply lower_approx_val; try apply H0; eauto. lia.
   + intros. specialize denote_value_terminates with (v := v) (hyps := hyps) as [ vv Hterm].
     red in H2. rewrite Hterm in H2.
     (* prove call_term has a vis at the head, then derive contradiction from H2 *)
     admit.
 - rewrite denote_comp_equation_2. apply H in H1 as Hc1.
   rename H0 into Hc2.  inversion Hc1. subst. 
   constructor. intros Hn. specialize (H0 Hn) as [Hretc1 Hstuckc1]. split.
   + intros vv3 Hvv3. 
     assert (exists vv1, comp_equiv_rutt (denote_comp c1 hyps) (ret vv1) ).
     admit. 
     destruct H0 as [vv1 Hvv1]. 
     specialize (Hretc1 vv1 Hvv1) as [v1 [Hv11 Hv12]].
     assert (HΓ : closing_subst_approx (n - 1) (t1 :: Γ) (vv1,hyps) (v1, ρ)).
     { constructor. auto. eapply lower_closing_subst_approx; eauto. lia. }
     eapply IHnc with (c := c2) in HΓ as Hc2'.
     inversion Hc2'. subst. rename H0 into Hpredn. 
     assert (n = 1 \/ n - 1 > 0). lia.
     destruct H0.
     * subst. cbn in *.
       (* think this through carefully, there seems to be a problem if n = 1*) admit.
     * destruct (Hpredn H0) as [Hretc2 Hstuckc2]. clear Hpredn.

     (* problem with rewriting with comp_equiv_rutt and bind rewrite Hvv1 in Hvv3. *)
     
     
        (* can use Hvv3 to prove that c1 and c2 evaluate to rets
           then use Hretc1 to create a closing subst
         *)
    (* destruct H2 as [Hc11 Hc12].
   constructor. admit. split.
   + intros.
     assert (Hvv1 : exists vv1, comp_equiv_rutt (denote_comp c1 hyps) (ret vv1) ).
     admit.
     destruct Hvv1 as [vv1 Hvv1]. apply Hc11 in Hvv1 as Hvv1'.
     destruct Hvv1' as [v1 [Hv11 Hv12]]. clear Hc12.
     assert (Hρ :  closing_subst_approx (S n) (t1 :: Γ) (v1, ρ) (vv1, hyps)).
     constructor; auto.
     specialize (Hc2 (v1, ρ) (vv1, hyps) Hρ). inversion Hc2.
     subst. destruct H4 as [Hc21 Hc22]. clear Hc22.
     assert (Hvv2 : exists vv2, comp_equiv_rutt (denote_comp c2 (vv1,hyps)) (ret vv2)).
     admit.
     destruct Hvv2 as [vv2 Hvv2].
     apply Hc21 in Hvv2 as Hvv2'. destruct Hvv2' as [v2 [Hv21 Hv22] ].
     assert (types_equiv _ vv2 vv).
     (* from H2 and the equivalence to rets *) admit.
     exists v2.
     split.
     (* congruence rules I will need to make + Hvv1 and Hv11 Hv21 *)
     admit.
     (* rewrite acording to the types_equiv in H4 *)
     admit.
   + intros.
     (* will need itree rule that either denote_comp c1 as a vis, or 
        denote_comp c1 is a ret and denote_comp c2 is a vis
      *) admit.
 - rewrite denote_comp_equation_3. (*comp_match_nat and bind *)
   admit.
 - rewrite denote_comp_equation_4. (* comp_match_list and bind *)
   admit.
 - rewrite denote_comp_equation_5. (* comp_split and bind *)
   admit.
 - rewrite denote_comp_equation_6. constructor. admit. split.
   + intros.
     assert (Hf : exists f, comp_equiv_rutt (MR := MR) (denote_value vf hyps) (ret f)).
     admit.
     destruct Hf as [f Hf]. specialize (H _ _ H1 _ _ Hf).
     assert (Harg : exists arg, comp_equiv_rutt (MR := MR) (denote_value varg hyps) (ret arg)).
     admit.
     destruct Harg as [arg Harg].
     specialize (H0 _ _ H1 _ _ Harg).
     (* here is a situation where the amount of steps needs to decrease,
        rewrite the approx_comp
      *)
     simp approx_val in H.

   (* comp_app and bind *)
   admit.
 - rewrite denote_comp_equation_7. (* comp_call and bind *)
   admit.
 - rewrite denote_comp_equation_8. (* comp_mfix and interp_mrec *)
   apply H0 in H1 as Hc. inversion Hc. subst. destruct H3 as [Hc1 Hc2].
   apply H in H1 as Hbodies. 
   (* I think this is showing I have the wrong bodies logical relation,
      that idea I had that had something to do with bodies steps c
      either to a ret or to an inr, then we need extra reasoning to 
      bring the small step up to speed and the denotation
    *) admit.
 - rewrite denote_comp_equation_9. apply H in H0 as Hc.
   inversion Hc. subst. destruct H2 as [Hc1 Hc2].
   constructor. admit.
   split.
   + intros. 
     (* H1 can tell us everything about denote_comp c then we apply Hc1 to that info
        then we know how c steps
      *) admit.
   + intros.
     (* similar thing going on *) admit.
 - rewrite denote_comp_equation_10. apply H in H0 as Hc.
   inversion Hc. subst. destruct H2 as [Hc1 Hc2].
   (* morally similar to the previous *)
   admit.
 - (* these cases are too broken to bother with right now *) admit.
 - admit. *) *)
Admitted.

Lemma adequacy : forall (c : comp Nat [] []) (n : nat),
    comp_equiv (denote_comp c) (denote_value (val_const n)) ->
    eval_rel c (val_const n).
Proof.
  destruct (fundamental_theorem_adequacy 2) as [Had _].
  intros c n Hc.
  specialize (Had Nat [] [] c tt tt (closing_subst_approx_nil 2)).
  inversion Had. subst. clear Had. assert (2 > 0). auto. specialize (H H0) as [Hret _]. 
  specialize (Hc tt tt I). apply Hret in Hc. clear - Hc. destruct Hc as [m [Hm1 Hm2]]. 
  cbn in *. red in m. dependent destruction m; try inversion x. simp approx_val in Hm2.
  subst. simp close_comp in Hm1. rename n0 into n. dependent induction Hm1.
  - eapply eval_rel_step; eauto.
  - eapply eval_rel_val; auto.
Qed.
