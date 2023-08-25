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

Definition denote_comp_type t Γ MR : Type :=
  denote_ctx Γ -> mtree (denote_mfix_ctx MR) (denote_type t).

Definition comp_bind {Γ MR t1 t2}
           (m1 : denote_comp_type t1 Γ MR)
           (m2 : denote_comp_type t2 (t1 :: Γ) MR) :
  denote_comp_type t2 Γ MR :=
  fun hyps => x <- m1 hyps;; m2 (x, hyps).
  
(* 

   Lemma that is typically true according to nick
   e1 --> e1' => e1' <=j e2 => e1 <=(j+1) e2

   think about if this makes sense, especially in light of
   whether you decrement steps in the ret case 

*)


(* this might need to be an inductive proof *)
Lemma let_compat Γ MR t1 t2 
      (m1 : denote_comp_type t1 Γ MR) (m2 : denote_comp_type t2 (t1 :: Γ) MR)
      (c1 : comp t1 Γ MR) (c2 : comp t2 (t1 :: Γ) MR)
  : comp_rel m1 c1 -> comp_rel m2 c2 ->
    comp_rel (comp_bind m1 m2) (comp_let c1 c2).
Proof.
  intros Hmc1 Hmc2. intros n hyps ρ Hhρ.
  constructor. intros Hn. specialize (Hmc1 n hyps ρ Hhρ) as Hmc1n.
  inversion Hmc1n. intros. subst. destruct (H Hn) as [Hretmc1 Hstuckmc1]. clear H.
  split.
  - intros vv2 Hvv2. unfold comp_bind in Hvv2.
    assert (exists vv1, comp_equiv_rutt (m1 hyps) (ret vv1)).
    admit.
    destruct H as [vv1 Hvv1]. specialize (Hretmc1 vv1 Hvv1).
    destruct Hretmc1 as [v1 [Hv11 Hv12]].
    (* maybe steps should not decrement in the ret case? 
       I am concerned that might break other things  *) 
    assert (Hhρ' : closing_subst_approx n (t1 :: Γ) (vv1, hyps) (v1, ρ)).
    constructor; auto.
    assert (comp_equiv_rutt (m2 (vv1, hyps)) (ret vv2)).
    admit.
    specialize (Hmc2 n (vv1, hyps) (v1, ρ) Hhρ') as Hmc2n.
    inversion Hmc2n. 
    destruct (H0 Hn) as [Hretmc2 Hstuckmc2]. clear H0.
    apply Hretmc2 in H.
    destruct H as [v2 [Hv21 Hv22]]. exists v2. split; auto.
    admit.
  - intros. rename H into Hcall.
    (* start tomorrow by stating this lemma assertion  *)
    assert (Hcase :
             (exists k', comp_equiv_rutt (m1 hyps) (vv <- call_term x xR vvcall;; k' vv))
               \/
             (exists vv1, comp_equiv_rutt (m1 hyps) (ret vv1) /\ 
                       comp_equiv_rutt (m2 (vv1, hyps)) (vv <- call_term x xR vvcall;; k vv)
           )).
    admit.
    destruct Hcase as [[k' Hk'] | [vv1 [Hvv11 Hvv12] ]].
    + apply Hstuckmc1 in Hk' as Hcall'.
      destruct Hcall' as [vcall [E [c' [Hvcall [HE1 [HE2 HE3 ]] ]]] ].
       (* figure out how to construct the evaluation context that is morally this
          perhaps close_comp is not general enough 
          needs to be a more general substitution?


          
        *) 
      eexists. eexists. eexists. split; eauto. split; [ | split]; eauto.
      * admit.
      * admit.
      * intros. apply HE3 in H0; auto.
        (* concerned about this part 
           k vvret = k' vvret ;; m2 kyps
           use that to substitute in
           if I have an induction hypothesis according to <
           then maybe I can continue
           this is starting to look sketchy, but not necessarily unsalvageable

           also might be easier and sufficient to prove approx_comp composes with
           bind/let at a fixed j'
           

         *)
        admit.
   + apply Hretmc1 in Hvv11 as Hvv13. destruct Hvv13 as [v1 [Hv11 Hv12]].
     (* lost the thread a bit on this one *)
     assert (Hhρ' : closing_subst_approx n (t1 :: Γ) (vv1, hyps) (v1, ρ)).
     constructor; auto. specialize (Hmc2 _ _ _ Hhρ').
     inversion Hmc2. specialize (H Hn). destruct H as [Hretmc2 Hstuckmc2].
     subst. apply Hstuckmc2 in Hvv12 as Hvv13.
     destruct Hvv13 as [vcall [E [c' [Hvcall [HE1 [HE2 HE3 ]] ]]] ].
     exists vcall. eexists. eexists. split; [ auto | split ]; [ | split].
     * admit.
     * admit.
     * auto.
Admitted.
