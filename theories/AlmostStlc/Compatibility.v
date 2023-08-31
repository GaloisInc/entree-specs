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
Require Export RecursionTrace.

Definition denote_comp_type t Γ MR : Type :=
  denote_ctx Γ -> mtree (denote_mfix_ctx MR) (denote_type t).

Definition denote_bodies_type Γ MR R1 R2 : Type :=
  denote_ctx Γ -> forall arg : denote_call_frame R2, mtree (denote_mfix_ctx (R1 :: MR)) (encodes arg).

Definition comp_bind {Γ MR t1 t2}
           (m1 : denote_comp_type t1 Γ MR)
           (m2 : denote_comp_type t2 (t1 :: Γ) MR) :
  denote_comp_type t2 Γ MR :=
  fun hyps => x <- m1 hyps;; m2 (x, hyps).

Definition interp_mrec_bodies {t Γ MR R} (bodies : denote_bodies_type Γ MR R R) (m : denote_comp_type t Γ (R :: MR)) 
           : denote_comp_type t Γ MR :=
  fun hyps => interp_mrec (bodies hyps) (m hyps).
  
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

          morally
          exists (ev_let E (close_comp Γ ρ c2)).

          need a substitution that uses ρ to turn c2 into
          a comp t2 [t1] MR,

          then I need theorems about the order of substitutions 

          there is a lot of ugly theory about closing substitutions I need

        *) 
      eexists.  eexists. eexists. split; eauto. split; [ | split]; eauto.
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


           should reduce/rewrite to 
           (vv1 <- k' vvret;; m2 (vv1, hyps)) <=j' (
              let (E[vret]]) (close ρ c2)


              and by H0 we know k' vvret <=j' E[vret] (for this specific j')
              and by Hmc2 we know forall j, m2 (vv1, hyps) <=j (close ρ c2)
           

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



Lemma mfix_compat t Γ R MR dbodies sbodies m (c : comp t Γ (R :: MR)):
  bodies_rel dbodies sbodies ->
  comp_rel m c ->
  comp_rel (interp_mrec_bodies dbodies m) (comp_mfix _ sbodies c).
Proof.
  intros Hbodies Hmc n hyps ρ Hhρ.
  constructor. intros. split.
  - intros vv Hvv. apply recursion_trace_den_ret in Hvv.
    destruct Hvv as [l Hrec]. 
    assert (approx_comp (n + length l) approx_val (m hyps) (close_comp Γ ρ c)).
    apply Hmc. 

    (* this is a major problem in order to use Hmc at n + len lI need to know the contexts approx 
                 each other at n + len l but I only know that for n
                 maybe this is the wrong level of abstraction, could I prove some core part of this lemma 
                 on closed terms and then use that to generalize?
     *)
    (* needs to be rutt, do that today?
    eapply recursion_trace_den_ret in Hvv.
    *)



(*
IH : forall m l vv, recursion_trace_den m l (ret vv) ->
     forall c, m <=(n + len l) c ->
       exists v, mfix bodies c ->* v /\ vv <=n v


   Base case : 
     m ≈ ret vv
     which means (ret vv) <=(n + len l) c so
     c ->* v where vv <=(n + len) v going the rest of the way is trivial assuming lemmas that should hold


   Inductive case :
    H1:m1 ≈ (vv <- call_term vvin;; k1 vv)
    H2:recursion_trace (vv <- (apply_bodies x vvin);; k1 vv ) l m3
    H3: m1 <=(n + len l + 1) c

    using H1 and H3 can learn that c ->* E[ca] where vvin <=(n + len l + 1) ca


    enough to show exists v, mfix bodies E[ca] ->* v /\ vv <=n v

    which I can prove using IH and a proof that vv <- (apply_bodies x vvin);; k1 vv <=(n + len l) E[ca]

    Intuitively this should be true and derivable from H1, H3 and the fact that c ->* E[ca]
    is this the equivalent of the lemma nick suggested? I feel like it might be look into this carefully


    two parts 
    1 : m <=n c and c ->* E[ca] then m <=n E[ca] ( probably wrong generality)
    2 : call_term vvin;; k <=n E[ca] ->

                  forall j, bodies vvin <=j c -> 
                         bodies vvin;; k <=(n - 1) let x = c1 in E[x]  (or is it at n + 1? that is strictly stronger)
                         ??? probably bugs in this statement maybe it is backwards, but I think the idea that removing a call lowers a step index seems sound
                         also might rely on bodies approximating a syntax at all levels


*)
