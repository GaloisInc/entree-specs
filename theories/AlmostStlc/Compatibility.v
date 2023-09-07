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

Lemma multi_step_vis_dep_inv E `{EncodedType E} R S U
      (t : entree E R) (k1 : R -> entree E S) k2 n e (f : encodes e -> U) :
  encodes e = U ->
  JMeq f (@id U) ->
  multi_step n (vv <- t;; k1 vv) (vv <- (Vis e (fun x => Ret (f x)));; k2 vv) -> 
  (exists (j1 j2 : nat) r, j1 + j2 = n /\ multi_step j1 t (ret r) /\
                             multi_step j2 (k1 r) (vv <- (Vis e (fun x => Ret (f x)));; k2 vv)) \/
  (exists k1', multi_step n t (vv <- (Vis e (fun x => Ret (f x)));; k1' vv) /\
            forall vv1, vv2 <- k1' vv1;; k1 vv2 ≅ k2 vv1).
Proof.
  intros He Hid Hn. setoid_rewrite bind_vis in Hn.
  eapply multi_step_vis_bind_inv in Hn.
  destruct Hn as [[j1 [j2 [r [Hj [Hstep1 Hstep2]]]]] | [k1' [Hstep Heq] ] ].
  - left. exists j1, j2, r. do 2 (split; auto). setoid_rewrite bind_vis. auto.
  - right. setoid_rewrite bind_ret_l in Heq. subst. exists k1'. split; auto.
    unfold id in *. setoid_rewrite bind_vis.
    enough (Vis e k1' ≅ Vis e (fun x : encodes e => EnTree.bind (Ret x) (fun vv : encodes e => k1' vv))).
    rewrite <- H0. auto. apply eqit_Vis. intros. rewrite bind_ret_l. reflexivity.
Qed.


Lemma multi_step_call_term_bind_inv T1 T2 MR R tin tout (xR : var R MR) (x : var (tin, tout) R) vvin 
      (t : mtree (denote_mfix_ctx MR) T1) (k1 : T1 -> mtree (denote_mfix_ctx MR) T2) k2 n :
  multi_step n (vv <- t;; k1 vv) (vv <- call_term x xR vvin;; k2 vv) -> 
  (exists (j1 j2 : nat) (r : T1), j1 + j2 = n /\ multi_step j1 t (ret r) /\ multi_step j2 (k1 r) (vv <- call_term x xR vvin;; k2 vv)) \/
  (exists k1', multi_step n t (vv <- call_term x xR vvin;; k1' vv) /\ forall vv1, vv2 <- k1' vv1;; k1 vv2 ≅ k2 vv1).
Proof.
  unfold call_term. destruct (call_mrec x xR vvin) as [d f] eqn : Heqx.
  intros Hn. 
  setoid_rewrite bind_trigger in Hn. setoid_rewrite bind_trigger. 
  eapply multi_step_vis_dep_inv in Hn; eauto.
  - specialize call_mrec_encodes with (xt := x) (xR := xR) (c := vvin). 
    rewrite Heqx. auto.
  - specialize call_mrec_cont with (xt := x) (xR := xR) (c := vvin). 
    rewrite Heqx. auto.
Qed.

(*
(* this might need to be an inductive proof *)
Lemma let_compat Γ MR t1 t2 
      (m1 : denote_comp_type t1 Γ MR) (m2 : denote_comp_type t2 (t1 :: Γ) MR)
      (c1 : comp t1 Γ MR) (c2 : comp t2 (t1 :: Γ) MR)
  : comp_rel m1 c1 -> comp_rel m2 c2 ->
    comp_rel (comp_bind m1 m2) (comp_let c1 c2).
*)
Lemma let_compat_aux n : forall Γ MR t1 t2
      (m1 : denote_comp_type t1 Γ MR) (m2 : denote_comp_type t2 (t1 :: Γ) MR)
      (c1 : comp t1 Γ MR) (c2 : comp t2 (t1 :: Γ) MR),
    bounded_comp_rel n m1 c1 -> bounded_comp_rel n m2 c2 ->
    bounded_comp_rel n (comp_bind m1 m2) (comp_let c1 c2).
Proof.
  induction n as [ n' IHn' ] using (well_founded_induction lt_wf).
  intros ? ? ? ? ? ? ? ? Hmc1 Hmc2 n hyps ρ Hn' Hhρ.
  (* can I just make this inductive? *)
  constructor. intros j Hj. specialize (Hmc1 n hyps ρ Hn' Hhρ) as Hmc1n.
  inversion Hmc1n. subst. rename H into Happrox1.
  split.
  - intros vv2 Hvv2. unfold comp_bind in Hvv2.
    eapply multi_step_ret_bind_inv in Hvv2.
    destruct Hvv2 as [j1 [j2 [vv1 [Hn [Hvv11 Hvv12] ]]]].
    (* problem here, look into it tomorrow, might be introducing *)
    assert (Hj1 : j1 < n). lia.
    specialize (Happrox1 j1 Hj1). destruct Happrox1 as [Hretmc1 _].
    specialize (Hretmc1 vv1 Hvv11).
    destruct Hretmc1 as [v1 [Hv11 Hv12]].
    assert (Hhρ' : closing_subst_approx (n - j1) (t1 :: Γ) (vv1, hyps) (v1, ρ)).
    constructor; auto.
    destruct j1. assert (n - 0 = n). lia. rewrite H. auto.
    eapply lower_closing_subst_approx; eauto. lia.
    assert (Hnj1 : n - j1 <= n'). lia.
    specialize (Hmc2 (n - j1) (vv1, hyps) (v1, ρ) Hnj1 Hhρ') as Hmc2n.
    inversion Hmc2n. assert (Hj2 : j2 < n - j1). lia.
    specialize (H j2 Hj2). destruct H as [Hretmc2 _ ].
    specialize (Hretmc2 _ Hvv12). destruct Hretmc2 as [v2 [Hv21 Hv22]].
    exists v2. split.
    + (* need stepping metatheory, can be a focus next week *) admit.
    + assert (n - j = n - j1 - j2). lia. rewrite H. auto.
  - intros. rename H into Hcall.
    eapply multi_step_call_term_bind_inv in Hcall.
    destruct Hcall as [[j1 [j2 [vv1 [Hj12 [Hstep1 Hstep2]] ]]] |  [k1' [Hstep Hk1']] ].
    + assert (Hj1 : j1 < n). lia. specialize (Happrox1 j1 Hj1).
      destruct Happrox1 as [Hretmc1 _]. specialize (Hretmc1 _ Hstep1).
      destruct Hretmc1 as [v1 [Hstepv Happroxvv1]].
      assert (Hhρ' : closing_subst_approx (n - j1) (t1 :: Γ) (vv1, hyps) (v1, ρ)).
      constructor; auto.
      destruct j1. assert (n - 0 = n). lia. rewrite H. auto.
      eapply lower_closing_subst_approx; eauto. lia.
      assert (Hnj1 : n - j1 <= n'). lia.
      specialize (Hmc2 (n - j1) (vv1, hyps) (v1, ρ) Hnj1 Hhρ').
      inversion Hmc2. subst.  assert (Hj2 : j2 < n - j1). lia.
      specialize (H j2 Hj2). destruct H as [_ Hstuckmc2]. clear Hmc2.
      apply Hstuckmc2 in Hstep2.
      destruct Hstep2 as [vcall [E [c' [Hvcall [HE1 [HE2 HE3 ]] ]]] ].
      exists vcall, E, c'.
      split; [| split]; [| | split]; eauto.
      * assert (H : n - j1 - j2 = n - (j1 + j2)). lia. rewrite <- H.
        auto.
      * admit. (* stepping metatheory *)
      * intros. eapply HE3; eauto. lia.
    + specialize (Happrox1 j Hj). destruct Happrox1 as [_ Hstuckmc1].
      apply Hstuckmc1 in Hstep.
       destruct Hstep as [vcall [E [c' [Hvcall [HE1 [HE2 HE3 ]] ]]] ].
       exists vcall. eexists. eexists. (* comp_let c' c2 with proper closing*) 
       split; [ | split]; [| | split]; eauto.
       * admit. (* will require stepping metatheory *)
       * admit. (* should be trivial once I can formalize the eval context 
                  morally (ev_let E (close_comp Γ ρ c2)). but requires *)
       * intros. rewrite <- Hk1'. clear Hstuckmc1.
         assert (Hj'' : j'' < n'). lia.
         specialize (IHn' j'' Hj'' [] MR t1 t2 (fun _ => k1' vvret) (fun '(vv2,_) => m2 (vv2, hyps))).
         specialize (IHn' (subst_eval_context E (comp_ret vret))).
         unfold comp_bind in IHn'. admit.
         (* the choice of c2 requires an open substitution thing, but should be fine*)

         (* lots of details up in the air but this feels good *)
         (* let Γ = [], m2 := fun vv2 => m2 (vv2, hyps), which I have knowledge about at j''*)
         (* lets try to *)
         (* I have info about k1' vvret at j'' or lower *)
         (* I have infor about m2 at any level I have info about return of k1' vvret 
            which is at most j'' *)
         (* seems to fit with *)
 Admitted.


Lemma let_compat Γ MR t1 t2 
      (m1 : denote_comp_type t1 Γ MR) (m2 : denote_comp_type t2 (t1 :: Γ) MR)
      (c1 : comp t1 Γ MR) (c2 : comp t2 (t1 :: Γ) MR)
  : comp_rel m1 c1 -> comp_rel m2 c2 ->
    comp_rel (comp_bind m1 m2) (comp_let c1 c2).
Proof.
  intros. red. intros. eapply let_compat_aux; try red; eauto.
Qed.

Lemma mfix_compat t Γ R MR dbodies sbodies m (c : comp t Γ (R :: MR)):
  bodies_rel dbodies sbodies ->
  comp_rel m c ->
  comp_rel (interp_mrec_bodies dbodies m) (comp_mfix _ sbodies c).
Proof.
  intros Hbodies Hmc n hyps ρ Hhρ.
  constructor. intros. split.
  - intros vv Hvv. apply recursion_trace_ret in Hvv as Hvv'.
    destruct Hvv' as [l Hrec].
    specialize (Hmc n _ _ Hhρ).
    (**)
    unfold interp_mrec_bodies in Hvv.
    generalize dependent (m hyps). generalize dependent c.
    clear m.
    (*Hhρ is a little problematic, could get rid of it if I can commute close_comp with 
      comp_mfix *)
    (* will require a bind lemma *)
    induction j' as [ j IHj ] using (well_founded_induction lt_wf).
    intros c m Happrox Hstep Hrec. dependent destruction Hrec.
    + admit.
    + admit.
    +
    
    revert Happrox Hstep.
    dependent induction Hrec.
    + intros. setoid_rewrite H2 in Hstep. 
      inversion Happrox. subst. assert (0 < n). lia. specialize (H0 0 H1).
      destruct H0 as [Hret _].
      setoid_rewrite H2 in Hret. assert (r = vv). apply eqit_Ret_inv in H3. subst. auto.
      subst. specialize (Hret vv). 
      assert (multi_step (E := denote_mrec_ctx (denote_mfix_ctx (R :: MR))) 0 (ret vv) (ret vv)).
      constructor. reflexivity. specialize (Hret H0).
      destruct Hret as [v [Hv1 Hv2]]. exists v.
      split.
      * (*step metatheory*) admit.
      * destruct n0; auto. eapply lower_approx_val; try apply Hv2. lia.
    + exfalso. (* ret ≅ vis*) admit.
    +


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
