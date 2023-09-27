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
Require Export SmallStepSeqFacts.
Require Import Lia.
Require Import Coq.Classes.Morphisms.
Require Export ClosingSubst.
Require Export LogicalApprox.
Require Export RecursionTrace.
Require Export ApproxCompTerm.
From Paco Require Import paco.

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

Lemma weaken_r_value_nil_nil : forall t (v : value t []),
    weaken_r_value [] v = v.
Proof.
  intros. unfold weaken_r_value. rewrite val_map_id; auto.
  intros. inversion x.
Qed.

Lemma let_compat_aux n : forall Γ MR t1 t2
      (m1 : denote_comp_type t1 Γ MR) (m2 : denote_comp_type t2 (t1 :: Γ) MR)
      (c1 : comp t1 Γ MR) (c2 : comp t2 (t1 :: Γ) MR),
    bounded_comp_rel n m1 c1 -> bounded_comp_rel n m2 c2 ->
    bounded_comp_rel n (comp_bind m1 m2) (comp_let c1 c2).
Proof.
  induction n as [ n' IHn' ] using (well_founded_induction lt_wf).
  intros ? ? ? ? ? ? ? ? Hmc1 Hmc2 n hyps ρ Hn' Hhρ.
  constructor. intros j Hj. specialize (Hmc1 n hyps ρ Hn' Hhρ) as Hmc1n.
  inversion Hmc1n. subst. rename H into Happrox1.
  split.
  - intros vv2 Hvv2. unfold comp_bind in Hvv2.
    eapply multi_step_ret_bind_inv in Hvv2.
    destruct Hvv2 as [j1 [j2 [vv1 [Hn [Hvv11 Hvv12] ]]]].
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
    + rewrite close_comp_let. eapply eval_rel_stuck_let1; eauto.
      rewrite subst_comp_const_close. eauto.
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
      * rewrite close_comp_let. eapply eval_rel_stuck_let1; eauto.
        rewrite subst_comp_const_close. auto.
      * intros. eapply HE3; eauto. lia.
    + specialize (Happrox1 j Hj). destruct Happrox1 as [_ Hstuckmc1].
      apply Hstuckmc1 in Hstep.
       destruct Hstep as [vcall [E [c' [Hvcall [HE1 [HE2 HE3 ]] ]]] ].
       exists vcall. exists (ev_let E (close_comp_binder ρ c2) ). 
       exists (comp_let c' (close_comp_binder ρ c2)). 
       (* comp_let c' c2 with proper closing*) 
       split; [ | split]; [| | split]; eauto.
       * rewrite close_comp_let.
         eapply eval_rel_stuck_let2; eauto.
       * constructor. auto.
       * intros. rewrite <- Hk1'. clear Hstuckmc1.
         assert (Hj'' : j'' < n'). lia.
         specialize (IHn' j'' Hj'' [] MR t1 t2 (fun _ => k1' vvret) (fun '(vv2,_) => m2 (vv2, hyps))).
         specialize (IHn' (subst_eval_context E (comp_ret vret))).
         unfold comp_bind in IHn'. simp subst_eval_context. red in IHn'.
         erewrite <- close_comp_equation_1. 
         eapply IHn' with (hyps := tt) (ρ := tt).
         -- red. intros j''' [] [] Hj''' _. simp close_comp. eapply HE3.
            lia. inversion Hj'''. subst. auto. eapply lower_approx_val; try apply H0.
            lia.
         -- red. intros j''' [vv1 []] [v1 []] Hj''' Hvv1. 
            dependent destruction Hvv1.
            simp close_comp. rewrite <- close_comp_open. 
            eapply Hmc2. lia. constructor. rewrite weaken_r_value_nil_nil. auto.
            eapply lower_closing_subst_approx. eauto. lia.
         -- lia.
         -- constructor.
Qed.

Lemma let_approx n : forall MR t1 t2
      (m1 : mtree (denote_mfix_ctx MR) (denote_type t1)) (k2 : denote_type t1 -> mtree (denote_mfix_ctx MR) (denote_type t2))
      (c1 : comp t1 [] MR) (c2 : comp t2 [t1] MR),
    approx_comp n approx_val m1 c1 -> 
    (forall n0 vv1 v1, n0 <= n -> approx_val n0 t1 vv1 v1 -> approx_comp n0 approx_val (k2 vv1) (subst_comp_cons c2 v1)) ->
    approx_comp n approx_val (bind m1 k2) (comp_let c1 c2).
Proof.
  intros. specialize let_compat_aux with (Γ := []) as Hlet. 
  red in Hlet. specialize Hlet with (n := n) (j := n) (hyps := tt) (ρ := tt).
  specialize (Hlet MR t1 t2 (fun _ => m1) (fun '(x, _) => k2 x) c1 c2).
  unfold comp_bind in Hlet. simp close_comp in Hlet. apply Hlet; auto.
  red. intros j [] [] Hj _. simp close_comp. eapply lower_approx_comp'; try apply H. lia. 
  intros. eapply lower_approx_val; eauto.
  red. intros j [vv1 []] [v1 []] Hj Happrox. dependent destruction Happrox. 2 : constructor.
  simp close_comp. rewrite weaken_r_value_nil_nil. eapply H0; eauto.
Qed.

Lemma approx_comp_multi_step_minus:
  forall (t : vtype) (R : call_frame) (MR : mfix_ctx) (c' : comp t [] (R :: MR)) 
    (n : nat)
    m1 m2
    (n0 : nat),
    n < n0 ->
    approx_comp n0 approx_val m1 c' -> multi_step n m1 m2 -> approx_comp (n0 - n) approx_val m2 c'.
Proof.
  intros t R MR c' n m1 m2 n0.
  intros Hnn0 Happrox Hstep. inversion Happrox. subst.
  clear Happrox.
  rename H into Happrox.
  constructor. intros. split.
  - assert (Hj' : j' + n < n0). lia.
    specialize (Happrox _ Hj'). destruct Happrox as [Hret _].
    intros vv Hstep'. 
    assert (multi_step (n + j') m1 (ret vv)). eapply multi_step_add; eauto.
    rewrite PeanoNat.Nat.add_comm in H0. specialize (Hret vv H0).
    destruct Hret as [v [Hv1 Hv2]]. exists v.
    split; auto. eapply lower_approx_val'; try apply Hv2. lia.
 - assert (Hj' : j' + n < n0). lia.
    specialize (Happrox _ Hj'). destruct Happrox as [_ Hstuck].
    intros. 
    assert (multi_step (n + j') m1 (vv <- call_term x xR vvcall;; k vv)).
    eapply multi_step_add; eauto. rewrite PeanoNat.Nat.add_comm in H1.
    specialize (Hstuck _ _ _ _ _ _ _ H1).
    destruct Hstuck as [vcall [E [c'' [HE1 [HE2 [HE3 HE4]]]]]].
    exists vcall, E, c''. split; [ | split; [ | split]]; auto.
    eapply lower_approx_val'; try apply HE1. lia.
    intros. eapply HE4; eauto. lia.
Qed.

Lemma let_compat Γ MR t1 t2 
      (m1 : denote_comp_type t1 Γ MR) (m2 : denote_comp_type t2 (t1 :: Γ) MR)
      (c1 : comp t1 Γ MR) (c2 : comp t2 (t1 :: Γ) MR)
  : comp_rel m1 c1 -> comp_rel m2 c2 ->
    comp_rel (comp_bind m1 m2) (comp_let c1 c2).
Proof.
  intros. red. intros. eapply let_compat_aux; try red; eauto.
Qed.

(* replace eq with beta equivalence  *)
Lemma subst_eval_context__ctx n t1 MR1 t2 r (E : @eval_context t1 MR1 t2 MR1 r true) (c : comp t2 [] MR1) :
  approx_comp_term n (subst_eval_context E c) (comp_let c (subst_eval_context_ctx E (comp_ret (val_var VarZ)))).
Proof.
  generalize dependent c. dependent induction E.
  - intros. simp subst_eval_context. simp subst_eval_context_ctx. 
    apply approx_comp_term_let_ret_r.
  - intros c2. simp subst_eval_context. simp subst_eval_context_ctx. 
    eapply approx_comp_term_trans. eapply approx_comp_term_let_cong. eauto. intros. apply approx_comp_term_refl.
    eapply approx_comp_term_let_assoc.
Qed.

Lemma subst_eval_context__ctx' n t1 MR1 t2 r (E : @eval_context t1 MR1 t2 MR1 r true) (c : comp t2 [] MR1) :
  approx_comp_term n (comp_let c (subst_eval_context_ctx E (comp_ret (val_var VarZ)))) (subst_eval_context E c).
Proof.
  generalize dependent c. dependent induction E.
  - intros. simp subst_eval_context. simp subst_eval_context_ctx. 
    apply approx_comp_term_let_ret_r'.
  - intros c2. simp subst_eval_context. simp subst_eval_context_ctx. 
    eapply approx_comp_term_trans. 2 : eapply approx_comp_term_let_cong; eauto.
    2 : intros; try apply approx_comp_term_refl.
    apply approx_comp_term_let_assoc'.
Qed.


(* TODO: this is currently unsound, relying on an equality when I need a seperate equivalence relation 
   that is proper wrt approx_comp *)
Lemma approx_comp_eval_context t1 MR1 t2 r (E : @eval_context t1 MR1 t2 MR1 r true)
      (c : comp t2 [] MR1) m k n1 n2:
  n1 < n2 ->
         approx_comp n1 approx_val m c -> 
  (forall n3 (vv2 : denote_type t2) (v2 : closed_value t2),
      n3 < n2 -> approx_val n3 t2 vv2 v2 ->
      approx_comp n3 approx_val (k vv2) (subst_eval_context E (comp_ret v2))) ->
  approx_comp n1 approx_val (bind m k) (subst_eval_context E c).
Proof.
  intros Hn12 Hmc HkE. eapply approx_comp_approx_comp_term.
  eapply subst_eval_context__ctx'.

  (* might have done some of this in the wrong direction *)
  eapply let_approx; eauto.
  intros. eapply HkE in H0. 2 : lia.
  enough ( (subst_comp_cons (SmallStepSeq.subst_eval_context_ctx E (comp_ret (val_var VarZ))) v1) 
           = (subst_eval_context E (comp_ret v1))).
  rewrite H1. auto.
  clear. dependent induction E.
  - simp subst_eval_context_ctx. unfold subst_comp_cons. simp subst_comp. simp subst_var.
    simp subst_eval_context. auto.
  - simp subst_eval_context_ctx. unfold subst_comp_cons. simp subst_comp.
    unfold subst_comp_cons in IHE. rewrite IHE; auto. simp subst_eval_context.
    f_equal. destruct subst_weaken_mid_aux as [? _]. erewrite <- H with (Γ := [t1]); eauto.
    Unshelve. all : eauto. f_equal. unfold weaken_r_comp, weaken_mid_comp.
    eapply comp_map_dep_f_equal; eauto. red. intros.
    cbn in b. dependent destruction b.
    2 : inversion b1. unfold weaken_var_r. simp append_var. simp weaken_var_mid. auto.
Qed.


Lemma approx_comp_log_rel_bodies_step:
  forall (R1 R2 : call_frame) (MR : mfix_ctx) (sbodies : mfix_bodies [] MR R1 R2)
    (dbodies : forall arg : denote_call_frame R2, mtree (denote_mfix_ctx (R1 :: MR)) (encodes arg)) (tin tout : vtype)
    (x : var (tin, tout) R2) (vvin : denote_type tin) (n : nat) (vcall : closed_value tin),
    log_rel_bodies_step n dbodies sbodies ->
    approx_val n tin vvin vcall ->
    approx_comp (n - 1) approx_val (apply_bodies dbodies x vvin) (subst_comp_cons (nth_body sbodies x) vcall).
Proof.
  intros R1 R2 MR sbodies dbodies tin tout x vvin n vcall.
  intros Hbodies Hin. destruct n. constructor. intros. lia.
  dependent induction x.
  - dependent destruction sbodies. simp nth_body. unfold apply_bodies.
    simp call_mrec_call_frame. setoid_rewrite bind_ret_r.
    simp log_rel_bodies_step in Hbodies. destruct Hbodies as [Hbody _].
    simp approx_val in Hbody.
    specialize (Hbody vvin vcall (S n - 1)).
    assert (Hn1 : S n - 1 < S n). lia.
    assert (Hn2 : approx_val (S n - 1) tin vvin vcall). eapply lower_approx_val; try apply Hin. lia.
    specialize (Hbody Hn1 Hn2). clear - Hbody. revert Hbody.  
    eapply lower_approx_comp_aux1 with (P := fun n0 => n0 < S n). lia.
    intros. lia. intros. split; auto.
  - dependent destruction sbodies. 
    simp nth_body. simp log_rel_bodies_step in Hbodies.
    destruct Hbodies as [_ Hbodies].
    assert (apply_bodies dbodies (VarS x) vvin ≅ apply_bodies (fun x : denote_call_frame l => dbodies (inr x)) x vvin).
    unfold apply_bodies. simp call_mrec_call_frame. destruct (call_mrec_call_frame x vvin). reflexivity.
    rewrite H. eapply IHx; eauto.
Qed.

Lemma call_term_bind_inv_aux1  : 
 forall (MR : mfix_ctx)
    (R0 : call_frame) (tin0 tout0 : vtype) (x0 : var (tin0, tout0) R0) (xR0 : var R0 MR)
    (vvin : denote_type tin0)
    (tin tout : vtype) (Rcall : call_frame)
    (xR : var Rcall MR) (x : var (tin, tout) Rcall) (vvcall : denote_type tin),
   projT1 (call_mrec x xR vvcall) = projT1 (call_mrec x0 xR0 vvin) ->
   var_eq xR xR0.
Proof.
  intros. generalize dependent xR0.
  dependent induction xR.
  - simp call_mrec. intros.
    dependent destruction xR0. constructor. simp call_mrec in H.
    destruct (call_mrec_call_frame x vvcall). destruct (call_mrec x0 xR0 vvin).
    discriminate.
  - intros. dependent destruction xR0.
    + simp call_mrec in H. destruct (call_mrec x xR vvcall). 
      destruct (call_mrec_call_frame x0 vvin). discriminate.
    + constructor. eapply IHxR with (x := x) (vvcall := vvcall).
      simp call_mrec in H.
      destruct (call_mrec x xR vvcall). destruct (call_mrec x0 xR0 vvin).
      injection H. intros. subst. auto.
Qed.

Lemma call_term_bind_inv_aux2 : 
 forall (MR : mfix_ctx)
    
    (tin tout : vtype) (Rcall : call_frame)
    (tin0 tout0 : vtype) (x0 : var (tin0, tout0) Rcall)
    (xR : var Rcall MR) (x : var (tin, tout) Rcall) (vvcall : denote_type tin) 
    (vvin : denote_type tin0),
   projT1 (call_mrec x xR vvcall) = projT1 (call_mrec x0 xR vvin) ->
   (var_eq x x0 * (vvin ~= vvcall))%type.
Proof.
  intros. generalize dependent x0. generalize dependent x.
  dependent induction xR.
  - intros. simp call_mrec in H.
    assert (projT1 (call_mrec_call_frame x vvcall) = projT1 (call_mrec_call_frame x0 vvin)).
    destruct (call_mrec_call_frame x vvcall). destruct (call_mrec_call_frame x0 vvin).
    injection H. intros. auto. clear H.
    generalize dependent x0. dependent induction x.
    + simp call_mrec_call_frame. intros.
      dependent destruction x0. simp call_mrec_call_frame in H0. injection H0.
      intros. subst. split; constructor. exfalso.
      simp call_mrec_call_frame in H0. destruct (call_mrec_call_frame x0 vvin).
      discriminate.
    + intros.
      dependent destruction x0.
      * simp call_mrec_call_frame in H0. destruct (call_mrec_call_frame x vvcall).
        discriminate.
      * destruct b. simp call_mrec_call_frame in H0.
        enough (var_eq x x0 * (vvin ~= vvcall)). destruct X. split; auto.
        constructor. auto.
        eapply IHx; eauto. 
        destruct (call_mrec_call_frame x vvcall).
        destruct (call_mrec_call_frame x0 vvin). injection H0. auto.
  - intros. eapply IHxR. simp call_mrec in H.
    destruct (call_mrec x xR vvcall).
    destruct (call_mrec x0 xR vvin). injection H. intros. subst.
    auto.
Qed.


Lemma call_term_bind_inv1:
  forall (t : vtype) (MR : mfix_ctx)
    (R0 : call_frame) (tin0 tout0 : vtype) (x0 : var (tin0, tout0) R0) (xR0 : var R0 MR)
    (vvin : denote_type tin0)
    (k1 : denote_type tout0 -> mtree (denote_mfix_ctx (MR)) (denote_type t)) 
    (tin tout : vtype) (Rcall : call_frame)
    (xR : var Rcall MR) (x : var (tin, tout) Rcall) (vvcall : denote_type tin)
    (k' : denote_type tout -> mtree (denote_mfix_ctx (MR)) (denote_type t)) b1 b2,
    eqit eq b1 b2 (vv <- call_term x xR vvcall;; (k' vv)) (vv <- call_term x0 xR0 vvin;; (k1 vv)) ->
    tin = tin0 /\ tout = tout0 /\ x ~= x0 /\ xR ~= xR0 /\ Rcall = R0 /\ vvcall ~= vvin.
Proof.
  intros t MR R0 tin0 tout0 x0 xR0 vvin k1 tin tout Rcall xR x vvcall k'.
  unfold call_term. destruct (call_mrec x xR vvcall) eqn : Heq1.
  destruct (call_mrec x0 xR0 vvin) eqn : Heq2. setoid_rewrite bind_trigger.
  setoid_rewrite bind_vis. 
  intros. assert (x1 = x2). pinversion H. auto. subst.
  specialize (eqit_Vis_inv _ _ _ _ _ _ H) as H'. setoid_rewrite bind_ret_l in H'.
  clear H H'. 
  assert (var_eq xR xR0).
  { eapply call_term_bind_inv_aux1. rewrite Heq1, Heq2. auto. }
  apply var_eq_surj in X as ?. subst. apply var_eq_eq in X. subst.
  assert ((var_eq x x0 * (vvin ~= vvcall))%type).
  eapply call_term_bind_inv_aux2. rewrite Heq1, Heq2. auto.
  destruct X as [Heq HJMeq]. apply var_eq_surj in Heq as ?. injection X.
  intros. subst. rewrite HJMeq. apply var_eq_eq in Heq.  subst.
  repeat split; auto.
Qed.

Lemma call_term_bind_inv_JMeq_aux :
forall (t : vtype) (MR : mfix_ctx) A B
  (k1 k2 : B -> mtree (denote_mfix_ctx MR) (denote_type t))
  (d : A -> B)
  (x0 : B) b1 b2 ,
  (forall x , eqit eq b1 b2 (k1 (d x)) (k2 (d x))) ->
  d ~= @id B -> A = B -> eqit eq b1 b2 (k1 x0)  (k2 x0).
Proof.
  intros. subst. rewrite H0 in H. unfold id in *. auto.
Qed.

Lemma call_term_bind_inv2:
  forall (t : vtype) (MR : mfix_ctx)
    (tin tout : vtype) (Rcall : call_frame)
    (xR : var Rcall MR) (x : var (tin, tout) Rcall) (vvcall : denote_type tin)
    (k1 k2 : denote_type tout -> mtree (denote_mfix_ctx MR) (denote_type t)) b1 b2,
    eqit eq b1 b2 (vv <- call_term x xR vvcall;; (k1 vv))  (vv <- call_term x xR vvcall;; (k2 vv)) ->
    forall x, eqit eq b1 b2 (k1 x) (k2 x).
Proof.
  unfold call_term. intros. destruct (call_mrec x xR vvcall) eqn : Heq1.
  setoid_rewrite bind_trigger in H. setoid_rewrite bind_vis in H.
   specialize (call_mrec_encodes _ _ _ _ x xR vvcall) as Henc.
  specialize (call_mrec_cont _ _ _ _ x xR vvcall) as Hcont.
  rewrite Heq1 in Hcont. cbn in Hcont. rewrite Heq1 in Henc. cbn in Henc.
  assert (forall x, eqit eq b1 b2 (k1 (d x)) (k2 (d x))). intros. eapply eqit_Vis_inv in H.
  setoid_rewrite bind_ret_l in H. eauto. eapply call_term_bind_inv_JMeq_aux; eauto.
Qed.
 
(*
Lemma mfix_compat t Γ R MR dbodies sbodies m (c : comp t Γ (R :: MR)):
  bodies_rel dbodies sbodies ->
  comp_rel m c ->
  comp_rel (interp_mrec_bodies dbodies m) (comp_mfix _ sbodies c).

*)

(* use the trick from bind_compat to get a useful inductive hypothesis *)
Lemma mfix_compat_aux n : forall t Γ R MR dbodies sbodies m (c : comp t Γ (R :: MR)),
  bounded_bodies_rel n dbodies sbodies ->
  bounded_comp_rel n m c ->
  bounded_comp_rel n (interp_mrec_bodies dbodies m) (comp_mfix _ sbodies c).
Proof.
  induction n as [n00 IHn] using (well_founded_induction lt_wf).
  intros t Γ R MR dbodies sbodies m c Hbodies Hmc n hyps ρ Hnn Hhρ. 
  constructor. intros. split.
  - intros vv Hvv. apply recursion_trace_den_ret in Hvv as Hvv'.
    destruct Hvv' as [l Hrec].
    red in Hmc.
    specialize (Hmc n hyps ρ Hnn Hhρ).
    (**)
    unfold interp_mrec_bodies in Hvv. rewrite close_comp_mfix. red in Hbodies.
    specialize (Hbodies n hyps ρ Hnn Hhρ).
    remember (close_comp Γ ρ c) as c'. remember (close_bodies Γ ρ sbodies) as sbodies'.
    remember (dbodies hyps) as dbodies'. remember (m hyps) as m'.
    clear Heqsbodies' Heqdbodies' Heqc' Heqm'. clear m sbodies c dbodies.
    clear Hvv Hhρ ρ hyps Γ. revert Hmc. generalize dependent c'.
    remember (ret vv) as x. revert Heqx. generalize dependent n. induction Hrec; intros.
    (* now I am back to feeling confident this is the correct relation,
       but I suspect I am not at the exact correct generality 
     *)
    + subst. apply eqit_Ret_inv in H. subst.
      rewrite H0 in Hmc. inversion Hmc. subst.
      assert (H00 : 0 < n0). lia.
      specialize (H _ H00). destruct H as [Hret _].
      assert (multi_step (E := denote_mrec_ctx (denote_mfix_ctx (R :: MR))) 0 (ret r) (ret r)).
      constructor. reflexivity. specialize (Hret _ H).
      destruct Hret as [v [Hv1 Hv2]].
      exists v. split.
      * apply eval_rel_stuck_mfix_ret; auto.
      * eapply lower_approx_val'; try apply Hv2. lia.
    + exfalso. subst. clear - H. unfold call_term in H.
      destruct (call_mrec x xR vvin). setoid_rewrite bind_trigger in H.
      setoid_rewrite bind_vis in H. pinversion H.
    + subst. rewrite H in Hmc. specialize (IHHrec (n0 - 1)). 
      assert (Hbodiesn0 : log_rel_bodies_step (n0 - 1) dbodies' sbodies').
      eapply lower_log_rel_bodies_step; try apply Hbodies. lia.
      assert (Hn0 : n < n0 - 1). lia.
      assert (Hn00 : n0 - 1 <= n00). lia.
      specialize (IHHrec Hbodiesn0 Hn00 Hn0 eq_refl).
      inversion Hmc. subst. assert (H00 : 0 < n0). lia.
      specialize (H1 0 H00). destruct H1 as [_ Hstuck].
      assert (H2 : multi_step 0 (vv <- call_term x VarZ vvin;; k1 vv) (vv <- call_term x VarZ vvin;; k1 vv)).
      constructor. reflexivity. specialize (Hstuck _ _ _ _ _ _ _ H2).
      destruct Hstuck as [vcall [E [c'' [HE1 [HE2 [HE3 HE4 ]]]]]].
      set (subst_eval_context E (subst_comp_cons (nth_body sbodies' x) vcall)) as c'''.
      specialize (IHHrec c''').
      assert (approx_comp (n0 - 1) approx_val (x <- apply_bodies dbodies' x vvin;; k1 x) c''').
      {
        unfold c'''.
        eapply approx_comp_eval_context; eauto.
        - eapply  approx_comp_log_rel_bodies_step; eauto.
          eapply lower_approx_val'; try apply HE1. lia.
        - intros. apply HE4; auto. lia.
      }
      specialize (IHHrec H1). destruct IHHrec as [v [Hv1 Hv2]].
      exists v. split.
      * eapply eval_rel_stuck_mfix_stuck_call_VarZ; eauto. 
      * eapply lower_approx_val'; try apply Hv2. lia.
    + intros. subst. specialize (IHHrec (n0 - n)).
      assert (Hmn0 : m < n0 - n). lia.
      assert (Hbodiesn0 : log_rel_bodies_step (n0 - n) dbodies' sbodies').
      eapply lower_log_rel_bodies_step'; try apply Hbodies. lia.
      assert (Hnn0 : n0 - n <= n00). lia.
      specialize (IHHrec Hbodiesn0 Hnn0 Hmn0 eq_refl). specialize (IHHrec c').
      match type of IHHrec with | ?P1 -> ?P2 => enough P1 end.
      specialize (IHHrec H1). destruct IHHrec as [v [Hv1 Hv2]].
      eexists. split; eauto. eapply lower_approx_val'; try apply Hv2.
      lia. eapply approx_comp_multi_step_minus; eauto. lia.
  - intros ? ? ? ? ? ? ? Hstep. unfold interp_mrec_bodies in *.
    setoid_rewrite close_comp_mfix. 
    eapply multi_step_interp_mrec_den_vis_inv in Hstep as Hk'.
    destruct Hk' as [k' Hk']. setoid_rewrite Hk' in Hstep.
    setoid_rewrite Hk'. clear Hk' k. red in Hmc.
    specialize (Hmc n hyps ρ Hnn Hhρ).
    specialize (Hbodies n _ _ Hnn Hhρ).
    remember (close_comp Γ ρ c) as c'. remember (close_bodies Γ ρ sbodies) as sbodies'.
    remember (dbodies hyps) as dbodies'. remember (m hyps) as m'.
    eapply recursion_trace_den_vis in Hstep. destruct Hstep as [l Hrec].
    clear Heqsbodies' Heqdbodies' Heqc' Heqm'. clear m sbodies c dbodies.
    clear Hhρ ρ hyps Γ.  generalize dependent c'. generalize dependent n.
    dependent induction Hrec; intros.
    + clear - H. exfalso. unfold call_term in H.
      destruct (call_mrec x xR vvcall). setoid_rewrite bind_trigger in H.
      setoid_rewrite bind_vis in H. pinversion H.
    + intros. setoid_rewrite H0 in Hmc. 
      eapply call_term_bind_inv1 in H as H1'. destruct H1' as [? [? [? [? [? ?]]]]]. 
      subst. subst. 
      assert (forall x, interp_mrec dbodies' (k' x) ≅ interp_mrec dbodies' (k1 x)).
      eapply call_term_bind_inv2; eauto.
      inversion Hmc. subst. assert (H00 : 0 < n0). lia.
      specialize (H3 0 H00). destruct H3 as [_ Hstuck].
      specialize (Hstuck tin0 tout0 _ (VarS xR0) x0 vvin k1).
      assert (multi_step 0 (vv <- call_term x0 (VarS xR0) vvin;; k1 vv)
             (vv <- call_term x0 (VarS xR0) vvin;; k1 vv)). constructor. reflexivity.
      specialize (Hstuck H3).
      destruct Hstuck as [vcall [E [c'' [HE1 [HE2 [HE3 HE4]]]]]].
      specialize stuck_call_push_eval_context_mfix. intros HE'. 
      specialize (HE' _ _ _ _ sbodies' _ _ _ _ _ E).
      destruct HE' as [E' [HE'1 HE'2]].
      (* need more properties of E' *)
      exists vcall. 
      exists E'.
      exists (push_eval_context _ E (comp_mfix_map sbodies') (comp_call xR0 x0 vcall)).
      split; [ | split; [ | split]].
      * eapply lower_approx_val'; try apply HE1. lia.
      * eapply eval_rel_stuck_mfix_stuck_call_neq_VarZ; eauto.
        eapply eval_rel_stuck_stuck; eauto.
      * eauto.
      * intros. setoid_rewrite H2.
        eapply approx_comp_approx_comp_term; eauto.
        assert (Hj'' : j'' < n00). lia.
        specialize (IHn j'' Hj'' t [] R MR (fun _ => dbodies') sbodies'). 
        specialize (IHn (fun _ => (k1 vvret)) (subst_eval_context E (comp_ret vret))).
        assert (bounded_bodies_rel j'' (fun _ : denote_ctx [] => dbodies') sbodies').
        red. intros j [] [] ? ?. simp close_bodies. 
        eapply lower_log_rel_bodies_step'; try apply Hbodies. lia.
        specialize (IHn H6).
        match type of IHn with | ?P1 -> ?P2 => assert P1 end.
        red. intros j [] [] ? ?. simp close_comp.
        eapply lower_approx_comp'; try apply HE4; eauto. 
        intros.
        eapply lower_approx_val; eauto. lia.
        specialize (IHn H7). red in IHn. 
        specialize (IHn j'' tt tt (le_n _) (closing_subst_approx_nil _)).
        simp close_comp in IHn.
    + subst. rewrite H in Hmc. 
      specialize (IHHrec IHn). specialize (IHHrec _ _ _ xR x vvcall k').
      assert (H00 : vv <- call_term x xR vvcall;; interp_mrec dbodies' (k' vv) =
           vv <- call_term x xR vvcall;; interp_mrec dbodies' (k' vv)).
      reflexivity.
      specialize (IHHrec H00). 
      inversion Hmc. subst. specialize (H1 0). 
      clear H00. assert (H00 : 0 < n0). lia.
      specialize (H1 H00). destruct H1 as [_ Hstuck].
      assert (Hstep0 : multi_step 0 (vv <- call_term x0 VarZ vvin;; k1 vv) 
                                  (vv <- call_term x0 VarZ vvin;; k1 vv)).
      constructor. reflexivity.
      apply Hstuck in Hstep0. clear Hstuck.
      destruct Hstep0 as [vcall [E [c'' [HE1 [HE2 [HE3 HE4]]]]]].
      set (subst_eval_context E (subst_comp_cons (nth_body sbodies' x0) vcall)) as c'''.
      assert (Hbodiesn0 : log_rel_bodies_step (n0 - 1) dbodies' sbodies').
      eapply lower_log_rel_bodies_step; try apply Hbodies. lia.
      assert (Hn0 : n < n0 - 1). lia.
      assert (Hnn0 : n0 - 1 <= n00). lia.
      specialize (IHHrec _ Hbodiesn0 Hnn0 Hn0 c''').
      assert (approx_comp (n0 - 1) approx_val (x <- apply_bodies dbodies' x0 vvin;; k1 x) c''').
      {
        unfold c'''. 
        eapply approx_comp_eval_context; eauto.
        - eapply approx_comp_log_rel_bodies_step; eauto.
          eapply lower_approx_val'; try apply HE1. lia.
        - intros. eapply HE4. lia. auto.
      }
      specialize (IHHrec H1).
      destruct IHHrec as [vcall' [E' [c'''' [HE'1 [HE'2 [HE'3 HE'4]]]]]].
      unfold c''' in *. exists vcall', E', c''''.
      split; [ | split; [ | split]].
      * eapply lower_approx_val'; try apply HE'1. lia.
      * eapply eval_rel_stuck_mfix_stuck_call_VarZ; eauto.
      * auto.
      * intros. eapply HE'4; eauto. lia.
    + specialize (IHHrec IHn _ _ _ _ _ _ _ eq_refl). 
      specialize (IHHrec (n0 - n)).
      assert (Hmn0 : m < n0 - n). lia.
      assert (Hnn0 : n0 - n <= n00). lia.
      assert (Hbodiesn0 : log_rel_bodies_step (n0 - n) dbodies' sbodies').
      eapply lower_log_rel_bodies_step'; try apply Hbodies. lia.
      specialize (IHHrec Hbodiesn0 Hnn0 Hmn0 c').
      assert (Happrox : approx_comp (n0 - n) approx_val t2 c').
      eapply approx_comp_multi_step_minus; eauto. lia.
      specialize (IHHrec Happrox).
      destruct IHHrec as [vcall [E [c'' [HE1 [HE2 [HE3 HE4]]]]]].
      exists vcall, E, c''.
      split; [ | split; [ | split]]; eauto.
      * eapply lower_approx_val'; try apply HE1. lia.
      * intros. eapply HE4; eauto. lia.
Qed.

Lemma mfix_compat t Γ R MR dbodies sbodies m (c : comp t Γ (R :: MR)):
  bodies_rel dbodies sbodies ->
  comp_rel m c ->
  comp_rel (interp_mrec_bodies dbodies m) (comp_mfix _ sbodies c).
Proof.
  intros. red. intros. eapply mfix_compat_aux; eauto.
  all : red; intros; eauto.
Qed.

Lemma call_compat tin tout Γ R MR m (vin : value tin Γ) 
      (xR : var R MR) (x : var (tin, tout) R) :
  val_rel m vin ->
  comp_rel (fun hyps => vvin <- m hyps;; call_term x xR vvin) (comp_call xR x vin).
Proof.
  intros Hval. red. intros.
  apply Hval in H as Hval'. destruct Hval' as [vvin [Hvvin1 Hvvin2]].
  setoid_rewrite Hvvin1. setoid_rewrite bind_ret_l.
  constructor. intros.
  split.
  - intros. exfalso. apply multi_step_eutt in H1. unfold call_term in H1.
    destruct (call_mrec x xR vvin). setoid_rewrite bind_vis in H1. pinversion H1.
  - intros. apply multi_step_eutt in H1 as H1'.
    setoid_rewrite <- bind_ret_r with (s := call_term x xR vvin) in H1'.
    apply call_term_bind_inv1 in H1' as H2. decompose record H2. subst. subst. clear H2.
    clear H1'. dependent destruction H1.
    2 : { dependent destruction H3. unfold call_term in H2. 
          destruct (call_mrec x0 xR0 vvcall). setoid_rewrite bind_vis in H2.
          pinversion H2. inversion CHECK. }
    setoid_rewrite <- bind_ret_r with (s := call_term x0 xR0 vvcall) in H1 at 1.
    assert (forall x, k x ≅ ret x). intros. symmetry. eapply call_term_bind_inv2;  eauto.
    setoid_rewrite H2. exists (close_value Γ ρ vin), ev_hole, (comp_call xR0 x0 (close_value Γ ρ vin)).
    split; [ | split; [ | split]].
    + eapply lower_approx_val'; try apply Hvvin2. lia.
    + rewrite close_comp_call.
      eapply eval_rel_stuck_stuck. constructor.
    + constructor.
    + intros. simp subst_eval_context. constructor.
      intros. split.
      * intros. apply multi_step_eutt in H6.
        apply eqit_Ret_inv in H6. subst. exists vret.
        split. apply eval_rel_stuck_val. unfold step. simp observe. auto.
        eapply lower_approx_val'; try apply H4. lia.
      * intros. exfalso. clear - H6. apply multi_step_eutt in H6.
        unfold call_term in H6. destruct (call_mrec x xR vvcall0).
        setoid_rewrite bind_trigger in H6. setoid_rewrite bind_vis in H6.
        pinversion H6.
Qed.

(* note that you added this tau during the application, will need to be added to the
   denotation *)
Lemma app_compat t1 t2 Γ MR mf marg (vf : value (Arrow t1 MR t2) Γ)
      (varg : value t1 Γ) : 
  val_rel mf vf ->
  val_rel marg varg ->
  comp_rel (fun hyps => vvf <- mf hyps;; vvarg <- marg hyps;; Tau (vvf vvarg)) 
           (comp_app vf varg).
Proof.
  intros Hf Harg. intros n hyps ρ Hhρ.
  specialize (Hf n _ _ Hhρ). specialize (Harg n _ _ Hhρ).
  destruct Hf as [vvf [Hvvf1 Hvvf2]].
  destruct Harg as [vvarg [Hvvarg1 Hvvarg2]].
  rewrite Hvvf1. setoid_rewrite bind_ret_l.
  rewrite Hvvarg1. setoid_rewrite bind_ret_l.
  destruct n. constructor. intros. lia.
  rewrite close_comp_comp_app.
  remember (close_value Γ ρ vf) as vf'. clear Heqvf' vf.
  remember (close_value Γ ρ varg) as varg'. clear Heqvarg' varg.
  dependent destruction vf'; try inversion x.
  simp approx_val in Hvvf2.
  eapply approx_comp_multi_step_1. econstructor.
  constructor. reflexivity. constructor. reflexivity.
  eapply approx_comp_approx_comp_term; try apply approx_comp_term_comp_call.
  eapply lower_approx_comp_aux1 with (P := fun m' => m' < S n); try eapply Hvvf2; try lia.
  2 : eapply lower_approx_val; try apply Hvvarg2; try lia.
  intros. split; auto.
Qed.

Lemma abs_compat t1 t2 MR MR' Γ m (cbody : comp t2 (t1 :: Γ) MR) :
  comp_rel m cbody ->
  val_rel (MR := MR') (fun hyps => ret (fun x => m (x, hyps))) (val_abs cbody).
Proof.
  intros. econstructor. split. reflexivity.
  rewrite close_value_abs. destruct n; simp approx_val; auto.
  intros. specialize (H m' (vv,hyps) (v,ρ)). 
  assert (Hhρ' : closing_subst_approx m' (t1 :: Γ) (vv, hyps) (v, ρ)).
  constructor. auto. eapply lower_closing_subst_approx; eauto.
  specialize (H Hhρ'). rewrite <- close_comp_open.
  eapply lower_approx_comp_aux1 with (P := fun m' => m' < S n); try lia; eauto.
  split; intros; auto.
Qed.

Lemma const_compat MR Γ (n : nat) :
  val_rel (MR := MR) (fun hyps : denote_ctx Γ => ret n) (val_const n).
Proof.
  econstructor. split. reflexivity. rewrite close_value_const. 
  destruct n0; simp approx_val; auto.
Qed.

Lemma var_compat MR Γ t (x : var t Γ) :
  val_rel (MR := MR) (fun hyps : denote_ctx Γ => ret (index_ctx x hyps)) (val_var x).
Proof.
  red. intros. eexists. split. reflexivity.
  generalize dependent Γ. intros Γ x. dependent induction x.
  - intros [vv hyps] [v ρ] H. dependent destruction H. simp index_ctx. simp close_value.
    unfold subst_value_cons. simp subst_comp. simp subst_var.
    assert (close_value l ρ (weaken_r_value l v) = v).
    { (* this contains a few things that could be lifted out as lemmas *)
      generalize dependent l. clear H. intros Γ. revert v.
      induction Γ.
      - intros. simp close_value. unfold weaken_r_value. rewrite val_map_id; auto.
        intros. inversion x.
      - intros v [vv' hyps] [v' ρ] H. dependent destruction H.
        eapply IHΓ with (v := v)in H0. simp close_value.
        generalize dependent ρ. induction Γ.
        + intros []. simp close_value. intros. unfold subst_value_cons. 
          rewrite subst_value_weaken_r. auto.
        + intros [v'' ρ] H'. simp close_value in H'.
          simp close_value. rewrite <- H' at 2. f_equal.
          f_equal.
          destruct subst_weaken_mid_aux as [_ [Hmid _]].
          erewrite <- Hmid with (v1' := weaken_r_value (a1 :: Γ) v) (t2 := a0) (v2 := (weaken_r_value (a1 :: Γ) v')); eauto.
          unfold subst_value_cons. f_equal. unfold weaken_r_value, weaken_mid_value.
          rewrite val_map_fusion. eapply val_map_dep_f_equal; auto.
          red. intros. inversion b.
    }
    rewrite H1. auto.
  - intros [vv hyps] [v ρ] H. dependent destruction H. simp index_ctx. simp close_value.
    unfold subst_value_cons. simp subst_comp. simp subst_var. apply IHx in H0.
    destruct l. inversion x.
    simp subst_var.
Qed.
