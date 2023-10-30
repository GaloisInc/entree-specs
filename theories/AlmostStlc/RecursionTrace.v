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
Require Export EnTreeStep.
Section RecursionTrace.

Context (D E : Type) `{EncodedType D} `{EncodedType E}.
Context (bodies : forall (d : D), entree (D + E) (encodes d)).


Inductive recursion_trace {A : Type} :
  nat -> entree (D + E) A -> list D -> entree E A -> Prop := 
  | recursion_trace_ret_in t r n t' : t' ≅ (ret r) -> t ≅ ret r -> recursion_trace n t [] t'
  | recursion_trace_inr_in t (e : E) k n t' :
    t' ≅ (Vis e (fun x => interp_mrec bodies (k x))) ->
    t ≅ (Vis (inr e) k) -> recursion_trace n t [] t'
  | recursion_trace_inl_in t1 (d : D) k1 t2 m l : 
    t1 ≅ (Vis (inl d) k1) ->
    recursion_trace m (bind (bodies d) k1) l t2 ->
    recursion_trace (S m) t1 (d :: l) t2
  | recursion_trace_multi_step n m t1 t2 t3 l :
    multi_step n t1 t2 ->
    recursion_trace m t2 l t3 ->
    recursion_trace (n + m) t1 l t3.

Lemma recursion_trace_len A n t1 d t2 : 
  recursion_trace (A := A) n t1 d t2 -> n >= length d.
Proof.
  intros Hrec. induction Hrec; cbn; lia.
Qed.

Instance recursion_trace_eq_itree A : Proper (eq ==> eq_itree eq ==> eq ==> eq_itree eq ==> Basics.flip Basics.impl) (@recursion_trace A).
Proof.
  repeat intro. subst. 
  generalize dependent x0. generalize dependent x2. induction H5; intros.
  - eapply recursion_trace_ret_in; eauto. rewrite H4. eauto. rewrite H3. auto.
  - eapply recursion_trace_inr_in. rewrite H4. eauto. rewrite H3. auto.
  - econstructor; eauto. rewrite H2. eauto. eapply IHrecursion_trace; eauto.
    reflexivity.
  - econstructor; eauto. 2 : eapply IHrecursion_trace; eauto; try reflexivity.
    rewrite H2. auto.
Qed.


Lemma recursion_trace_ret R (t : entree (D + E) R) r n :
  multi_step n (interp_mrec bodies t) (ret r) ->
  exists d, recursion_trace n t d (ret r).
Proof.
  intros Hstep.
  remember (interp_mrec bodies t) as x.
  assert (x ≅ interp_mrec bodies t). subst. reflexivity.
  clear Heqx. rename H1 into Heqx.
  remember (ret r) as y.
  assert (y ≅ ret r). subst. reflexivity.
  clear Heqy. rename H1 into Heqy. generalize dependent t.
  generalize dependent r. induction Hstep; intros.
  - setoid_rewrite Heqy. exists [].
    destruct (eq_itree_case t) as [ | [ | ]].
    + destruct H2 as [r' Hr']. rewrite Hr' in Heqx. rewrite interp_mrec_ret in Heqx.
      rewrite H1 in Heqx. rewrite Heqy in Heqx.
      apply eqit_Ret_inv in Heqx. subst. rewrite Hr'. econstructor; reflexivity. 
    + destruct H2 as [t'' Ht'']. rewrite Ht'' in Heqx.
      rewrite interp_mrec_tau in Heqx. rewrite H1, Heqy in Heqx.
      pinversion Heqx; inversion CHECK.
    + destruct H2 as [e [k Hek]]. rewrite Hek in Heqx.
      destruct e. rewrite interp_mrec_vis_inl in Heqx. 
      rewrite H1, Heqy in Heqx.
      pinversion Heqx; inversion CHECK.
      rewrite interp_mrec_vis_inr in Heqx. rewrite H1, Heqy in Heqx. pinversion Heqx.
  - destruct H1. rewrite H1 in Heqx. destruct (eq_itree_case t) as [ | [ | ]].
    + destruct H2 as [r' Hr']. rewrite Hr' in Heqx. rewrite interp_mrec_ret in Heqx.
      pinversion Heqx; inversion CHECK.
    + destruct H2 as [t' Ht']. rewrite Ht' in Heqx. rewrite interp_mrec_tau in Heqx.
      apply eqit_inv_Tau in Heqx. eapply IHHstep in Heqx; eauto.
      destruct Heqx as [d Hd]. exists d. assert (S n = 1 + n). auto. rewrite H2.
      econstructor; eauto. econstructor. constructor. reflexivity. constructor. auto.
    + destruct H2 as [ [d | e] [Hk] ].
      * rewrite H2 in Heqx. rewrite interp_mrec_vis_inl in Heqx.
        apply eqit_inv_Tau in Heqx. eapply IHHstep in Heqx; eauto.
        destruct Heqx as [l Hl]. exists (d :: l). econstructor; eauto.
      * rewrite H2 in Heqx. rewrite interp_mrec_vis_inr in Heqx. pinversion Heqx; inversion CHECK.
Qed.

Lemma recursion_trace_vis R (t : entree (D + E) R) (e : E) k n :
  multi_step n (interp_mrec bodies t) (Vis e (fun x => interp_mrec bodies (k x))) ->
  exists d, recursion_trace n t d (Vis e (fun x => interp_mrec bodies (k x))).
Proof.
  intros Hstep.
  remember (interp_mrec bodies t) as x.
  assert (x ≅ interp_mrec bodies t). subst. reflexivity.
  clear Heqx. rename H1 into Heqx.
  remember ( (Vis e (fun x => interp_mrec bodies (k x)))) as y.
  assert (y ≅  (Vis e (fun x => interp_mrec bodies (k x)))). subst. reflexivity.
  clear Heqy. rename H1 into Heqy. generalize dependent t.
  generalize dependent e. induction Hstep; intros.
  - setoid_rewrite Heqy. exists [].
    destruct (eq_itree_case t) as [ | [ | ]].
    + destruct H2 as [r' Hr']. rewrite Hr' in Heqx. rewrite interp_mrec_ret in Heqx.
      rewrite H1 in Heqx. rewrite Heqy in Heqx. pinversion Heqx.
    + destruct H2 as [t'' Ht'']. rewrite Ht'' in Heqx.
      rewrite interp_mrec_tau in Heqx. rewrite H1, Heqy in Heqx.
      pinversion Heqx; inversion CHECK.
    + destruct H2 as [[d | e'] [k' Hk']]; rewrite Hk' in Heqx.
      * rewrite H1, Heqy in Heqx.
        rewrite interp_mrec_vis_inl in Heqx.  pinversion Heqx; inversion CHECK.
      * rewrite H1, Heqy in Heqx. rewrite interp_mrec_vis_inr in Heqx.
        econstructor 2; eauto.
  - destruct H1. rewrite H1 in Heqx. destruct (eq_itree_case t) as [ | [ | ]].
    + destruct H2 as [r' Hr']. rewrite Hr' in Heqx. rewrite interp_mrec_ret in Heqx.
      pinversion Heqx; inversion CHECK.
    + destruct H2 as [t' Ht']. rewrite Ht' in Heqx. rewrite interp_mrec_tau in Heqx.
      apply eqit_inv_Tau in Heqx. eapply IHHstep in Heqx; eauto.
      destruct Heqx as [d Hd]. exists d. assert (S n = 1 + n). auto. rewrite H2.
      econstructor; eauto. econstructor. constructor. reflexivity. constructor. auto.
    + destruct H2 as [ [d | e'] [Hk] ].
      * rewrite H2 in Heqx. rewrite interp_mrec_vis_inl in Heqx.
        apply eqit_inv_Tau in Heqx. eapply IHHstep in Heqx; eauto.
        destruct Heqx as [l Hl]. exists (d :: l). econstructor; eauto.
      * rewrite H2 in Heqx. rewrite interp_mrec_vis_inr in Heqx. pinversion Heqx; inversion CHECK.
Qed.

Lemma multi_step_interp_mrec_vis_inv R (t : entree (D + E) R) e k n : 
  multi_step n (interp_mrec bodies t) (Vis e k) ->
  exists k', forall x, k x ≅ interp_mrec bodies (k' x).
Proof.
  intros Hstep.
  remember (interp_mrec bodies t) as x.
  assert (x ≅ interp_mrec bodies t). subst. reflexivity.
  clear Heqx. rename H1 into Heqx.
  remember ( (Vis e k)) as y.
  assert (y ≅  (Vis e k)). subst. reflexivity.
  clear Heqy. rename H1 into Heqy. generalize dependent t.
  generalize dependent e. induction Hstep; intros.  
  - rewrite Heqx, Heqy in H1. clear Heqx Heqy.
    destruct (eq_itree_case t) as [ | [ | ]].
    + destruct H2. rewrite H2 in H1. rewrite interp_mrec_ret in H1. pinversion H1.
    + destruct H2. rewrite H2 in H1. rewrite interp_mrec_tau in H1.
      pinversion H1. inversion CHECK.
    + destruct H2 as [ [d | e'] [k' Hk'] ].
      * rewrite Hk' in H1. rewrite interp_mrec_vis_inl in H1. pinversion H1.
        inversion CHECK.
      * rewrite Hk' in H1. rewrite interp_mrec_vis_inr in H1.
        assert (e = e'). pinversion H1. subst. auto.
        subst. exists k'. intros. eapply eqit_Vis_inv in H1. symmetry. eauto.
  - dependent destruction H1. specialize (IHHstep e k Heqy).
    rewrite H1 in Heqx. destruct (eq_itree_case t) as [ | [ | ]].
    + destruct H2. rewrite H2 in Heqx. rewrite interp_mrec_ret in Heqx. pinversion Heqx.
      inversion CHECK.
    + destruct H2 as [t' Ht']. rewrite Ht', interp_mrec_tau in Heqx.
      apply eqit_inv_Tau in Heqx. eauto.
    + destruct H2 as [ [d | e'] [k' Hk'] ].
      * rewrite Hk', interp_mrec_vis_inl in Heqx. apply eqit_inv_Tau in Heqx.
        eauto.
      * rewrite Hk', interp_mrec_vis_inr in Heqx. pinversion Heqx. inversion CHECK.
Qed.

End RecursionTrace.

Definition apply_bodies {R1 R2 MR} {tin tout : type} (bodies : forall arg : denote_call_frame R1, mtree (denote_mfix_ctx (R2 :: MR)) (encodes arg))
           (x : var (tin, tout) R1) (vvin : denote_type tin) 
  : mtree (denote_mfix_ctx (R2 :: MR)) (denote_type tout) :=
    let '(d && f) := call_mrec_call_frame x vvin in
    Functor.fmap f (bodies d).

Section RecursionTraceDen.
  Context (R : call_frame) (MR : mfix_ctx).
  Context (bodies : forall arg : denote_call_frame R, mtree (denote_mfix_ctx (R :: MR)) (encodes arg)).

  Inductive call_den :=
    | call_den_in (tin tout : type) (x : var (tin, tout) R)
                  (vvin : denote_type tin).

  

  Inductive recursion_trace_den {t : type} :
    nat -> mtree (denote_mfix_ctx (R :: MR)) (denote_type t) -> list call_den -> mtree (denote_mfix_ctx MR) (denote_type t) -> Prop := 
  | recursion_trace_den_ret_in t r n t' : t' ≅ ret r -> t ≅ ret r -> recursion_trace_den n t [] t'
  | recursion_trace_den_inr_in t1 R tin tout (x : var (tin, tout) R) (xR : var R MR)
                              (vvin : denote_type tin) k1 t2 n :
    t2 ≅ vv <- call_term x xR vvin;; (interp_mrec bodies (k1 vv)) ->
    t1 ≅ vv <- call_term x (VarS xR) vvin;; k1 vv ->
    recursion_trace_den n t1 [] t2
  | recursion_trace_den_inl_in tin tout (x : var (tin, tout) R) (vvin : denote_type tin) k1 n t1 t2 l :
    t1 ≅ vv <- call_term x VarZ vvin;; k1 vv ->
    recursion_trace_den n (bind (apply_bodies bodies x vvin) k1) l t2 ->
    recursion_trace_den (S n) t1 (call_den_in tin tout x vvin :: l) t2
  | recursion_trace_den_multistep n m t1 t2 t3 l :
    multi_step n t1 t2 ->
    recursion_trace_den m t2 l t3 ->
    recursion_trace_den (n + m) t1 l t3
  .

  Instance recursion_trace_den_eq_itree t : Proper (eq ==> eq_itree eq ==> eq ==> eq_itree eq ==> Basics.flip Basics.impl) (@recursion_trace_den t).
  Proof.
    repeat intro. subst. 
    generalize dependent x0. generalize dependent x2. induction H3; intros.
    - eapply recursion_trace_den_ret_in; eauto. rewrite H2. eauto. rewrite H1. auto.
    - eapply recursion_trace_den_inr_in. rewrite H2. eauto. rewrite H1. auto.
    - econstructor; eauto. rewrite H0. eauto. eapply IHrecursion_trace_den; eauto.
      reflexivity.
    - econstructor; eauto. 2 : eapply IHrecursion_trace_den; eauto; try reflexivity.
      rewrite H0. auto.
  Qed.

  
  Inductive call_den_list_rel : list (denote_call_frame R) -> list call_den -> Prop :=
  | cdlr_nil : call_den_list_rel [] []
  | cdlr_cons h1 tin tout x vvin t1 t2 :  call_den_list_rel t1 t2 ->
    h1 = projT1 (call_mrec_call_frame x vvin) -> call_den_list_rel (h1 :: t1) (call_den_in tin tout x vvin :: t2).
  

  Lemma call_den_list_rel_ex1 l1 : exists l2, call_den_list_rel l1 l2.
  Proof.
    induction l1. exists []. constructor.
    destruct IHl1 as [l2 Hl2].
    specialize (call_extract (R :: MR) (inl a)) as [R' [xR [tin [tout [x [vvin Hcall]]]]] ].
    dependent destruction xR.
    2 : { simp call_mrec in Hcall. destruct (call_mrec x xR vvin). discriminate. }
    simp call_mrec in Hcall.
    exists (call_den_in _ _ x vvin :: l2). constructor; auto.
    destruct (call_mrec_call_frame x vvin). injection Hcall. intros. subst. auto.
 Qed.

 Lemma call_den_list_rel_ex2 l2 : exists l1, call_den_list_rel l1 l2.
 Proof.
   induction l2. exists []. constructor.
   destruct IHl2 as [l1 Hl1].
   dependent destruction a. exists (projT1 (call_mrec_call_frame x vvin) :: l1).
   constructor; auto.
 Qed.
  


  (* annoying mismatch of the actual traces *)
  Lemma recursion_trace_trace_den1 t n 
        (t1 : mtree (denote_mfix_ctx (R :: MR)) (denote_type t)) 
        (t2 : mtree (denote_mfix_ctx MR) (denote_type t)) l1 l2 :
    call_den_list_rel l1 l2 ->
    recursion_trace _ (denote_mrec_ctx (denote_mfix_ctx MR)) bodies n t1 l1 t2 -> recursion_trace_den (t := t) n t1 l2 t2.
  Proof.
    intros Hl Hrec. generalize dependent l2. induction Hrec.
    - intros. inversion Hl. subst. eapply recursion_trace_den_ret_in; eauto.
    - intros. inversion Hl. subst. 
      specialize (call_extract _ e) as [R' [xR [tin [tout [x [vvin Hcall]]]]] ].
      specialize (call_mrec_encodes _ _ _ _ x xR vvin) as Henc1.
      specialize (call_mrec_cont _ _ _ _ x xR vvin) as Henc2.
      destruct (call_mrec x xR vvin) as [d f] eqn : Heq. cbn in Hcall, Henc1, Henc2.
      subst. symmetry in Henc1.
      eapply recursion_trace_den_inr_in with (k1 := fun x => k (id_eq_refl Henc1 x)) (x := x). Unshelve. all : eauto.
      + rewrite H. unfold call_term. rewrite Heq. setoid_rewrite bind_trigger. setoid_rewrite bind_vis.
        apply eqit_Vis. intros. setoid_rewrite bind_ret_l. rewrite JMeq_id_id_eq_refl.
        reflexivity. auto.
      + rewrite H0. unfold call_term. simp call_mrec. rewrite Heq.
        setoid_rewrite bind_trigger. setoid_rewrite bind_vis. apply eqit_Vis.
        intros. setoid_rewrite bind_ret_l.
        rewrite JMeq_id_id_eq_refl; auto. reflexivity.
    - intros l1 Hl1. inversion Hl1. subst. specialize (IHHrec _ H2).
      specialize (call_mrec_call_frame_encodes _ _ _ x vvin) as Henc1.
      specialize (call_mrec_call_frame_cont _ _ _ x vvin) as Henc2.
      destruct (call_mrec_call_frame x vvin) as [d f] eqn : Heq. cbn in Henc1, Henc2, IHHrec, H, k1, Hl1.
      symmetry in Henc1. cbn in Hrec.
      eapply recursion_trace_den_inl_in with (k1 := fun x => k1 (id_eq_refl Henc1 x)).
      + unfold call_term. simp call_mrec. rewrite Heq. rewrite H.
        setoid_rewrite bind_trigger. setoid_rewrite bind_vis. apply eqit_Vis.
        intros. setoid_rewrite bind_ret_l. rewrite JMeq_id_id_eq_refl; auto. reflexivity.
      + unfold apply_bodies. rewrite Heq. setoid_rewrite bind_bind. 
        setoid_rewrite bind_ret_l. 
        assert ((EnTree.bind (bodies d) (fun r : encodes d => k1 (id_eq_refl Henc1 (f r)))) ≅ bind (bodies d) k1).
        eapply eqit_bind. reflexivity. intros. subst. rewrite JMeq_id_id_eq_refl; auto. reflexivity.
        rewrite H0. auto.
    - intros. specialize (IHHrec _ Hl). eapply recursion_trace_den_multistep; eauto.
  Qed.

  Lemma recursion_trace_trace_den2 t n 
        (t1 : mtree (denote_mfix_ctx (R :: MR)) (denote_type t)) 
        (t2 : mtree (denote_mfix_ctx MR) (denote_type t)) l1 l2 :
    call_den_list_rel l1 l2 ->
    recursion_trace_den (t := t) n t1 l2 t2 -> recursion_trace _ (denote_mrec_ctx (denote_mfix_ctx MR)) bodies n t1 l1 t2.
  Proof.
    intros Hl Hrec. generalize dependent l1. induction Hrec.
    - intros. inversion Hl. subst. eapply recursion_trace_ret_in; eauto.
    - intros. inversion Hl. subst. unfold call_term in H, H0.
      specialize (call_mrec_encodes _ _ _ _ x xR vvin) as Henc1.
      specialize (call_mrec_cont _ _ _ _ x xR vvin) as Henc2.
      simp call_mrec in H0.
      destruct (call_mrec x xR vvin) as [d f] eqn : Heq. cbn in Henc1, Henc2.
      setoid_rewrite bind_trigger in H. setoid_rewrite bind_vis in H.
      setoid_rewrite bind_trigger in H0. setoid_rewrite bind_vis in H0.
      eapply recursion_trace_inr_in; eauto. rewrite H. 
      apply eqit_Vis. intros. setoid_rewrite bind_ret_l. reflexivity.
    - intros l1 Hl1. inversion Hl1. subst. specialize (IHHrec _ H3). inj_existT. subst.
      specialize (call_mrec_call_frame_encodes _ _ _ x vvin) as Henc1.
      specialize (call_mrec_call_frame_cont _ _ _ x vvin) as Henc2.
      unfold call_term in H. simp call_mrec in H.
      destruct (call_mrec_call_frame x vvin) as [d f] eqn : Heq.
      cbn. cbn in Henc1, Henc2. setoid_rewrite bind_trigger in H. setoid_rewrite bind_vis in H.
      econstructor; eauto. eapply recursion_trace_eq_itree; try apply IHHrec; try reflexivity.
      unfold apply_bodies. rewrite Heq. setoid_rewrite bind_bind. reflexivity.
    - intros. specialize (IHHrec _ Hl). eapply recursion_trace_multi_step; eauto.
  Qed.

  Lemma recursion_trace_den_ret t (m : mtree (denote_mfix_ctx (R ::MR)) (denote_type t)) (r : denote_type t) n :
  multi_step n (interp_mrec bodies m) (ret r) ->
  exists l, recursion_trace_den n m l (ret r).
  Proof.
    intros. eapply recursion_trace_ret in H.
    destruct H as [l Hl]. specialize (call_den_list_rel_ex1 l) as Hl'. 
    destruct Hl' as [l2 Hl2]. exists l2. eapply recursion_trace_trace_den1; eauto.
  Qed.


  Lemma recursion_trace_den_vis (t : type) (m : mtree (denote_mfix_ctx (R :: MR)) (denote_type t)) 
        R' tin tout (x : var (tin, tout) R') (xR : var R' MR) (vvin : denote_type tin) k n :
    multi_step n (interp_mrec bodies m) (vv <- call_term x xR vvin;; (interp_mrec bodies (k vv))) ->
    exists l, recursion_trace_den n m l (vv <- call_term x xR vvin;; (interp_mrec bodies (k vv))).
  Proof.
    intros. unfold call_term in H. unfold call_term. destruct (call_mrec x xR vvin) as [d f].
    assert (Hd : (vv <- Functor.fmap f (EnTree.trigger d);; interp_mrec bodies (k vv)) ≅
            Vis d (fun x => interp_mrec bodies (k (f x)))).
    { setoid_rewrite bind_trigger. setoid_rewrite bind_vis. eapply eqit_Vis.
      intros. setoid_rewrite bind_ret_l. reflexivity. }
    rewrite Hd in H. setoid_rewrite Hd.
    eapply recursion_trace_vis in H. destruct H as [l Hl].
    specialize (call_den_list_rel_ex1 l) as Hl'. destruct Hl' as [l2 Hl2]. exists l2.
    eapply recursion_trace_trace_den1; eauto.
  Qed.

  Lemma multi_step_interp_mrec_den_vis_inv 
        (t : type) (m : mtree (denote_mfix_ctx (R :: MR)) (denote_type t)) 
        R' tin tout (x : var (tin, tout) R') (xR : var R' MR) (vvin : denote_type tin) 
        (k : denote_type tout -> mtree (denote_mfix_ctx MR) (denote_type t)) n :
    multi_step n (interp_mrec bodies m) (vv <- call_term x xR vvin;; k vv) ->
    exists k' : denote_type tout -> mtree (denote_mfix_ctx (R :: MR)) (denote_type t), 
    forall x, k x ≅ interp_mrec bodies (k' x).
  Proof.
    unfold call_term. 
    destruct (call_mrec x xR vvin) eqn : Heq. intros H.
    setoid_rewrite bind_trigger in H. setoid_rewrite bind_vis in H.
    eapply multi_step_interp_mrec_vis_inv in H. destruct H as [k' Hk'].
    setoid_rewrite bind_ret_l in Hk'. 
    specialize (call_mrec_encodes _ _ _ _ x xR vvin) as Henc1.
    specialize (call_mrec_cont _ _ _ _ x xR vvin) as Hcont.
    rewrite Heq in Henc1. cbn in Henc1. symmetry in Henc1.
    rewrite Heq in Hcont. cbn in Hcont.
    exists (fun x => k' (id_eq_refl Henc1 x)). intros. rewrite <- Hk'.
    erewrite JMeq_id_id_eq_refl'; auto. reflexivity.
  Qed.

End RecursionTraceDen.

Section TailRecursionTrace.
Context {E R S: Type} `{EncodedType E}.

Inductive tail_rec_trace (body : R -> entree E (R + S)) : 
  R -> nat -> entree E S -> Prop :=
 | trt_inl j1 j2 r r' t' t :
   t' ≅ ret (inl r') ->
   multi_step j1 (body r) t' ->
   tail_rec_trace body r' j2 t ->
   tail_rec_trace body r (1 + j1 + j2) t
 | trt_inr j t' t'' r s:
   t' ≅ ret (inr s) ->
   t'' ≅ ret s ->
   multi_step j (body r) t' ->
   tail_rec_trace body r j t''
 | trt_vis j r e k t' t'' :
   t' ≅ Vis e k ->
   t'' ≅ (Vis e (fun x => vv <- k x;; 
                       match vv with | inl r => Tau (EnTree.iter body r) | inr s => Ret s end)) ->
   multi_step j (body r) t' ->
   tail_rec_trace body r j t''.




End TailRecursionTrace.

#[local] Instance tail_rec_trace_eq_itree E R S `{EncodedType E} 
 (body : R -> entree E (R + S)) : Proper (eq ==> eq ==> eq_itree eq ==> Basics.flip Basics.impl) (tail_rec_trace body).
Proof.
  repeat intro. subst. generalize dependent x1. induction H3.
  - intros. econstructor; eauto.
  - intros. eapply trt_inr; eauto. rewrite H3. auto.
  - intros. eapply trt_vis; eauto. rewrite H3. auto.
Qed.

Lemma tail_rec_trace_multi_step1 E R S `{EncodedType E} 
      (body : R -> entree E (R + S)) (r : R) j t :
  tail_rec_trace body r j t -> multi_step j (EnTree.iter body r) t.
Proof.
  intros Hrec. dependent induction Hrec.
  - rewrite unfold_iter. revert Hrec H0 IHHrec.
    remember (body r) as t''.  clear Heqt''.
    dependent induction H1; intros.
    + rewrite H0. cbn. rewrite H1. setoid_rewrite bind_ret_l. cbn. econstructor.
      eauto. constructor. reflexivity.
    + dependent destruction H0. rewrite H0, bind_tau.
      eapply IHmulti_step in IHHrec; eauto. econstructor.
      2 : econstructor; reflexivity. fold (Nat.add n j2).
      assert (Datatypes.S (n + j2) = 1 + n + j2). lia. rewrite H3. auto.
  - rewrite unfold_iter.
    remember (body r) as t. clear Heqt. dependent induction H2.
    + rewrite H2, H0. setoid_rewrite bind_ret_l. constructor. symmetry. auto.
    + dependent destruction H3. rewrite H3, bind_tau. econstructor.
      2 : constructor; reflexivity. eauto.
  - rewrite unfold_iter. remember (body r) as t. clear Heqt. 
    dependent induction H2.
    + rewrite H2, H0, bind_vis. constructor. symmetry. auto.
    + dependent destruction H3. rewrite H3, bind_tau.
      econstructor.
      2 : constructor; reflexivity. eauto.
Qed.

Lemma tail_rec_trace_multi_step2 j : forall E A B `{EncodedType E} 
      (body : A -> entree E (A + B)) (r : A) s,
  multi_step j (EnTree.iter body r) (ret s) -> tail_rec_trace body r j (ret s).
Proof.
  induction j as [j Hj]  using (well_founded_induction lt_wf).
  intros E A B H body r s Hstep.
  rewrite unfold_iter in Hstep. eapply multi_step_ret_bind_inv in Hstep.
  destruct Hstep as [j1 [j2 [r0 [Hsum [Hstep1 Hstep2]]]]]. subst.
  destruct r0.
  - dependent destruction Hstep2. pinversion H0. inversion CHECK.
     dependent destruction H0. apply eqit_inv_Tau in H0.
     rewrite <- H0 in Hstep2. clear H0.
     assert (j1 + S n = 1 + j1 + n). lia. rewrite H0. clear H0.
     rename n into j2. eapply trt_inl; eauto. reflexivity. eapply Hj; eauto.
     lia.
   - assert (j2 = 0). dependent destruction Hstep2. auto.
     dependent destruction H0. pinversion H0. inversion CHECK.
     subst. dependent destruction Hstep2. apply eqit_Ret_inv in H0.
     subst b. assert (j1 + 0 = j1). lia. rewrite H0. clear H0.
     eapply trt_inr. reflexivity. reflexivity. auto.
Qed.

Lemma tail_rec_trace_multi_step3 j : forall E A B `{EncodedType E} 
      (body : A -> entree E (A + B)) r e k t,
    t ≅ (Vis e (fun x => vv <- k x;; 
                       match vv with | inl r => Tau (EnTree.iter body r) | inr s => Ret s end)) ->
  multi_step j (EnTree.iter body r) t ->
  tail_rec_trace body r j t.
Proof.
  induction j as [j Hj]  using (well_founded_induction lt_wf).
  intros E A B H body r e k t Ht Hstep. rewrite Ht in Hstep. 
  rewrite unfold_iter in Hstep.
  eapply multi_step_vis_bind_inv in Hstep.
  destruct Hstep as [Hstep | Hstep].
  - destruct Hstep as [j1 [j2 [[a | b] [H1 [H2 H3]]]]]; subst.
    + destruct j2. dependent destruction H3.
      pinversion H0. inversion CHECK.
      assert (j1 + S j2 = 1 + j1 + j2). lia. rewrite H0.
      eapply trt_inl. reflexivity. eauto.
      eapply Hj. lia. eauto.
      dependent destruction H3. dependent destruction H0.
      apply eqit_inv_Tau in H0. rewrite Ht, H0. auto.
    + apply multi_step_eutt in H3. pinversion H3.
 - destruct Hstep as [k' [Hstep Hk']].
   destruct (eq_itree_case t) as [[r' Hr'] | [[t' Ht'] | [e' [k'' Hek]] ]].
    + rewrite Hr' in Ht. pinversion Ht.
    + rewrite Ht' in Ht. pinversion Ht; inversion CHECK.
    + rewrite Hek in Ht.
      assert (e = e'). pinversion Ht. auto. subst e'.
      eapply trt_vis with (t' := Vis e k'); eauto. reflexivity. rewrite Hek, Ht. 
      apply eqit_Vis. symmetry. auto. eapply Hk'.
Qed.

Lemma tail_rec_trace_multi_step4 j : 
  forall MR A B (body : A -> mtree (denote_mfix_ctx MR) (A + B)) r 
    R (xR : var R MR) tin tout (x : var (tin, tout) R)
    (vvin : denote_type tin) k t,
    t ≅ vvout <- call_term x xR vvin;;
        vv     <- k vvout;;
        match vv with | inl r => Tau (EnTree.iter body r) | inr s => Ret s end ->
    multi_step j (EnTree.iter body r) t ->
    tail_rec_trace body r j t.
Proof.
  intros. rewrite H. unfold call_term in *. destruct (call_mrec x xR vvin). 
  setoid_rewrite bind_trigger. setoid_rewrite bind_vis. 
  eapply tail_rec_trace_multi_step3 with (e := x0) (k := fun x => k (d x)).
  apply eqit_Vis. intros. setoid_rewrite bind_ret_l. reflexivity. 
  setoid_rewrite bind_trigger in H. setoid_rewrite bind_vis in H.
  rewrite H in H0. auto.
Qed.

Section TailRecursionTraceDen.
  Context {MR : mfix_ctx} {R S : Type}.


  Inductive tail_rec_trace_call (body : R -> mtree (denote_mfix_ctx MR) (R + S)) : 
    R -> nat -> mtree (denote_mfix_ctx MR) S -> Prop :=
  | trtc_inl j1 j2 r r' t' t :
    t' ≅ ret (inl r') ->
    multi_step j1 (body r) t' ->
    tail_rec_trace_call body r' j2 t ->
    tail_rec_trace_call body r (1 + j1 + j2) t
  | trtc_inr j t' t'' r s:
    t' ≅ ret (inr s) ->
    t'' ≅ ret s ->
    multi_step j (body r) t' ->
    tail_rec_trace_call body r j t''
  | trtc_call j r R' tin tout (x : var (tin, tout) R') (xR : var R' MR) (vvin : denote_type tin) k t' t'' :
    t' ≅ bind (call_term x xR vvin) k ->
    t'' ≅ bind (call_term x xR vvin) (fun x => vv <- k x;; 
                        match vv with | inl r => Tau (EnTree.iter body r) | inr s => Ret s end) ->
    multi_step j (body r) t' ->
    tail_rec_trace_call body r j t''.

End TailRecursionTraceDen.

Lemma tail_rec_trace_call1 j : forall MR R S (body : R -> mtree (denote_mfix_ctx MR) (R + S)) t r,
  tail_rec_trace body r j t -> tail_rec_trace_call body r j t.
Proof. 
  induction j as [j IHj] using (well_founded_induction lt_wf).
  intros. dependent destruction H.
  - eapply trtc_inl; eauto. eapply IHj. lia. auto.
  - eapply trtc_inr; eauto.
  - specialize (call_extract MR e) as [R' [xR [tin [tout [x [vvin Hcall]]]]]].
    specialize (call_mrec_encodes _ _ _ _ x xR vvin) as Henc.
    specialize (call_mrec_cont _ _ _ _ x xR vvin) as Hcont.
    rewrite Hcall in Henc. symmetry in Henc.
    set (fun x => k (id_eq_refl Henc x)) as k'.
    eapply trtc_call with (x := x) (xR := xR) (vvin := vvin) (k := k'); eauto.
    + rewrite H. clear H0. unfold call_term.
      destruct (call_mrec x xR vvin) eqn : Hcall'. cbn in *.
      subst x0. setoid_rewrite bind_trigger. setoid_rewrite bind_vis.
      apply eqit_Vis. intros. unfold k'. setoid_rewrite bind_ret_l.
      rewrite JMeq_id_id_eq_refl; auto. reflexivity.
    + rewrite H0. clear H H0. unfold call_term.
      destruct (call_mrec x xR vvin) eqn : Hcall'. cbn in *.
      subst x0. setoid_rewrite bind_trigger. setoid_rewrite bind_vis.
      apply eqit_Vis. intros. setoid_rewrite bind_ret_l.
      eapply eqit_bind with (UU := eq).
      unfold k'.
      rewrite JMeq_id_id_eq_refl; auto. reflexivity.
      intros. subst. reflexivity.
Qed.

Lemma tail_rec_trace_call2 j : forall MR R S (body : R -> mtree (denote_mfix_ctx MR) (R + S)) t r,
  tail_rec_trace_call body r j t -> tail_rec_trace body r j t.
Proof. 
  induction j as [j IHj] using (well_founded_induction lt_wf).
  intros. dependent destruction H.
  - eapply trt_inl; eauto. eapply IHj; auto. lia.
  - eapply trt_inr; eauto.
  - unfold call_term in *. destruct (call_mrec x xR vvin).
    setoid_rewrite bind_trigger in H. setoid_rewrite bind_trigger in H0.
    setoid_rewrite bind_vis in H. setoid_rewrite bind_vis in H0.
    eapply trt_vis; eauto. rewrite H0. apply eqit_Vis.
    intros. setoid_rewrite bind_ret_l. reflexivity.
Qed.
