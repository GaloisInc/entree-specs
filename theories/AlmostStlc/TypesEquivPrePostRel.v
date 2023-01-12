Require Export TypedVar.
Require Export SyntaxSeq.
Require Export SmallStepSeq.
Require Export DenotationFacts.
Require Export DenotationSeq.
Require Export Eqit.
Require Export Rutt.
Require Export RuttFacts.
Require Import ITree.Basics.HeterogeneousRelations.
Require Export InterpMTreeFacts.
Import List.ListNotations.
Open Scope list_scope.
From Equations Require Import Equations Signature.
Require Import Coq.Program.Equality.
Require Import ExtLib.Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

Require Export TypesEquiv.

Definition commute_remove_rel {R MR xR} (rel : Rel (denote_mrec_ctx (denote_mfix_ctx (remove R MR xR) ) ) (denote_mrec_ctx (denote_mfix_ctx (remove R MR xR) ))) :
  Rel (denote_remainder (denote_mfix_ctx MR) (denote_var xR) ) (denote_remainder (denote_mfix_ctx MR) (denote_var xR) ) :=
  fun d1 d2 => 
    rel (projT1 (remove_denote xR d1) ) (projT1 (remove_denote xR d2)).

Definition commute_remove_post_rel {R MR xR} (rel : PostRel (denote_mrec_ctx (denote_mfix_ctx (remove R MR xR) ) ) (denote_mrec_ctx (denote_mfix_ctx (remove R MR xR) ))) :
  PostRel (denote_remainder (denote_mfix_ctx MR) (denote_var xR) ) (denote_remainder (denote_mfix_ctx MR) (denote_var xR) ) :=
  fun d1 d2 a b =>
      let '(d1' && f1) := remove_denote xR d1 in
      let '(d2' && f2) := remove_denote xR d2 in
      exists a' b',
        a = f1 a' ->
        b = f2 b' ->
        rel d1' d2' a' b'.

Definition commute_remove_post_rel' {R MR xR} (rel : PostRel (denote_mrec_ctx (denote_mfix_ctx (remove R MR xR) ) ) (denote_mrec_ctx (denote_mfix_ctx (remove R MR xR) ))) :
  PostRel (denote_remainder (denote_mfix_ctx MR) (denote_var xR) ) (denote_remainder (denote_mfix_ctx MR) (denote_var xR) ) :=
  fun d1 d2 a b =>
    forall (H1 : denote_remainder (denote_mfix_ctx MR) (denote_var xR) = (denote_mrec_ctx (denote_mfix_ctx (remove R MR xR) ))) (H2 : encodes d1 = encodes (id_eq H1 d1) ) 
      (H3 : encodes d2 = encodes (id_eq H1 d2) ), 
      rel (id_eq H1 d1) (id_eq H1 d2) (id_eq H2 a) (id_eq H3 b)
.

(* maybe the difficulty I am having now is an indication that I should rewrite the language *)

Transparent denote_var.

(* try to come up with something more general *)
Lemma commute_remove_post_rel_correct R MR xR : forall
      (rel : PostRel (denote_mrec_ctx (denote_mfix_ctx (remove R MR xR)))
         (denote_mrec_ctx (denote_mfix_ctx (remove R MR xR)))) 
      d1 d2 d1' d2' a b a' b',
  d1 ~= d1' -> d2 ~= d2' -> a ~= a' -> b ~= b' -> 
  rel d1' d2' a' b' -> commute_remove_post_rel rel d1 d2 a b.
Proof.
  intros. red.
  destruct (remove_denote xR d1) eqn : Heq1.
  destruct (remove_denote xR d2) eqn : Heq2.
  exists a'.
  dependent induction xR.
  - intros.
    red. simpl remove_denote. simpl. exists a0. exists b.
    intros. subst. auto.
  - intros. red. simpl remove_denote.
    destruct d1; destruct d2.
    + exists a0. exists b0. intros. subst.
      destruct d1'; destruct d2'.
      * simpl denote_var in *. cbn in a0.  eapply IHxR in H3; try eapply H1. 4 : { eapply H1. eauto.
      2 : { injection H.
      admit.
    +
      cbn in a0, b0. cbn in a'. 
    simpl remove in *. simpl. cbn.

Notation mfix_pre_equiv_insert MR R xR := (InsertPreRel (denote_var xR) (denote_var xR) (call_frame_pre_equiv R) (commute_remove_rel (mfix_pre_equiv (remove R MR xR)) )).


(**)
Lemma mfix_pre_equiv_position (MR : mfix_ctx) (R : call_frame)
      (t1 t2 : type) (xR : var R MR) (x : var (t1, t2) R) 
      (v1 v2 : denote_type t1) (d1 d2 : denote_mrec_ctx (denote_mfix_ctx MR)) :
  d1 = projT1 (call_mrec x xR v1) ->
  d2 = projT1 (call_mrec x xR v2) ->
  types_equiv t1 v1 v2 ->
  mfix_pre_equiv MR d1 d2.
Proof.
  revert x. dependent induction xR.
  - setoid_rewrite call_mrec_equation_1. intros x.
    dependent induction x.
    + setoid_rewrite call_mrec_call_frame_equation_1. 
      intros. cbn in H, H0. subst. constructor. constructor. auto.
    + destruct b as [t3 t4]. setoid_rewrite call_mrec_call_frame_equation_2.
      intros. specialize IHx with (x0 := x) (v1 := v1) (v2 := v2); eauto.
      destruct (call_mrec_call_frame x v1) eqn : Heq1.
      destruct (call_mrec_call_frame x v2) eqn : Heq2.
      simpl projT1 in IHx. simpl in H, H0. specialize (IHx (inl x1) (inl x0)). 
      eapply IHx in H1; eauto.
      subst. rewrite mfix_pre_equiv_equation_2. constructor.
      rewrite call_frame_pre_equiv_equation_2. constructor.
      rewrite mfix_pre_equiv_equation_2 in H1. inversion H1. auto.
  - setoid_rewrite call_mrec_equation_2. intros.
    destruct (call_mrec x xR v1) eqn : Heq1.
    destruct (call_mrec x xR v2) eqn : Heq2.
    subst. constructor. eapply IHxR; eauto. rewrite Heq1. auto.
    rewrite Heq2. auto.
Qed.

Lemma mfix_pre_equiv_position_inv (MR : mfix_ctx) (R : call_frame)
      (t1 t2 : type) (xR : var R MR) (x : var (t1, t2) R) 
      (v1 v2 : denote_type t1) (d1 d2 : denote_mrec_ctx (denote_mfix_ctx MR)) :
  d1 = projT1 (call_mrec x xR v1) ->
  d2 = projT1 (call_mrec x xR v2) ->
  mfix_pre_equiv MR d1 d2 ->
  types_equiv t1 v1 v2.
Proof.
  revert x. generalize dependent d1. generalize dependent d2.
  dependent induction xR.
  - setoid_rewrite call_mrec_equation_1. intros d2 d1 x.
    generalize dependent d2. generalize dependent d1.
    dependent induction x.
    + setoid_rewrite call_mrec_call_frame_equation_1.
      simpl projT1. intros. subst.
      rewrite mfix_pre_equiv_equation_2 in H1.
      dependent destruction H1.
      rewrite call_frame_pre_equiv_equation_2 in H.
      dependent destruction H. auto.
    + destruct b. setoid_rewrite call_mrec_call_frame_equation_2.
      intros.
      specialize (IHx t2 t1 v1 v2 x eq_refl JMeq_refl).
      destruct (call_mrec_call_frame x v1) eqn : Heq1.
      destruct (call_mrec_call_frame x v2) eqn : Heq2.
      cbn in H, H0. simpl projT1 in IHx. subst.
      rewrite mfix_pre_equiv_equation_2 in H1.
      dependent destruction H1.
      rewrite call_frame_pre_equiv_equation_2 in H.
      dependent destruction H. eapply IHx; eauto.
      constructor; auto.
  - setoid_rewrite call_mrec_equation_2.
    intros.
    destruct (call_mrec x xR v1) eqn : Heq1.
    destruct (call_mrec x xR v2) eqn : Heq2.
    cbn in H, H0. subst.
    specialize (IHxR v1 v2 x1 x0 x).
    apply IHxR.
    rewrite Heq1. auto. rewrite Heq2. auto.
    rewrite mfix_pre_equiv_equation_2 in H1.
    dependent destruction H1. auto.
Qed.

Lemma denote_mfix_exists (MR : mfix_ctx) (d : denote_mrec_ctx (denote_mfix_ctx MR)) : exists (R : call_frame) xR t1 t2 (x : var (t1,t2) R) v,
    d = projT1 (call_mrec x xR v).
Proof.
  revert d. induction MR.
  - intros. destruct d.
  - intros. destruct d.
    + exists a. exists (VarZ). setoid_rewrite call_mrec_equation_1.
      clear IHMR. revert d. induction a.
      intros [].
      intros. simpl in d. destruct a. destruct d.
      * exists t. exists t0. exists VarZ. 
        setoid_rewrite call_mrec_call_frame_equation_1. 
        cbn. eexists. eauto.
      * specialize (IHa d). 
        destruct IHa as [ t1 [t2 [x [v Hd] ] ] ].
        exists t1. exists t2. exists (VarS x). exists v.
        setoid_rewrite call_mrec_call_frame_equation_2.
        destruct (call_mrec_call_frame x v).
        injection Hd. intros. subst. auto.
    + specialize (IHMR d).
      destruct IHMR as [R [xR [t1 [t2 [x [v Hd] ] ] ]]].
      exists R. exists (VarS xR). exists t1. exists t2. exists x. exists v.
      simp call_mrec. destruct (call_mrec x xR v).
      subst. auto.
Qed.
(* may need to do again for the insert rel version *)
Lemma mfix_pre_equiv_position_inv_call1 (MR : mfix_ctx) (R1 R2 : call_frame)
      (t1 t2 t3 t4 : type) (xR : var R1 MR) (yR : var R2 MR) 
      (x : var (t1, t2) R1) (y : var (t3,t4) R2) 
      v1 v2 (d1 d2 : denote_mrec_ctx (denote_mfix_ctx MR)) :
  d1 = projT1 (call_mrec x xR v1) ->
  d2 = projT1 (call_mrec y yR v2) ->
  mfix_pre_equiv MR d1 d2 ->
  R1 = R2.
Proof.
  generalize dependent d2. generalize dependent d1.
  revert x y v1 v2 yR. dependent induction xR.
  - setoid_rewrite call_mrec_equation_1.
    intros. destruct (call_mrec_call_frame x v1) as [d1' f1] eqn : Heq1.
    cbn in H. rewrite H in H1. rewrite mfix_pre_equiv_equation_2 in H1.  
    dependent destruction H1.
    dependent destruction yR.
    2 : { setoid_rewrite call_mrec_equation_2 in H0.
          destruct (call_mrec y yR v2); discriminate. }
    setoid_rewrite call_mrec_equation_1 in H0.
    destruct (call_mrec_call_frame y v2) as [d2' f2] eqn : Heq2.
    auto.
  - setoid_rewrite call_mrec_equation_2.
    intros. destruct (call_mrec x xR v1) as [d1' f1] eqn: Heq1.
    subst. simpl projT1 in H1.
    dependent destruction yR.
    + setoid_rewrite call_mrec_equation_1 in H1.
      destruct (call_mrec_call_frame y v2). 
      simpl in H1;
      dependent destruction H1.
    + setoid_rewrite call_mrec_equation_2 in H1.
      destruct (call_mrec y yR v2) as [d2' f2] eqn : Heq2.
      rewrite mfix_pre_equiv_equation_2 in H1.
      dependent destruction H1. eapply IHxR; eauto.
      rewrite Heq1, Heq2. auto.
Qed.

Lemma mfix_pre_equiv_position_inv_call2 (MR : mfix_ctx) R
      (t1 t2 t3 t4 : type) (xR : var R MR) (yR : var R MR) 
      (x : var (t1, t2) R) (y : var (t3,t4) R) 
      v1 v2 (d1 d2 : denote_mrec_ctx (denote_mfix_ctx MR)) :
  d1 = projT1 (call_mrec x xR v1) ->
  d2 = projT1 (call_mrec y yR v2) ->
  mfix_pre_equiv MR d1 d2 ->
  t1 = t3 /\ t2 = t4 /\ xR = yR.
Proof.
  generalize dependent d2. generalize dependent d1.
  revert x y v1 v2 yR. dependent induction xR.
  - setoid_rewrite call_mrec_equation_1.
    intros. destruct (call_mrec_call_frame x v1) as [d1' f1] eqn : Heq1.
    cbn in H. rewrite H in H1. rewrite mfix_pre_equiv_equation_2 in H1.  
    dependent destruction H1.
    dependent destruction yR.
    2 : { setoid_rewrite call_mrec_equation_2 in H0.
          destruct (call_mrec y yR v2); discriminate. }
    setoid_rewrite call_mrec_equation_1 in H0.
    destruct (call_mrec_call_frame y v2) as [d2' f2] eqn : Heq2.
    injection H0. intros. subst a2. clear H0.
    revert Heq1 Heq2 H1. generalize dependent d2'. generalize dependent d1'.
    revert v1 v2 y. dependent induction x.
    + setoid_rewrite call_mrec_call_frame_equation_1. intros.
      injection Heq1. intros. subst.
      rewrite call_frame_pre_equiv_equation_2 in H1. 
      dependent destruction H1.
      dependent destruction y. auto.
      simp call_mrec_call_frame in Heq2.
      destruct (call_mrec_call_frame y v2). discriminate.
    + destruct b. setoid_rewrite call_mrec_call_frame_equation_2. intros.
      destruct (call_mrec_call_frame x v1) as [d1'' f1'] eqn : Heq3.
      injection Heq1. intros. subst.
      rewrite call_frame_pre_equiv_equation_2 in H1.
      dependent destruction H1.
      dependent destruction y.
      simp call_mrec_call_frame in Heq2. discriminate.
      simp call_mrec_call_frame in Heq2.
      destruct (call_mrec_call_frame y v2) as [d2' f2'] eqn : Heq4.
      injection Heq2. intros. subst b2. eapply IHx in H; eauto. 
      decompose record H. subst. repeat split; auto.
  - setoid_rewrite call_mrec_equation_2. intros.
    destruct (call_mrec x xR v1) as [d1' f1] eqn: Heq1.
    subst. simpl projT1 in H1.
    dependent destruction yR.
    + setoid_rewrite call_mrec_equation_1 in H1.
      destruct (call_mrec_call_frame y v2). 
      simpl in H1;
      dependent destruction H1.
    + setoid_rewrite call_mrec_equation_2 in H1.
      destruct (call_mrec y yR v2) as [d2' f2] eqn : Heq2.
      rewrite mfix_pre_equiv_equation_2 in H1.
      dependent destruction H1. 
      eapply IHxR in H; eauto.
      2 : rewrite Heq1; auto.
      2  : rewrite Heq2; auto.
      decompose record H. subst. repeat split; auto.
Qed.

Lemma mfix_pre_equiv_position_inv_call3 (MR : mfix_ctx) R
      (t1 t2: type) (xR : var R MR)
      (x y : var (t1, t2) R)
      v1 v2 (d1 d2 : denote_mrec_ctx (denote_mfix_ctx MR)) :
  d1 = projT1 (call_mrec x xR v1) ->
  d2 = projT1 (call_mrec y xR v2) ->
  mfix_pre_equiv MR d1 d2 ->
  x = y.
Proof.
  generalize dependent d2. generalize dependent d1.
  revert x y v1 v2. dependent induction xR.
  - setoid_rewrite call_mrec_equation_1.
    intros. destruct (call_mrec_call_frame x v1) as [d1' f1] eqn : Heq1.
    cbn in H. rewrite H in H1. rewrite mfix_pre_equiv_equation_2 in H1.  
    dependent destruction H1.
    destruct (call_mrec_call_frame y v2) as [d2' f2] eqn : Heq2.
    injection H0. intros. subst a2. clear H0.
    revert Heq1 Heq2 H1. generalize dependent d2'. generalize dependent d1'.
    revert v1 v2 y. dependent induction x.
    + setoid_rewrite call_mrec_call_frame_equation_1. intros.
      injection Heq1. intros. subst.
      rewrite call_frame_pre_equiv_equation_2 in H1. 
      dependent destruction H1.
      dependent destruction y. auto.
      simp call_mrec_call_frame in Heq2.
      destruct (call_mrec_call_frame y v2). discriminate.
    + destruct b. setoid_rewrite call_mrec_call_frame_equation_2. intros.
      destruct (call_mrec_call_frame x v1) as [d1'' f1'] eqn : Heq3.
      injection Heq1. intros. subst.
      rewrite call_frame_pre_equiv_equation_2 in H1.
      dependent destruction H1.
      dependent destruction y.
      simp call_mrec_call_frame in Heq2. discriminate.
      simp call_mrec_call_frame in Heq2.
      destruct (call_mrec_call_frame y v2) as [d2' f2'] eqn : Heq4.
      injection Heq2. intros. subst b2. 
      enough (x = y); subst; auto.
      eapply IHx; eauto.
  - setoid_rewrite call_mrec_equation_2. intros.
    destruct (call_mrec x xR v1) as [d1' f1] eqn: Heq1.
    subst. simpl projT1 in H1.
    destruct (call_mrec y xR v2) as [d2' f2] eqn : Heq2.
    rewrite mfix_pre_equiv_equation_2 in H1.
    dependent destruction H1. eapply IHxR; eauto.
    rewrite Heq1, Heq2. auto.
Qed.



Lemma insert_pre_rel_mfix_pre_equiv_1 (MR : mfix_ctx) (R : call_frame) (xR : var R MR) : 
  forall x y, 
    mfix_pre_equiv MR x y ->
  InsertPreRel (denote_var xR) (denote_var xR) (call_frame_pre_equiv R) (commute_remove_rel (mfix_pre_equiv (remove R MR xR)) ) x y.
Proof.
  induction xR.
  - intros. rewrite mfix_pre_equiv_equation_2 in H.
    red. dependent destruction H.
    + constructor. auto.
    + constructor. red.
      setoid_rewrite remove_denote_equation_1.
      Transparent remove. cbn. Opaque remove. auto.
  - intros. rewrite mfix_pre_equiv_equation_2 in H. dependent destruction H. 
     { do 2 constructor; auto. }
     simpl denote_var. red. 
     eapply IHxR in H. red in H.
     dependent destruction H.
     + destruct 
         ((bring_to_front (denote_mfix_ctx l) (denote_var xR) b1))
         eqn : Heq1; cbn in x0; subst; try discriminate.
       unfold denote_mfix_ctx. simpl.
       rewrite bring_to_front_equation_5.
       setoid_rewrite Heq1.
       simpl.
       destruct 
         ((bring_to_front (denote_mfix_ctx l) (denote_var xR) b2))
         eqn : Heq2; cbn in x; subst; try discriminate.
       unfold denote_mfix_ctx. simpl.
       rewrite bring_to_front_equation_5.
       setoid_rewrite Heq2. constructor.
       auto.
     + destruct 
         ((bring_to_front (denote_mfix_ctx l) (denote_var xR) b1))
         eqn : Heq1; cbn in x0; subst; try discriminate.
       unfold denote_mfix_ctx. simpl.
       rewrite bring_to_front_equation_5.
       setoid_rewrite Heq1.
       simpl.
       destruct 
         ((bring_to_front (denote_mfix_ctx l) (denote_var xR) b2))
         eqn : Heq2; cbn in x; subst; try discriminate.
       unfold denote_mfix_ctx. simpl.
       rewrite bring_to_front_equation_5.
       setoid_rewrite Heq2.
       constructor.
       clear - H. red. Transparent remove_denote.
       red in H.
       simpl remove_denote.
       Transparent remove. simpl remove. simpl.
       destruct (remove_denote xR b0);
         destruct (remove_denote xR b3).
       constructor. auto.
Qed.

(* now that I've got this proof done, maybe think a bit if it can be improved *)

Lemma insert_pre_rel_mfix_pre_equiv_2 (MR : mfix_ctx) (R : call_frame) (xR : var R MR) : 
  forall d1 d2, 
  InsertPreRel (denote_var xR) (denote_var xR) (call_frame_pre_equiv R) (commute_remove_rel (mfix_pre_equiv (remove R MR xR)) ) d1 d2 -> 
  mfix_pre_equiv MR d1 d2.
Proof.
  intros d1 d2 H. red in H.
  remember (bring_to_front (denote_mfix_ctx MR) (denote_var xR) d1) as d1'.
  remember (bring_to_front (denote_mfix_ctx MR) (denote_var xR) d2) as d2'.
  dependent destruction H.
  - destruct d1' as [ [d1' | d1'] f]; try discriminate.
    destruct d2' as [ [d2' | d2'] g]; try discriminate.
    injection x. injection x0. intros. subst. 
    revert Heqd1' Heqd2' H. clear x x0.
    generalize dependent d1. generalize dependent d2.
    revert d1' d2'. dependent induction xR.
    + simpl denote_var. intros.
      destruct d1.
      2 : { setoid_rewrite bring_to_front_equation_3 in Heqd1'. discriminate. }
      setoid_rewrite bring_to_front_equation_2 in Heqd1'. 
      injection Heqd1'. intros. subst.
      destruct d2.
      2 : { setoid_rewrite bring_to_front_equation_3 in Heqd2'. discriminate. }
      setoid_rewrite bring_to_front_equation_2 in Heqd2'. 
      rewrite mfix_pre_equiv_equation_2. constructor.
      injection Heqd2'. intros. subst. auto.
    + simpl denote_var. intros.
      destruct d1.
      { setoid_rewrite bring_to_front_equation_4 in Heqd1'. discriminate. }
      destruct d2.
      { setoid_rewrite bring_to_front_equation_4 in Heqd2'. discriminate. }
      setoid_rewrite bring_to_front_equation_5 in Heqd1'.
      destruct (bring_to_front
                ((fix map (l : list mrec_ctx) : mrec_ctx :=
                    match l with
                    | [] => []
                    | a :: t => denote_mrec_ctx a && encoded_mrec_ctx a :: map t
                    end)
                   ((fix map (l : mfix_ctx) : list mrec_ctx :=
                       match l with
                       | [] => []
                       | a :: t =>
                           List.map
                             (fun '(t1, t2) =>
                              denote_type t1 && inout_encoded (denote_type t1) (denote_type t2)) a
                           :: map t
                       end) l)) (denote_var xR) d) eqn : Heq1.
      destruct x; try discriminate. injection Heqd1'. intros. subst.
      setoid_rewrite bring_to_front_equation_5 in Heqd2'.
      destruct (bring_to_front
                ((fix map (l : list mrec_ctx) : mrec_ctx :=
                    match l with
                    | [] => []
                    | a :: t => denote_mrec_ctx a && encoded_mrec_ctx a :: map t
                    end)
                   ((fix map (l : mfix_ctx) : list mrec_ctx :=
                       match l with
                       | [] => []
                       | a :: t =>
                           List.map
                             (fun '(t1, t2) =>
                              denote_type t1 && inout_encoded (denote_type t1) (denote_type t2)) a
                           :: map t
                       end) l)) (denote_var xR) d0) eqn : Heq2.
      destruct x; try discriminate. injection Heqd2'. intros. subst.
      rewrite mfix_pre_equiv_equation_2. constructor.
      eapply IHxR; eauto.
  - subst. red in H. generalize dependent xR. intros xR.
    dependent induction xR.
    + simpl remove_denote. simpl projT1. intros.
      destruct ((bring_to_front (denote_mfix_ctx (a :: l)) VarZ d1)) as [d1' f1] eqn : Heq1.
      destruct ((bring_to_front (denote_mfix_ctx (a :: l)) VarZ d2)) as [d2' f2] eqn : Heq2.
      Transparent bring_to_front. cbn in x0. cbn in x.
      destruct d2; destruct d1; try discriminate.
      injection x. injection x0. intros. subst.
      rewrite mfix_pre_equiv_equation_2. constructor.
      assert (l = remove a (a :: l) VarZ). simp remove. auto.
      simpl in H. auto.
    + intros. rewrite mfix_pre_equiv_equation_2.
      destruct d1; destruct d2; simpl in x0; simpl in x; try injection x; try injection x0; intros;
        subst.
      * constructor. simpl in H. dependent destruction H. auto.
      * cbn in x.
        destruct (bring_to_front
             (denote_mfix_ctx'
                (List.map
                   (List.map
                      (fun '(t1, t2) =>
                       denote_type t1 && inout_encoded (denote_type t1) (denote_type t2))) l))
             (denote_var xR) d0). destruct x1; try discriminate.
        destruct b2. discriminate. injection x. intros. subst.
        simpl in H. destruct (remove_denote xR d1). dependent destruction H.
      * cbn in x0.
        destruct (bring_to_front
             (denote_mfix_ctx'
                (List.map
                   (List.map
                      (fun '(t1, t2) =>
                       denote_type t1 && inout_encoded (denote_type t1) (denote_type t2))) l))
             (denote_var xR) d). destruct x1; try discriminate.
        destruct b1. discriminate. injection x0. intros. subst.
        simpl in H. destruct (remove_denote xR d1). dependent destruction H.
      * cbn in x. cbn in x0.
        destruct (bring_to_front
              (denote_mfix_ctx'
                 (List.map
                    (List.map
                       (fun '(t1, t2) =>
                        denote_type t1 && inout_encoded (denote_type t1) (denote_type t2))) l))
              (denote_var xR) d) eqn : Heq1. destruct x1; try discriminate.
        injection x0. intros. subst.
        destruct (bring_to_front
             (denote_mfix_ctx'
                (List.map
                   (List.map
                      (fun '(t1, t2) =>
                       denote_type t1 && inout_encoded (denote_type t1) (denote_type t2))) l))
             (denote_var xR) d0) eqn : Heq2. destruct x1; try discriminate.
        injection x. intros. subst. constructor.
        eapply IHxR; eauto.
        2 : { setoid_rewrite Heq1. simpl. reflexivity. }
        2 : { setoid_rewrite Heq2. simpl. reflexivity. }
        simpl remove_denote in H.
        destruct (remove_denote xR d1). destruct (remove_denote xR d2).
        cbn in H. dependent destruction H; auto.
Qed.
(*
ipr_intro_l
     : forall (MR1 MR2 : mrec_ctx) (In1 In2 : Type)
         (Out1 : EncodedType In1) (Out2 : EncodedType In2)
         (x : var (In1 && Out1) MR1) (y : var (In2 && Out2) MR2)
         (RPostInv : PostRel In1 In2)
         (RPost : PostRel (denote_remainder MR1 x)
                    (denote_remainder MR2 y))
         (d1 : denote_mrec_ctx MR1) (d2 : denote_mrec_ctx MR2)
         (a : encodes d1) (b : encodes d2)
         (d1' : In1 + denote_remainder MR1 x)
         (d2' : In2 + denote_remainder MR2 y)
         (f1 : encodes d1' -> encodes d1)
         (f2 : encodes d2' -> encodes d2) (a' : encodes d1')
         (b' : encodes d2'),
       d1' && f1 = bring_to_front MR1 x d1 ->
       d2' && f2 = bring_to_front MR2 y d2 ->
       a = f1 a' ->
       b = f2 b' ->
       SumPostRel RPostInv RPost d1' d2' a' b' ->
       InsertPostRel x y RPostInv RPost d1 d2 a b


bring_to_front_call_mrec:
  forall (t1 t2 : vtype) (R : call_frame) (MR : mfix_ctx)
    (v : denote_type t1) (xt : var (t1, t2) R) 
    (xR : var R MR),
  projT1
    (bring_to_front (denote_mfix_ctx MR) (denote_var xR)
       (projT1 (call_mrec xt xR v))) =
  inl (projT1 (call_mrec_call_frame xt v))
bring_to_front_call_mrec_neq:
  forall (t1 t2 : vtype) (R1 R2 : call_frame) (MR : mfix_ctx)
    (v : denote_type t1) (xt : var (t1, t2) R1) 
    (xR : var R1 MR) (yR : var R2 MR) (Hneq : var_neq xR yR),
  projT1
    (bring_to_front (denote_mfix_ctx MR) (denote_var yR)
       (projT1 (call_mrec xt xR v))) =
  inr
    (projT1
       (remove_denote' yR
          (projT1
             (call_mrec xt
                (remove_var R2 R1 MR yR xR (var_neq_sym xR yR Hneq)) v))))


remove_denote_encodes:
  forall (R : call_frame) (MR : mfix_ctx) (x : var R MR)
    (d : denote_remainder (denote_mfix_ctx MR) (denote_var x)),
  encodes d = encodes (projT1 (remove_denote x d))
d' ~= d ->
commute_remove_post_rel R d <->
R d


*)

Lemma insert_post_rel_call1 (MR : mfix_ctx) (R : call_frame) (xR : var R MR) :
  forall d1 d2 a b, 
  InsertPostRel (denote_var xR) (denote_var xR) (call_frame_post_equiv R) (commute_remove_post_rel (mfix_post_equiv (remove R MR xR)) ) d1 d2 a b -> True.
Proof.
  intros. dependent destruction H. dependent destruction H3.
  - subst. admit.
  - red in H3.
Admitted.

Lemma insert_post_rel_mfix_post_equiv_2 (MR : mfix_ctx) (R : call_frame) (xR : var R MR) : 
  forall d1 d2 a b, 
  InsertPostRel (denote_var xR) (denote_var xR) (call_frame_post_equiv R) (commute_remove_post_rel (mfix_post_equiv (remove R MR xR)) ) d1 d2 a b -> mfix_post_equiv MR d1 d2 a b.
Proof.
(*
  intros. 
  specialize (denote_mfix_exists _ d1) as [R1 [yR [t1 [t2 [y [v1 Hd1]]]]]].
  specialize (denote_mfix_exists _ d2) as [R2 [zR [t3 [t4 [z [v2 Hd2]]]]]].
  assert (R1 = R2). admit. subst.
  assert (yR = zR). admit. subst.
  assert (t1 = t3). admit. subst.
  assert (t2 = t4). admit. subst.
  assert (y = z). admit. subst.
  destruct (var_eq_neq _ _ _ xR zR).
  - rename v into Heq. apply var_eq_surj in Heq as HR. subst.
    apply var_eq_eq in Heq. subst xR.
    dependent destruction H.
    (* bring_to_front_call_mrec_neq *)
    specialize (bring_to_front_call_mrec _ _ _ _ v1 z zR) as Hcall1.
    specialize (bring_to_front_call_mrec _ _ _ _ v2 z zR) as Hcall2.
    rewrite <- H in Hcall1. rewrite <- H0 in Hcall2. simpl projT1 in Hcall1. simpl projT1 in Hcall2.
    subst.
    dependent destruction H3. cbn in f1. cbn in f2. revert H H0 H3.
    (* maybe should decompose into call_mrec_call_frame for these*)
    (* assert that both f1 and f2 are the id function*)
    (* in this case, use Heq to show that H is equiv to a prove of call_frame_post_equiv _ (call_mrec_call_frame z v2) *)
    admit.
  - (* these inductions are going to be hideous *) *) Admitted.
Lemma insert_post_rel_mfix_post_equiv_1 (MR : mfix_ctx) (R : call_frame) (xR : var R MR) : 
  forall d1 d2 a b, 
    mfix_post_equiv MR d1 d2 a b ->
  InsertPostRel (denote_var xR) (denote_var xR) (call_frame_post_equiv R) (commute_remove_post_rel (mfix_post_equiv (remove R MR xR)) ) d1 d2 a b.
Proof.
Admitted.
(*
  intros d1 d2.
  specialize (denote_mfix_exists _ d1) as [R1 [yR [t1 [t2 [y [v1 Hd1]]]]]].
  specialize (denote_mfix_exists _ d2) as [R2 [zR [t3 [t4 [z [v2 Hd2]]]]]].
  specialize (call_mrec_encodes t1 t2 R1 _ y yR v1) as Hy.
  rewrite <- Hd1 in Hy.
  (* maybe I should rewrite Insert in terms of this decomposition, or maybe just a proof that relates it to a similar def *)
  
  subst.

  (* I think a creative solution is warranted here *)
  induction xR.
  - intros. rewrite mfix_post_equiv_equation_2 in H.
    simpl denote_var.
    dependent destruction H.
    + econstructor.
    unfold commute_remove_post_rel. 
    econstructor.
    simpl remove. cbn.
    econstructor; eauto.
    dependent destruction H.
    + econstructor. auto.
    + constructor. red.
      setoid_rewrite remove_denote_equation_1.
      Transparent remove. cbn. Opaque remove. auto.
  - intros. rewrite mfix_pre_equiv_equation_2 in H. dependent destruction H. 
     { do 2 constructor; auto. }
     simpl denote_var. red. 
     eapply IHxR in H. red in H.
     dependent destruction H.
     + destruct 
         ((bring_to_front (denote_mfix_ctx l) (denote_var xR) b1))
         eqn : Heq1; cbn in x0; subst; try discriminate.
       unfold denote_mfix_ctx. simpl.
       rewrite bring_to_front_equation_5.
       setoid_rewrite Heq1.
       simpl.
       destruct 
         ((bring_to_front (denote_mfix_ctx l) (denote_var xR) b2))
         eqn : Heq2; cbn in x; subst; try discriminate.
       unfold denote_mfix_ctx. simpl.
       rewrite bring_to_front_equation_5.
       setoid_rewrite Heq2. constructor.
       auto.
     + destruct 
         ((bring_to_front (denote_mfix_ctx l) (denote_var xR) b1))
         eqn : Heq1; cbn in x0; subst; try discriminate.
       unfold denote_mfix_ctx. simpl.
       rewrite bring_to_front_equation_5.
       setoid_rewrite Heq1.
       simpl.
       destruct 
         ((bring_to_front (denote_mfix_ctx l) (denote_var xR) b2))
         eqn : Heq2; cbn in x; subst; try discriminate.
       unfold denote_mfix_ctx. simpl.
       rewrite bring_to_front_equation_5.
       setoid_rewrite Heq2.
       constructor.
       clear - H. red. Transparent remove_denote.
       red in H.
       simpl remove_denote.
       Transparent remove. simpl remove. simpl.
       destruct (remove_denote xR b0);
         destruct (remove_denote xR b3).
       constructor. auto.
Qed.
*)
