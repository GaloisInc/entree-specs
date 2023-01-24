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
Require Export MapEFacts.
Import List.ListNotations.
Open Scope list_scope.
From Equations Require Import Equations Signature.
Require Import Coq.Program.Equality.
Require Import ExtLib.Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.


Inductive list_rel {A} (R : Rel A A): Rel (list A) (list A) :=
  | list_rel_nil : list_rel R nil nil
  | list_rel_cons a b l1 l2 : R a b ->list_rel R l1 l2 -> list_rel R (cons a l1) (cons b l2).

Theorem transitive_list_rel A (R : Rel A A) : Transitive R -> Transitive (list_rel R).
Proof.
  intros HTrans l1 l2 l3. revert l1 l3. induction l2.
  - intros l1 l3 Hl12 Hl23. inversion Hl12. inversion Hl23. constructor.
  - intros l1 l3 Hl12 Hl23. inversion Hl12. subst. inversion Hl23. subst.
    econstructor; eauto.
Qed.


Equations types_equiv (t : type) : Rel (denote_type t) (denote_type t) := {
    types_equiv Nat := eq;
    types_equiv (Pair t1 t2) := prod_rel (types_equiv t1) (types_equiv t2);
    types_equiv (List t) := list_rel (types_equiv t);
    types_equiv (Arrow t1 MR t2) :=
    fun f g => forall x y, types_equiv t1 x y -> 
                   rutt (mfix_pre_equiv MR) (mfix_post_equiv MR) (types_equiv t2) (f x) (g y)
}
where mfix_pre_equiv (MR : mfix_ctx) : 
  Rel (denote_mrec_ctx (denote_mfix_ctx MR)) (denote_mrec_ctx (denote_mfix_ctx MR)) :=
{
  mfix_pre_equiv nil := fun _ _ => False;
  mfix_pre_equiv (cons cf MR) :=
    sum_rel (call_frame_pre_equiv cf) (mfix_pre_equiv MR);
}
where call_frame_pre_equiv (R : call_frame) :
  Rel (denote_call_frame R) (denote_call_frame R) := 
{
  call_frame_pre_equiv nil := fun _ _ => False;
  call_frame_pre_equiv (cons (t1,t2) R) :=
    sum_rel (types_equiv t1) (call_frame_pre_equiv R)
}
where mfix_post_equiv (MR : mfix_ctx) : 
  PostRel (denote_mrec_ctx (denote_mfix_ctx MR)) (denote_mrec_ctx (denote_mfix_ctx MR)) :=
{
  mfix_post_equiv nil := fun _ _ _ _ => False;
  mfix_post_equiv (cons cf MR) := SumPostRel (call_frame_post_equiv cf) (mfix_post_equiv MR);
}
where call_frame_post_equiv (R : call_frame) : 
  PostRel (denote_call_frame R) (denote_call_frame R) :=
{
  call_frame_post_equiv nil := fun _ _ _ _ => False;
  call_frame_post_equiv (cons (t1,t2) R) :=
    SumPostRel (fun _ _ => types_equiv t2) (call_frame_post_equiv R);
}.
(* use to create relations for [Γ] -> mtree [MR] [t] *)

Fixpoint ctx_equiv (Γ : ctx) : Rel (denote_ctx Γ) (denote_ctx Γ) :=
  match Γ with
  | nil => fun _ _ => True
  | cons t Γ => prod_rel (types_equiv t) (ctx_equiv Γ)
  end.

Definition comp_equiv_rutt {t MR} t1 t2 :=
  rutt (mfix_pre_equiv MR) (mfix_post_equiv MR) (types_equiv t) t1 t2.

Definition comp_equiv {t Γ MR} :=
    fun c1 c2 => forall hyps1 hyps2, ctx_equiv Γ hyps1 hyps2 ->
              comp_equiv_rutt (t := t) (MR := MR) (c1 hyps1) (c2 hyps2).

Definition mfix_bodies_equiv {Γ MR R} :=
  fun bodies1 bodies2 => forall hyps1 hyps2 arg1 arg2, 
      ctx_equiv Γ hyps1 hyps2 -> call_frame_pre_equiv R arg1 arg2 ->
       rutt (mfix_pre_equiv MR) (mfix_post_equiv MR) (call_frame_post_equiv R arg1 arg2)  (bodies1 hyps1 arg1) (bodies2 hyps2 arg2).

Lemma mfix_pre_call_mrec:
    forall (t1 t2 : vtype) (MR : mfix_ctx) (R : call_frame) (xR : var R MR) 
           (x : var (t1, t2) R) (r1 r2 : denote_type t1) (c1 : denote_mrec_ctx (denote_mfix_ctx MR))
           (f1 : encodes c1 -> denote_type t2) (c2 : denote_mrec_ctx (denote_mfix_ctx MR))
           (f2 : encodes c2 -> denote_type t2),
      types_equiv t1 r1 r2 ->
      call_mrec x xR r1 = c1 && f1 -> call_mrec x xR r2 = c2 && f2 -> mfix_pre_equiv MR c1 c2.
Proof.
  intros t1 t2 MR R xR x r1 r2 c1 f1 c2 f2.
  dependent induction xR.
  - simp call_mrec. intros. rewrite mfix_pre_equiv_equation_2.
    destruct (call_mrec_call_frame x r1) as [d1 g1] eqn : Heq1.
    destruct (call_mrec_call_frame x r2) as [d2 g2] eqn : Heq2.
    inversion H1. subst. inversion H0. subst. constructor.
    rename a into R. revert Heq1 Heq2 H. clear H0 H1.
    dependent induction x.
    + simp call_mrec_call_frame. intros.
      inversion Heq1. inversion Heq2. subst. constructor. auto.
    + destruct b as [t3 t4]. simp call_mrec_call_frame.
      rewrite call_frame_pre_equiv_equation_2. intros.
      destruct (call_mrec_call_frame x r1) as [d3 g3] eqn : Heq3.
      destruct (call_mrec_call_frame x r2) as [d4 g4] eqn : Heq4.
      inversion Heq1. inversion Heq2. subst. constructor.
      eapply IHx; eauto.
  - simp call_mrec. intros. rewrite mfix_pre_equiv_equation_2.
    destruct (call_mrec x xR r1) as [d1 g1] eqn : Heq1.
    destruct (call_mrec x xR r2) as [d2 g2] eqn : Heq2.
    specialize (IHxR x r1 r2 d1 g1 d2 g2 H Heq1 Heq2).
    inversion H0. inversion H1. constructor. auto.
Qed.

Lemma mfix_post_equiv_types_equiv_aux:
  forall (t1 t2 : vtype) (MR : mfix_ctx) (R : call_frame) (xR : var R MR) 
    (x : var (t1, t2) R) (r1 r2 : denote_type t1) (c1 : denote_mrec_ctx (denote_mfix_ctx MR))
    (f1 : encodes c1 -> denote_type t2),
    call_mrec x xR r1 = c1 && f1 ->
    forall (c2 : denote_mrec_ctx (denote_mfix_ctx MR)) (f2 : encodes c2 -> denote_type t2),
      call_mrec x xR r2 = c2 && f2 ->
      encodes c1 = denote_type t2 ->
      encodes c2 = denote_type t2 ->
      f1 ~= @id (denote_type t2) ->
      f2 ~= @id (denote_type t2) ->
      forall (a : encodes c1) (b : encodes c2),
        mfix_post_equiv MR c1 c2 a b -> types_equiv t2 (f1 a) (f2 b).
Proof.
  intros t1 t2 MR R xR x r1 r2 c1 f1 Heq1 c2 f2 Heq2 Henc1 Henc2 Hcont1 Hcont2 a b Hab.
  dependent induction xR.
  - rewrite mfix_post_equiv_equation_2 in Hab.
    simp call_mrec in Heq1, Heq2.
    destruct (call_mrec_call_frame x r1) as [d1 g1] eqn : Heq3.
    destruct (call_mrec_call_frame x r2) as [d2 g2] eqn : Heq4.
    inversion Heq1. inversion Heq2. subst.
    apply Eqdep.EqdepTheory.inj_pair2 in Heq1, Heq2. subst.
    dependent destruction Hab.
    dependent induction x.
    + rewrite call_frame_post_equiv_equation_2 in H3.
      simp call_mrec_call_frame in Heq3, Heq4.
      inversion Heq3. inversion Heq4. subst.
      dependent destruction H3. cbn in f1, f2.
      unfold inout_encoded in f1, f2. apply JMeq_eq in Hcont1, Hcont2.
      subst. auto.
    + destruct b. rewrite call_frame_post_equiv_equation_2 in H3.
      simp call_mrec_call_frame in Heq3, Heq4.
      inversion Heq3. inversion Heq4. subst.
      destruct (call_mrec_call_frame x r1) as [d1' g1'] eqn : Heq5.
      destruct (call_mrec_call_frame x r2) as [d2' g2'] eqn : Heq6.
      inversion H0. inversion H1. subst.
      dependent destruction H3.
      apply Eqdep.EqdepTheory.inj_pair2 in H0, H1. subst.
      eapply IHx; eauto.
  - rewrite mfix_post_equiv_equation_2 in Hab.
    simp call_mrec in Heq1, Heq2.
    destruct (call_mrec x xR r1) as [d1 g1] eqn : Heq3.
    destruct (call_mrec x xR r2) as [d2 g2] eqn : Heq4.
    inversion Heq1. inversion Heq2.
    subst. dependent destruction Hab.
    apply Eqdep.EqdepTheory.inj_pair2 in Heq1, Heq2.
    subst.
    eapply IHxR in H3; eauto.
Qed.

Lemma mfix_post_equiv_types_equiv:
  forall (t1 t2 : vtype) (MR : mfix_ctx) (R : call_frame) (xR : var R MR) 
    (x : var (t1, t2) R) (r1 r2 : denote_type t1) (c1 : denote_mrec_ctx (denote_mfix_ctx MR))
    (f1 : encodes c1 -> denote_type t2),
    call_mrec x xR r1 = c1 && f1 ->
    forall (c2 : denote_mrec_ctx (denote_mfix_ctx MR)) (f2 : encodes c2 -> denote_type t2),
      call_mrec x xR r2 = c2 && f2 ->
      forall (a : encodes c1) (b : encodes c2),
        mfix_post_equiv MR c1 c2 a b -> types_equiv t2 (f1 a) (f2 b).
Proof.
  intros. eapply mfix_post_equiv_types_equiv_aux; eauto.
  - specialize (call_mrec_encodes _ _ _ _ x xR r1) as Henc1. rewrite <- Henc1.
    rewrite H. auto.
  - specialize (call_mrec_encodes _ _ _ _ x xR r2) as Henc2. rewrite <- Henc2.
    rewrite H0. auto.
  - specialize (call_mrec_cont _ _ _ _ x xR r1) as Hcont1. rewrite H in Hcont1.
    auto.
  - specialize (call_mrec_cont _ _ _ _ x xR r2) as Hcont2. rewrite H0 in Hcont2.
    auto.
Qed.

Lemma comp_equiv_call (t1 t2 : type) Γ MR R (xR : var R MR) (x : var (t1,t2) R) 
      (v1 v2 : value t1 Γ): 
  comp_equiv (MR := MR) (denote_value v1) (denote_value v2) ->
  comp_equiv (denote_comp (comp_call xR x v1)) (denote_comp (comp_call xR x v2)).
Proof.
  intros. red. unfold comp_equiv_rutt. intros.
  simp denote_comp.
  eapply rutt_bind; eauto.
  intros. eapply H; auto.
  unfold call_term. intros.
  destruct (call_mrec x xR r1) as [c1 f1] eqn : Heq1.
  destruct (call_mrec x xR r2) as [c2 f2] eqn : Heq2. 
  setoid_rewrite bind_trigger. apply rutt_Vis.
  eapply mfix_pre_call_mrec; eauto.
  intros. apply rutt_Ret. eapply mfix_post_equiv_types_equiv; eauto.
Qed.


Lemma pre_equiv_sum_rel MR R : 
  eq_rel (mfix_pre_equiv (R :: MR)) (sum_rel (call_frame_pre_equiv R) (mfix_pre_equiv MR)).
Proof.
  rewrite mfix_pre_equiv_equation_2.
  intros. reflexivity.
Qed.

Lemma post_equiv_sum_post_rel MR R : 
  PostRelEq  (mfix_post_equiv (R :: MR)) (SumPostRel (call_frame_post_equiv R) (mfix_post_equiv MR)).
Proof.
  rewrite mfix_post_equiv_equation_2.
  intros. reflexivity.
Qed.

Lemma types_equiv_sym_prod : (forall t, Symmetric (types_equiv t)) /\ 
                          (forall MR, Symmetric (mfix_pre_equiv MR) /\ SymmetricPostRel (mfix_post_equiv MR) ) /\
                          (forall R, Symmetric (call_frame_pre_equiv R) /\ SymmetricPostRel (call_frame_post_equiv R)).
Proof.
  eapply type_mfix_mutind; intros; simp types_equiv.
  - auto.
  - intros l1 l2 Hl. induction Hl. constructor. econstructor; eauto.
  - repeat intro. destruct H1. constructor; auto.
  - intros f g Hfg x y Hxy. destruct H0. apply rutt_sym; auto.
  - split; repeat intro; contradiction.
  - destruct H. destruct H0. split.
    + repeat intro. inversion H3; constructor; auto.
    + repeat intro. dependent destruction H3; constructor; auto.
  - cbn. split; repeat intro; contradiction.
  - destruct H1. split; repeat intro.
    + dependent destruction H3; constructor; auto.
    + dependent destruction H3; constructor; auto.
Qed.

#[global] Instance types_equiv_sym : forall t : type, Symmetric (types_equiv t).
Proof.
  destruct types_equiv_sym_prod; auto.
Qed.

Lemma types_equiv_trans_prod : (forall t, Transitive (types_equiv t)) /\ 
                          (forall MR, Transitive (mfix_pre_equiv MR) /\ TransitivePostRel (mfix_pre_equiv MR) (mfix_post_equiv MR) ) /\
                          (forall R, Transitive (call_frame_pre_equiv R) /\ 
                                  TransitivePostRel (call_frame_pre_equiv R) (call_frame_post_equiv R)).
Proof.
  eapply type_mfix_mutind; intros; simp types_equiv.
  - repeat intro; subst; auto.
  - apply transitive_list_rel. auto. 
  - repeat intro. dependent destruction H1. dependent destruction H2.
    constructor; eauto.
  - intros f g h Hfg Hgh x y Hxy.
    destruct H0.
    eapply rutt_trans'; eauto.
    apply Hgh. transitivity x; auto. symmetry. auto.
  - split; repeat intro; contradiction.
  - destruct H. destruct H0. split; repeat intro.
    + dependent destruction H3; dependent destruction H4; constructor; eauto.
    + dependent destruction H4; dependent destruction H5; dependent destruction H3.
      * eapply H1 in H3; eauto. specialize (H3 a2 H4 H5). destruct H3 as [b [Hb1 Hb2] ].
           exists b. split; constructor; auto.
      * eapply H2 in H3; eauto. specialize (H3 b2 H4 H5). destruct H3 as [b [Hb1 Hb2]].
           exists b. split; constructor; auto.
  - split; repeat intro; contradiction.
  - destruct H1. split; repeat intro.
    + dependent destruction H3; dependent destruction H4; constructor; auto; etransitivity; eauto.
    + dependent destruction H4; dependent destruction H5; dependent destruction H3.
      * exists c. split; constructor; auto. transitivity a; eauto. symmetry. auto.
      * eapply H2 in H3; eauto. specialize (H3 b2 H4 H5). destruct H3 as [b [Hb1 Hb2]].
        exists b. split; constructor; eauto.
Qed.

#[global] Instance types_equiv_trans : forall t : type, Transitive (types_equiv t).
Proof.
  destruct types_equiv_trans_prod. auto.
Qed.

#[global] Instance comp_equiv_rutt_trans : forall t MR, Transitive (@comp_equiv_rutt t MR).
Proof.
  intros t MR. red. intros t1 t2 t3 Ht12 Ht23.
  destruct types_equiv_trans_prod as [? [? ?]].
  specialize (H0 MR) as [? ?].
  eapply rutt_trans'; eauto.
Qed.
#[global] Instance comp_equiv_rutt_sym : forall t MR, Symmetric (@comp_equiv_rutt t MR).
Proof.
  intros t MR. red. intros t1 t2 Ht12.
  destruct (types_equiv_sym_prod) as [? [? ?]].
  specialize (H0 MR) as [? ?].
  apply rutt_sym; auto.
Qed.

Lemma types_equiv_index_ctx:
  forall (t : vtype) (Γ : ctx) (x : var t Γ) (hyps1 hyps2 : denote_ctx Γ),
    ctx_equiv Γ hyps1 hyps2 -> types_equiv t (index_ctx x hyps1) (index_ctx x hyps2).
Proof.
  intros t Γ x. dependent induction x.
  - intros. destruct hyps1; destruct hyps2. simp index_ctx.
    red in H. destruct H. auto.
  - intros. destruct hyps1; destruct hyps2. simp index_ctx. apply IHx.
    red in H. destruct H. auto.
Qed.
Arguments lift_handler (MR1) {MR2}.

Lemma mfix_pre_equiv_lift_handler:
  forall (MR1 MR2 : mfix_ctx) (e1 e2 : denote_mrec_ctx (denote_mfix_ctx MR2)),
    mfix_pre_equiv MR2 e1 e2 -> map_rel (lift_handler _) (lift_handler _) (mfix_pre_equiv (MR1 ++ MR2)) e1 e2.
Proof.
  intros MR1 MR2. unfold map_rel. revert MR2. induction MR1.
  - intros. auto.
  - setoid_rewrite lift_handler_equation_2. intros MR2 e1 e2 He12.
    apply IHMR1 in He12. destruct (lift_handler MR1 e1). destruct (lift_handler MR1 e2).
    constructor. auto.
Qed.

Lemma mfix_post_equiv_lift_handler:
  forall (MR1 MR2 : mfix_ctx) (e1 e2 : denote_mrec_ctx (denote_mfix_ctx MR2)) 
    (a : encodes e1) (b : encodes e2),
    map_post_rel (lift_handler MR1) (lift_handler MR1) (mfix_post_equiv (MR1 ++ MR2)) e1 e2 a b ->
    mfix_post_equiv MR2 e1 e2 a b.
Proof.
  intros MR1 MR2. unfold map_post_rel. revert MR2. induction MR1.
  - repeat setoid_rewrite lift_handler_equation_1. intros.
    decompose record H. subst. auto.
  - repeat setoid_rewrite lift_handler_equation_2. intros.
    specialize (IHMR1 MR2 e1 e2 a0 b). simp lift_handler in H.
    destruct (lift_handler MR1 e1). destruct (lift_handler MR1 e2).
    apply IHMR1. decompose record H. subst. eexists. eexists.
    repeat split; eauto.
    simpl app in H3. rewrite mfix_post_equiv_equation_2 in H3.
    dependent destruction H3. auto.
Qed.

Lemma perm_nil_cons1:
  forall A (l : list A), perm [] l -> l = [].
Proof.
  intros A l Hperm. dependent induction Hperm; eauto.
Qed.

Lemma perm_nil_cons2:
  forall A (l : list A), perm l [] -> l = [].
Proof.
  intros A l Hperm. dependent induction Hperm; eauto.
Qed.

Lemma perm_nil_cons1': 
  forall A (a : A) (t : list A), perm [] (a :: t) -> False.
Proof.
  intros. apply perm_nil_cons1 in X. discriminate.
Qed.

Lemma perm_nil_cons2' :
  forall A (a : A) (t : list A), perm (a :: t) [] -> False.
Proof.
  intros. apply perm_nil_cons2 in X. discriminate.
Qed.

Lemma unfold_denote_mfix_ctx R MR : 
  denote_mfix_ctx (R :: MR) = (denote_call_frame R && encodes_call_frame R) :: denote_mfix_ctx MR.
Proof. reflexivity. Qed.
Transparent perm_map.
Lemma mfix_pre_equiv_perm_handler:
  forall (MR1 MR2 : mfix_ctx) (Hperm : perm MR1 MR2) (e1 e2 : denote_mrec_ctx (denote_mfix_ctx MR1)),
    mfix_pre_equiv MR1 e1 e2 ->
    map_rel (perm_handler (denote_mfix_ctx MR1) (denote_mfix_ctx MR2) (perm_denote Hperm))
            (perm_handler (denote_mfix_ctx MR1) (denote_mfix_ctx MR2) (perm_denote Hperm))
            (mfix_pre_equiv MR2) e1 e2.
Proof.
  intros MR1 MR2 Hperm. unfold map_rel. dependent induction Hperm.
  - intros. contradiction.
  - intros. rewrite mfix_pre_equiv_equation_2 in H. dependent destruction H.
    + simp perm_handler. unfold perm_denote. repeat simp perm_map.
      simpl perm_map. simp perm_handler.
      setoid_rewrite perm_handler_equation_5. constructor; auto.
    + unfold perm_denote. simpl perm_map.
      apply IHHperm in H. rewrite mfix_pre_equiv_equation_2. simpl List.map.
      destruct (perm_handler (denote_mfix_ctx l1) (denote_mfix_ctx l2) (perm_denote Hperm) b1)
        eqn : Heq1;
      destruct (perm_handler (denote_mfix_ctx l1) (denote_mfix_ctx l2) (perm_denote Hperm) b2)
        eqn : Heq2. cbn in H.
      setoid_rewrite perm_handler_equation_6; setoid_rewrite Heq1; setoid_rewrite Heq2.
      constructor; auto.
 - repeat rewrite mfix_pre_equiv_equation_2. intros e1 e2 He12.
   dependent destruction He12. 2 : dependent destruction H.
   + unfold perm_denote. simpl perm_map. 
     setoid_rewrite perm_handler_equation_7. repeat constructor. auto.
   + unfold perm_denote. simpl perm_map. setoid_rewrite perm_handler_equation_8.
     constructor. auto.
   + unfold perm_denote. simpl perm_map. 
     apply IHHperm in H.
     destruct (perm_handler (denote_mfix_ctx l1) (denote_mfix_ctx l2) (perm_denote Hperm) b1)
              eqn : Heq1;
     destruct (perm_handler (denote_mfix_ctx l1) (denote_mfix_ctx l2) (perm_denote Hperm) b2)
              eqn : Heq2. cbn in H.
     setoid_rewrite perm_handler_equation_9; setoid_rewrite Heq1; setoid_rewrite Heq2.
     repeat constructor. auto.
 - intros e1 e2 He12. unfold perm_denote. simpl perm_map.
   apply IHHperm1 in He12.
   destruct (perm_handler (denote_mfix_ctx l1) (denote_mfix_ctx l2) (perm_denote Hperm1) e1)
     eqn : Heq1;
   destruct (perm_handler (denote_mfix_ctx l1) (denote_mfix_ctx l2) (perm_denote Hperm1) e2)
     eqn : Heq2. cbn in He12.
   (* might be worth rethinking the whole mapE handler thing 
      of using equations to do weird safe typecasts,

      or perhaps think carefully about how this might be refactored into two more normal lemmas
    *)
   destruct l1; destruct l3.
   + cbv in e1. contradiction. 
   + exfalso. clear - Hperm1 Hperm2. eapply perm_nil_cons1'.
     eapply perm_trans; eauto.
   + exfalso. clear - Hperm1 Hperm2. eapply perm_nil_cons2'.
     eapply perm_trans; eauto.
   + specialize (IHHperm2 x x0 He12). specialize (IHHperm1 e1 e2).
     setoid_rewrite perm_handler_equation_10; setoid_rewrite Heq1; setoid_rewrite Heq2.
     destruct (perm_handler (denote_mfix_ctx l2) (denote_mfix_ctx (l0 :: l3))
                     (perm_denote Hperm2) x) eqn : Heq3.
     destruct ((perm_handler (denote_mfix_ctx l2) (denote_mfix_ctx (l0 :: l3))
                     (perm_denote Hperm2) x0)) eqn : Heq4.
     setoid_rewrite Heq3. setoid_rewrite Heq4.
     simpl projT1. auto.
Qed.
#[local] Instance eq_sub_eq {A} : subrelation (@eq A) eq.
Proof.
  repeat intro. auto.
Qed.
(*
#[local] Instance eq_sub_impl {A : Prop} : subrelation (@eq A) (@impl A).
*)
Lemma mfix_post_equiv_perm_handler:
  forall (MR1 MR2 : mfix_ctx) (Hperm : perm MR1 MR2) (e1 e2 : denote_mrec_ctx (denote_mfix_ctx MR1))
    (a : encodes e1) (b : encodes e2),
    map_post_rel (perm_handler (denote_mfix_ctx MR1) (denote_mfix_ctx MR2) (perm_denote Hperm))
                 (perm_handler (denote_mfix_ctx MR1) (denote_mfix_ctx MR2) (perm_denote Hperm))
                 (mfix_post_equiv MR2) e1 e2 a b -> mfix_post_equiv MR1 e1 e2 a b.
Proof.
  intros MR1 MR2 Hperm. unfold map_post_rel. dependent induction Hperm.
  - intros. contradiction.
  - unfold perm_denote. simpl perm_map.
    intros. simp perm_handler in H.
    destruct e1; destruct e2.
    + cbn in H. repeat rewrite perm_handler_equation_5 in H.
      destruct H as [a' [b' [Ha' [Hb' H] ] ] ].
      subst. dependent destruction H. constructor; eauto.
    + match goal with
      | H : let 'd' && f1 := ?x in _ |- _ => destruct x eqn : Heq1 end.
      match goal with
      | H : let 'd' && f1 := ?x in _ |- _ => destruct x eqn : Heq2 end.
      setoid_rewrite perm_handler_equation_5 in Heq1.
      setoid_rewrite perm_handler_equation_6 in Heq2.
      match goal with
      | H : (let 'd' && f1 := ?x in _) = _ |- _ => destruct x end.
      injection Heq1. injection Heq2. intros. subst.
      decompose record H. rewrite mfix_post_equiv_equation_2 in H4. dependent destruction H4.
    + match goal with
      | H : let 'd' && f1 := ?x in _ |- _ => destruct x eqn : Heq1 end.
      match goal with
      | H : let 'd' && f1 := ?x in _ |- _ => destruct x eqn : Heq2 end.
      setoid_rewrite perm_handler_equation_5 in Heq2.
      setoid_rewrite perm_handler_equation_6 in Heq1.
      match goal with
      | H : (let 'd' && f1 := ?x in _) = _ |- _ => destruct x end.
      injection Heq1. injection Heq2. intros. subst.
      decompose record H. rewrite mfix_post_equiv_equation_2 in H4. dependent destruction H4.
    + match goal with
      | H : let 'd' && f1 := ?x in _ |- _ => destruct x eqn : Heq1 end.
      match goal with
      | H : let 'd' && f1 := ?x in _ |- _ => destruct x eqn : Heq2 end.
      setoid_rewrite perm_handler_equation_6 in Heq1.
      setoid_rewrite perm_handler_equation_6 in Heq2.
      match goal with
      | H : (let 'd' && f1 := ?x in _) = _ |- _ => destruct x eqn : Heq3 end.
      match goal with
      | H : (let 'd' && f1 := ?x in _) = _ |- _ => destruct x eqn : Heq4 end.
      destruct H as [a' [b' [Ha' [Hb' H] ] ]].
      subst. rewrite mfix_post_equiv_equation_2.
      constructor. 
      specialize (IHHperm d d0 (e a') (e0 b')).
      setoid_rewrite Heq4 in IHHperm. setoid_rewrite Heq3 in IHHperm.
      apply IHHperm. injection Heq2. intros. subst. injection Heq1.
      intros. subst. inj_existT. subst.
      exists a'. exists b'. do 2 split; auto. rewrite mfix_post_equiv_equation_2 in H. 
      dependent destruction H. auto.
  - (* the rest, unfortunately will likely be similarly painful come back to this
       on monday *)
    intros e1 e2 a b He12.
    match goal with
      | H : let 'd' && f1 := ?x in _ |- _ => destruct x eqn : Heq1 end.
    match goal with
      | H : let 'd' && f1 := ?x in _ |- _ => destruct x eqn : Heq2 end.
    destruct He12 as [a' [b' [Ha' [Hb' H]] ]]. subst.
    unfold perm_denote in Heq1, Heq2. simpl perm_map in Heq1, Heq2.
    repeat rewrite mfix_post_equiv_equation_2 in H.
    repeat destruct e1 as [e1 | e1].
    + setoid_rewrite perm_handler_equation_7 in Heq1. injection Heq1. intros. subst.
      inj_existT. subst.
      repeat dependent destruction H.
      repeat destruct e2 as [e2 | e2].
      * setoid_rewrite perm_handler_equation_7 in Heq2. injection Heq2.
        intros. subst. inj_existT. subst. constructor; auto.
      * setoid_rewrite perm_handler_equation_8 in Heq2. discriminate.
      * setoid_rewrite perm_handler_equation_9 in Heq2. 
        match goal with
        | H : (let 'd' && f1 := ?x in _) = _ |- _ => destruct x; discriminate end.
    + setoid_rewrite perm_handler_equation_8 in Heq1. injection Heq1.
      intros. subst. inj_existT. subst.
      dependent destruction H.
      repeat destruct e2 as [e2 | e2].
      * setoid_rewrite perm_handler_equation_7 in Heq2; discriminate.
      * setoid_rewrite perm_handler_equation_8 in Heq2. injection Heq2.
        intros. subst. inj_existT. subst.
        repeat constructor; auto.
      * setoid_rewrite perm_handler_equation_9 in Heq2.
         match goal with
        | H : (let 'd' && f1 := ?x in _) = _ |- _ => destruct x; discriminate end.
    + setoid_rewrite perm_handler_equation_9 in Heq1.
      match goal with
      | H : (let 'd' && f1 := ?x in _) = _ |- _ => destruct x eqn : Heq3 end.
      injection Heq1. intros. subst. inj_existT. subst.
      repeat dependent destruction H.
      repeat destruct e2 as [e2 | e2].
      * clear Heq3. setoid_rewrite perm_handler_equation_7 in Heq2.
        discriminate.
      * clear Heq3. setoid_rewrite perm_handler_equation_8 in Heq2.
        discriminate.
      * setoid_rewrite perm_handler_equation_9 in Heq2.
        match goal with
        | H : (let 'd' && f1 := ?x in _) = _ |- _ => destruct x eqn : Heq4 end.
        specialize (IHHperm e1 e2 (e a') (e0 b')).
        setoid_rewrite Heq3 in IHHperm. setoid_rewrite Heq4 in IHHperm.
        repeat rewrite mfix_post_equiv_equation_2.
        repeat constructor. apply IHHperm.
        injection Heq2. intros. subst. inj_existT. subst.
        exists a'. exists b'. repeat split; auto.
  - intros e1 e2 a b. unfold perm_denote. simpl perm_map. intros IHe12.
    apply IHHperm1. clear IHHperm1.
    match goal with
      | |- let 'd' && f1 := ?x in _ => destruct x eqn : Heq1 end.
      match goal with
      | |- let 'd' && f1 := ?x in _ => destruct x eqn : Heq2 end.
    match goal with
      | H : (let 'd' && f1 := ?x in _) |- _ => destruct x eqn : Heq3 end.
    match goal with
      | H : (let 'd' && f1 := ?x in _) |- _ => destruct x eqn : Heq4 end.
    destruct l1; destruct l3; try contradiction.
    setoid_rewrite perm_handler_equation_10 in Heq3.
    setoid_rewrite perm_handler_equation_10 in Heq4.
    destruct IHe12 as [a' [b' [Ha' [Hb' H] ] ] ].
    subst. rewrite mfix_post_equiv_equation_2 in H.
    setoid_rewrite Heq1 in Heq3. setoid_rewrite Heq2 in Heq4.
    dependent destruction H.
    * match goal with
      | H : (let 'd' && f1 := ?x in _) = _ |- _ => destruct x eqn : Heq5 end.
      match goal with
      | H : (let 'd' && f1 := ?x in _) = _ |- _ => destruct x eqn : Heq6 end.
      injection Heq4. intros. subst. inj_existT. subst.
      injection Heq3. intros. subst. inj_existT. subst.
      exists (e8 a). exists (e7 b). repeat split; auto.
      eapply IHHperm2. clear H0 H1.
      match goal with
      | |- let 'd' && f1 := ?x in _ => destruct x eqn : Heq7 end.
      match goal with
      | |- let 'd' && f1 := ?x in _ => destruct x eqn : Heq8 end.
      setoid_rewrite Heq8 in Heq5. setoid_rewrite Heq7 in Heq6.
      injection Heq5. injection Heq6. intros. subst. inj_existT.
      subst. exists a. exists b. repeat split; auto. constructor; auto.
    * match goal with
      | H : (let 'd' && f1 := ?x in _) = _ |- _ => destruct x eqn : Heq5 end.
      match goal with
      | H : (let 'd' && f1 := ?x in _) = _ |- _ => destruct x eqn : Heq6 end.
      injection Heq4. intros. subst. inj_existT. subst.
      injection Heq3. intros. subst. inj_existT. subst.
      clear H0 H1. exists (e6 a). exists (e5 b). repeat split; auto.
      eapply IHHperm2.
      match goal with
      | |- let 'd' && f1 := ?x in _ => destruct x eqn : Heq7 end.
      match goal with
      | |- let 'd' && f1 := ?x in _ => destruct x eqn : Heq8 end.
      setoid_rewrite Heq8 in Heq5. setoid_rewrite Heq7 in Heq6.
      injection Heq6. injection Heq5. intros. subst. inj_existT. subst.
      exists a. exists b. repeat split; auto. constructor; auto.
Qed.

Lemma types_equiv_comp_refl_prod : 
  (forall t Γ MR (c : comp t Γ MR), comp_equiv (denote_comp c) (denote_comp c)) /\
  (forall t Γ (v : value t Γ), forall MR, comp_equiv (MR := MR) (denote_value v) (denote_value v)) /\
    (forall Γ MR R R' (bodies : mfix_bodies Γ MR R R'), mfix_bodies_equiv (denote_bodies bodies) (denote_bodies bodies)).
Proof.
  unfold comp_equiv, comp_equiv_rutt.
  apply comp_value_mutind.
  - repeat intro. do 2 rewrite denote_value_equation_1. apply rutt_Ret. simp types_equiv. auto.
  - repeat intro. do 2 rewrite denote_value_equation_2. apply rutt_Ret. simp types_equiv. constructor.
  - intros t Γ vh Hhv vt Hvt MR. specialize (Hhv MR). specialize (Hvt MR).
    intros hyps1 hyps2 Hhyps. setoid_rewrite denote_value_equation_3.
    eapply rutt_bind; eauto; intros. eapply rutt_bind; eauto. intros. apply rutt_Ret.
    simp types_equiv. constructor; auto.
  - intros t1 t2 Γ v1 Hv1 v2 Hv2 MR hyps1 hyps2 Hhyps. setoid_rewrite denote_value_equation_4.
    eapply rutt_bind; try eapply Hv1; eauto. intros. eapply rutt_bind; try eapply Hv2; eauto.
    intros. apply rutt_Ret. constructor; auto.
  - intros t1 t2 Γ MR cbody Hcbody MR' hyps1 hyps2 Hhyps. setoid_rewrite denote_value_equation_5.
    apply rutt_Ret. simp types_equiv. intros. apply Hcbody. split; auto.
  - intros t Γ x MR hyps1 hyps2 Hhyps. setoid_rewrite denote_value_equation_6.
    apply rutt_Ret. apply types_equiv_index_ctx; auto.
  - repeat intro. simp denote_comp.
  - intros t1 t2 Γ MR c1 Hc1 c2 Hc2 hyps1 hyps2 Hhyps.
    simp denote_comp. eapply rutt_bind; eauto. intros. eapply Hc2. split; auto.
  - intros ? ? ? ? Hvn ? HcZ ? HcS ? ? ?. simp denote_comp.
    eapply rutt_bind; try eapply Hvn; eauto. intros n1 n2 Hn12. simp types_equiv in Hn12. subst.
    destruct n2; eauto. eapply HcS. split; auto. reflexivity.
  - intros ? ? ? ? ? Hvl ? Hcnil ? Hccons ? ? ?. simp denote_comp.
    eapply rutt_bind; try eapply Hvl; eauto. intros l1 l2 Hl12. simp types_equiv in Hl12.
    dependent destruction Hl12; eauto. eapply Hccons. do 2 (split; auto).
  - intros ? ? ? ? ? ? Hvp ? Hes ? ? ?. simp denote_comp.
    eapply rutt_bind; try apply Hvp; auto. intros. simp types_equiv in H0.
    dependent destruction H0. destruct r1. destruct r2. cbn in *.
    apply Hes. repeat (split; auto).
  - intros ? ? ? ? ? Hvf ? Hvarg ? ? ?. simp denote_comp.
    eapply rutt_bind; try apply Hvf; auto. intros f g Hfg.
    eapply rutt_bind. apply Hvarg; auto. exact Hfg.
  - intros. apply comp_equiv_call. repeat intro. eapply H. auto. auto.
  - intros t Γ MR R bodies Hbodies c Hc hyps1 hyps2 Hhyps.
    simp denote_comp. 
    eapply interp_mrec_rutt with (RPreInv := call_frame_pre_equiv R) (RPostInv := call_frame_post_equiv R). 
    intros. eapply Hbodies; eauto.
    apply Hc. auto.
  - intros t Γ MR1 MR2 c Hc hyps1 hyps2 Hhyps. simp denote_comp. apply mapE_rutt.
    eapply rutt_mon; try eapply Hc; eauto. apply mfix_pre_equiv_lift_handler.
    apply mfix_post_equiv_lift_handler.
  - intros t Γ MR1 MR2 Hperm c Hc hyps1 hyps2 Hhyps. simp denote_comp. apply mapE_rutt.
    eapply rutt_mon; try apply Hc; eauto.
    apply mfix_pre_equiv_perm_handler.
    apply mfix_post_equiv_perm_handler.  
  - repeat intro. simp denote_bodies. inversion arg1.
  - intros Γ MR t1 t2 R R' body Hbody bodies Hbodies hyps1 hyps2 args1 args2 Hhyps Hargs.
    rewrite call_frame_pre_equiv_equation_2 in Hargs. dependent destruction Hargs.
    + setoid_rewrite denote_bodies_equation_2. red in Hbody.
      eapply rutt_mon; try eapply Hbody; eauto.
      * intros. constructor. auto.
      * split; auto.
    + setoid_rewrite denote_bodies_equation_3. eapply rutt_mon; try eapply Hbodies; eauto.
      intros. constructor. auto.
Qed.

Theorem types_equiv_comp_refl : forall t Γ MR (c : comp t Γ MR), comp_equiv (denote_comp c) (denote_comp c).
Proof. destruct types_equiv_comp_refl_prod as [? [? ?]]; auto. Qed.

Theorem types_equiv_value_refl : forall t Γ MR (v : value t Γ), comp_equiv (MR := MR) (denote_value v) (denote_value v).
Proof. destruct types_equiv_comp_refl_prod as [? [? ?]]; intros; auto. Qed.

Theorem types_equiv_mfix_bodies_refl : forall Γ MR R R' (bodies : mfix_bodies Γ MR R R'), mfix_bodies_equiv (denote_bodies bodies) (denote_bodies bodies).
Proof. destruct types_equiv_comp_refl_prod as [? [? ?]]; intros; auto. Qed.

#[global] Instance ctx_equiv_sym Γ : Symmetric (ctx_equiv Γ).
Proof.
  red. induction Γ.
  - intros. auto.
  - intros. simpl ctx_equiv in *. dependent destruction H.
    constructor; auto. symmetry. auto.
Qed.

#[global] Instance ctx_equiv_trans Γ : Transitive (ctx_equiv Γ).
Proof.
  red. induction Γ.
  - intros. auto.
  - intros. simpl ctx_equiv in *. dependent destruction H.
    dependent destruction H0. constructor; eauto.
    etransitivity; eauto.
Qed.
