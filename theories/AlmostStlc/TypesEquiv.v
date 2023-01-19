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

Inductive list_rel {A} (R : Rel A A): Rel (list A) (list A) :=
  | list_rel_nil : list_rel R nil nil
  | list_rel_cons a b l1 l2 : R a b ->list_rel R l1 l2 -> list_rel R (cons a l1) (cons a l2).

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

Definition comp_equiv {t Γ MR} :=
    fun c1 c2 => forall hyps1 hyps2, ctx_equiv Γ hyps1 hyps2 ->
              rutt (mfix_pre_equiv MR) (mfix_post_equiv MR) (types_equiv t) (c1 hyps1) (c2 hyps2).

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
  intros. red. intros.
  simp denote_comp.
  eapply rutt_bind; eauto.
  intros.
  unfold call_term.
  destruct (call_mrec x xR r1) as [c1 f1] eqn : Heq1.
  destruct (call_mrec x xR r2) as [c2 f2] eqn : Heq2. 
  setoid_rewrite bind_trigger. apply rutt_Vis.
  eapply mfix_pre_call_mrec; eauto.
  intros. apply rutt_Ret. eapply mfix_post_equiv_types_equiv; eauto.
Qed.


Lemma pre_equiv_sum_rel MR R : 
  forall c1 c2, mfix_pre_equiv (R :: MR) c1 c2 <-> sum_rel (call_frame_pre_equiv R) (mfix_pre_equiv MR) c1 c2.
Proof.
  rewrite mfix_pre_equiv_equation_2.
  intros. reflexivity.
Qed.

Lemma post_equiv_sum_post_rel MR R : 
  forall c1 c2 v1 v2, mfix_post_equiv (R :: MR) c1 c2 v1 v2 <-> SumPostRel (call_frame_post_equiv R) (mfix_post_equiv MR) c1 c2 v1 v2.
Proof.
  rewrite mfix_post_equiv_equation_2.
  intros. reflexivity.
Qed.
