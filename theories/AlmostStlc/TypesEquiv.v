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
where call_frame_pre_equiv (cf : call_frame) :
  Rel (denote_call_frame cf) (denote_call_frame cf) := 
{
  call_frame_pre_equiv nil := fun _ _ => False;
  call_frame_pre_equiv (cons (t1,t2) cf') :=
    sum_rel (types_equiv t1) (call_frame_pre_equiv cf')
}
where mfix_post_equiv (MR : mfix_ctx) : 
  PostRel (denote_mrec_ctx (denote_mfix_ctx MR)) (denote_mrec_ctx (denote_mfix_ctx MR)) :=
{
  mfix_post_equiv nil := fun _ _ _ _ => False;
  mfix_post_equiv (cons cf MR) := SumPostRel (call_frame_post_equiv cf) (mfix_post_equiv MR);
}
where call_frame_post_equiv (cf : call_frame) : 
  PostRel (denote_call_frame cf) (denote_call_frame cf) :=
{
  call_frame_post_equiv nil := fun _ _ _ _ => False;
  call_frame_post_equiv (cons (t1,t2) cf ) :=
    SumPostRel (fun _ _ => types_equiv t2) (call_frame_post_equiv cf);
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



(*
now show that for any d1 : denote MR, exists R t1 t2 xR x,
  d1 = projT1 (call_mrec x xR v1)

  then do these lemmas for insert rel

Lemma mfix_pre_equiv_position_inv (MR : mfix_ctx) 
      (d1 d2 : denote_mrec_ctx (denote_mfix_ctx MR)) :
  mfix_pre_equiv MR d1 d2 ->
  exists R (t1 t2 : type) (xR : var R MR) (x : var (t1,t2)),
  d1 = projT1 (call_mrec x xR v1) ->
  d2 = projT1 (call_mrec x xR v2) ->
  types_equiv t1 v1 v2 ->
  m.
Proof.
() *)
      (*
InsertPreRel :
forall {MR1 MR2 : mrec_ctx} {In1 In2 : Type} {Out1 : EncodedType In1} {Out2 : EncodedType In2} (x : var (In1 && Out1) MR1)
  (y : var (In2 && Out2) MR2),
Rel In1 In2 -> Rel (denote_remainder MR1 x) (denote_remainder MR2 y) -> Rel (denote_mrec_ctx MR1) (denote_mrec_ctx MR2)

mfix_pre_equiv
     : forall MR : mfix_ctx, Rel (denote_mrec_ctx (denote_mfix_ctx MR)) (denote_mrec_ctx (denote_mfix_ctx MR))

call_frame_pre_equiv
     : forall cf : call_frame, Rel (denote_call_frame cf) (denote_call_frame cf)
*)
(*
The term "mfix_pre_equiv (remove R MR xR)" has type
 "Rel (denote_mrec_ctx (denote_mfix_ctx (remove R MR xR))) (denote_mrec_ctx (denote_mfix_ctx (remove R MR xR)))"
while it is expected to have type
 "Rel (denote_remainder (denote_mfix_ctx MR) (denote_var xR)) (denote_remainder (denote_mfix_ctx MR) (denote_var xR))"
(cannot unify "denote_remainder (denote_mfix_ctx MR) (denote_var xR)" and "denote_mrec_ctx (denote_mfix_ctx (remove R MR xR))"

need some kind of lift thing to commute

*)


(*
Lemma insert_pre_rel_mfix_pre_equiv_aux1:
  forall (a b : call_frame) (l : mfix_ctx) (xR : var a l)
    (d : denote_mrec_ctx (denote_mfix_ctx' (List.map (List.map (fun '(t1, t2) => denote_type t1 && inout_encoded (denote_type t1) (denote_type t2))) l)))
    (d0 : denote_mrec_ctx (denote_mfix_ctx' (List.map (List.map (fun '(t1, t2) => denote_type t1 && inout_encoded (denote_type t1) (denote_type t2))) l)))
                 (a1 a2 : denote_call_frame a),
    inl a2 = projT1 (bring_to_front (denote_mfix_ctx (b :: l)) (VarS (denote_var xR)) (inr d0)) ->
    inl a1 = projT1 (bring_to_front (denote_mfix_ctx (b :: l)) (VarS (denote_var xR)) (inr d)) ->
    call_frame_pre_equiv a a1 a2 ->
    sum_rel (call_frame_pre_equiv a) (commute_remove_rel (mfix_pre_equiv (remove a l xR))) (projT1 (bring_to_front (denote_mfix_ctx l) (denote_var xR) d))
            (projT1 (bring_to_front (denote_mfix_ctx l) (denote_var xR) d0)).
Abort.

Lemma insert_pre_rel_equiv_comp_equiv_aux2:
  forall (a b : call_frame) (l : mfix_ctx) (xR : var a l) (x0 y : denote_mrec_ctx (denote_mfix_ctx (b :: l)))
    (b1 b2 : denote_remainder (denote_mfix_ctx (b :: l)) (denote_var (VarS xR))),
    commute_remove_rel (mfix_pre_equiv (remove a (b :: l) (VarS xR))) b1 b2 ->
    (forall x y : denote_mrec_ctx (denote_mfix_ctx l),
         InsertPreRel (denote_var xR) (denote_var xR) (call_frame_pre_equiv a) (commute_remove_rel (mfix_pre_equiv (remove a l xR))) x
           y <-> mfix_pre_equiv l x y) ->
    inr b1 = projT1 (bring_to_front (denote_mfix_ctx (b :: l)) (VarS (denote_var xR)) x0) ->
    inr b2 = projT1 (bring_to_front (denote_mfix_ctx (b :: l)) (VarS (denote_var xR)) y) -> mfix_pre_equiv (b :: l) x0 y.
Proof.
  intros a b l xR x0 y b1 b2.
  intros Hb12 IH Hb1 Hb2. red in Hb12. 
  Transparent remove_denote. Transparent remove.
  destruct (bring_to_front (denote_mfix_ctx (b :: l)) (VarS (denote_var xR)) x0) eqn : Heq1.
  simpl in Hb1. subst.
  destruct (bring_to_front (denote_mfix_ctx (b :: l)) (VarS (denote_var xR)) y) eqn : Heq2.
  simpl in Hb2. subst.
  simpl remove in Hb12. simpl in Hb12. 
  dependent destruction Hb12.
  - destruct b1; destruct b2.
    * injection x1; injection x; intros; subst. clear x x1.
      fold call_frame_pre_equiv in H.
      destruct x0; destruct y.
      -- constructor. fold call_frame_pre_equiv.
         setoid_rewrite bring_to_front_equation_4 in Heq1.
         setoid_rewrite bring_to_front_equation_4 in Heq2.
         injection Heq1. intros. subst.
         injection Heq2. intros. subst. auto.
      -- setoid_rewrite bring_to_front_equation_5 in Heq2.
         match goal with H : (let (x,f) := ?t in _ ) = _ |- _ =>
                           destruct t as [ [? | ?] ? ]; discriminate end.
      -- setoid_rewrite bring_to_front_equation_5 in Heq1.
         match goal with H : (let (x,f) := ?t in _ ) = _ |- _ =>
                           destruct t as [ [? | ?] ? ]; discriminate end.
      -- constructor.
         setoid_rewrite bring_to_front_equation_5 in Heq1.
         match goal with H : (let (x,f) := ?t in _ ) = _ |- _ =>
                           destruct t as [ [? | ?] ? ]; discriminate end.
    * destruct (remove_denote xR d0); discriminate.
    * destruct (remove_denote xR d); discriminate.
    * destruct (remove_denote xR d); discriminate.
  - destruct b1 eqn : Hb1'; try discriminate. destruct b2 eqn : Hb2'; try discriminate.
    (**)
    destruct x0; destruct y.
    + constructor. fold call_frame_pre_equiv.
      setoid_rewrite bring_to_front_equation_4 in Heq1. discriminate.
    + setoid_rewrite bring_to_front_equation_4 in Heq1. discriminate.
    + setoid_rewrite bring_to_front_equation_4 in Heq2. discriminate.
    + setoid_rewrite bring_to_front_equation_5 in Heq1.
      match goal with H : (let (x,f) := ?t in _ ) = _ |- _ =>
                           destruct t as [ [? | ?] ? ] eqn : Heq3; try discriminate end.
      injection Heq1. intros. subst. clear Heq1.
      setoid_rewrite bring_to_front_equation_5 in Heq2.
      match goal with H : (let (x,f) := ?t in _ ) = _ |- _ =>
                           destruct t as [ [? | ?] ? ] eqn : Heq4; try discriminate end.
      injection Heq2. intros. subst. clear Heq2.
      constructor.
      destruct (remove_denote xR d0) as [d0' ?] eqn : Heq5.
      destruct (remove_denote xR d) as [d' ?] eqn : Heq6.
      injection x. injection x1. intros. subst. clear x x1 IH.
      (* possible that this case requires induction on xR 
         

       *)
Abort. *)
(* how would insert pre rel work with mfix pre rel 

maybe consider using the position relation,
if related, x and y must have the same position

if they both have a position, then this relation reduces down 
to the types equiv stuff, in any case call it for now

*)

(*
       split.
    + simpl denote_var. unfold InsertPreRel. 
      intros. rewrite mfix_pre_equiv_equation_2.
      simpl denote_mfix_ctx in H.
      dependent destruction H.
      * simp bring_to_front in x1.
        simpl in x0, y.
        destruct x0; destruct y; 
        try setoid_rewrite bring_to_front_equation_2 in x1;
        try setoid_rewrite bring_to_front_equation_2 in x;
          try discriminate.
        cbn in x, x1. injection x. injection x1. intros. subst.
        constructor. auto.
      * destruct x0; destruct y; 
          try setoid_rewrite bring_to_front_equation_3 in x1;
          try setoid_rewrite bring_to_front_equation_3 in x;
          try discriminate.
        injection x1. injection x. intros; subst.
        constructor.
        red in H.
        assert (remove a (a :: l) VarZ  = l).
        simp remove. auto.
        setoid_rewrite remove_denote_equation_1 in H.
        cbn in H.
        clear - H. Transparent remove. cbn in H.
        Opaque remove. auto.
   + intros. rewrite mfix_pre_equiv_equation_2 in H.
     red. dependent destruction H.
     * constructor. auto.
     * constructor. red.
       setoid_rewrite remove_denote_equation_1.
       Transparent remove. cbn. Opaque remove. auto.          
  - split; intros.
    + red in H. dependent destruction H.
      * Transparent denote_var. simpl denote_var in x1, x.
        destruct x0; destruct y;
        try setoid_rewrite bring_to_front_equation_2 in x1;
        try setoid_rewrite bring_to_front_equation_2 in x;
          try discriminate.
        constructor. apply IHxR. red.
        eapply insert_pre_rel_mfix_pre_equiv_aux1; eauto.
      * simpl denote_var in x, x1, H.
        revert H x1 x.
        red in H. admit.
    + red in H. dependent destruction H. 
      * do 2 constructor; auto.
      * simpl denote_var. red. 
        eapply IHxR in H. red in H.
        dependent destruction H.
        -- destruct 
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
       -- destruct 
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
Admitted. *)
(* lets put this part aside for a bit and focus on another part *)
(*
Should be a PER 


rewrite with eutt

it should generalize eutt

should be the case that if it is a denotation, then it is self related
so it acts as an equivalence relation on its actual domain


tomorrow would be a good time to get a basic sketch of rutt done at least,
leave implementations of lemmas for later, there is a sense in which it is not
along a critical path because it is known to be true, where as
other things might actually include some bugs

on monday work on this but also dedicate some time to the proposal intro


also maybe go back to the comp_map proof and see what kind of reasoning principles are needed

*)
