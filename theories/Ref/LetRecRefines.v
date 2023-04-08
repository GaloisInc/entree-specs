From Coq Require Export
     Datatypes
     Arith.PeanoNat
     Arith.Peano_dec
     Arith.Compare
     Wf_nat
     Morphisms
     Setoid
     Program.Equality
     Lists.List
     Logic.Eqdep_dec
     Logic.EqdepFacts
     Eqdep EqdepFacts
     Logic.ProofIrrelevance
     Bool.Sumbool
.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Basics.QuantType
     Core.EnTreeDefinition
     Core.SubEvent
     Ref.Padded
     Ref.EnTreeSpecDefinition
     Ref.EnTreeSpecFacts
     Ref.EnTreeSpecCombinatorFacts
     Ref.RecSpecFix
     Ref.SpecM
     Eq.Eqit
     Ref.MRecSpec
     Ref.SpecMFacts
.

From Paco Require Import paco.

Export SigTNotations.

Import SpecMNotations.
Local Open Scope entree_scope.

(* FIXME: move to SpecM.v *)
Definition SpecM' (E:EncType) stack A : Type :=
  entree_spec' (FunStackE E stack) A.


Section lr_refines.

Context {E1 E2 : EncType} {stk1 stk2 : FunStack} {R1 R2 : Type}.
Context (funs1 : FrameTuple E1 stk1) (funs2 : FrameTuple E2 stk2).

Context (RPre : Rel (FunStackE E1 stk1) (FunStackE E2 stk2))
  (RPost : PostRel (FunStackE E1 stk1) (FunStackE E2 stk2))
  (RR : R1 -> R2 -> Prop).

Inductive lr_refinesF (sim : SpecM E1 stk1 R1 -> SpecM E2 stk2 R2 -> Prop) : SpecM' E1 stk1 R1 -> SpecM' E2 stk2 R2 -> Prop :=

(* Ret |= Ret *)
| lr_refinesF_Ret r1 r2 : RR r1 r2 -> lr_refinesF sim (RetF r1) (RetF r2)

(* t1 |= t2 => Tau t1 |= Tau t2 *)
| lr_refinesF_Tau t1 t2 : sim t1 t2 -> lr_refinesF sim (TauF t1) (TauF t2)

(* RPre e1 e2 -> (forall a b, RPost e1 e2 a b -> k1 a |= k2 b) ->
   Vis e1 k1 |= Vis e2 k2 *)
| lr_refinesF_Vis e1 e2 k1 k2 :
  RPre e1 e2 -> (forall a b, RPost e1 e2 a b -> sim (k1 a) (k2 b)) ->
  lr_refinesF sim (VisF (Spec_vis e1) k1) (VisF (Spec_vis e2) k2)

(* t1 |= t2 => Tau t1 |= t2 *)
| lr_refinesF_TauL t1 ot2 : lr_refinesF sim (observe t1) ot2 ->
                            lr_refinesF sim (TauF t1) ot2

(* t1 |= t2 => t1 |= Tau t2 *)
| lr_refinesF_TauR ot1 t2 : lr_refinesF sim ot1 (observe t2) ->
                            lr_refinesF sim ot1 (TauF t2)

(* (forall a, t1 |= k a) => t1 |= Forall k *)
| lr_refinesF_forallR A ot1 k : (forall a, lr_refinesF sim ot1 (observe (k a))) ->
                                lr_refinesF sim ot1 (VisF (Spec_forall A) k)

(* (exists a, t1 |= k a) => t1 |= Exists k *)
| lr_refinesF_existsR A ot1 k a : lr_refinesF sim ot1 (observe (k a)) ->
                                  lr_refinesF sim ot1 (VisF (Spec_exists A) k)

(* (exists a, k a |= t2) => Forall k |= t2 *)
| lr_refinesF_forallL A ot2 k a : lr_refinesF sim (observe (k a)) ot2 ->
                                  lr_refinesF sim (VisF (Spec_forall A) k) ot2

(* (forall a, k a |= t2) => Exists k |= t2 *)
| lr_refinesF_existsL A ot2 k : (forall a, lr_refinesF sim (observe (k a)) ot2) ->
                                lr_refinesF sim (VisF (Spec_exists A) k) ot2

(* apply funs1 call1 >>= k1 |= t2 => CallS call1 >>= k1 |= t2 *)
| lr_refinesF_unfoldL call1 k1 ot2 :
    lr_refinesF sim (TauF (applyFrameTuple E1 stk1 funs1 call1 >>= k1)) ot2 ->
    lr_refinesF sim (VisF (Spec_vis (inl call1)) k1) ot2

(* t1 |= apply funs2 call2 >>= k2 => t1 |= CallS call2 >>= k2 *)
| lr_refinesF_unfoldR ot1 call2 k2 :
    lr_refinesF sim ot1 (TauF (applyFrameTuple E2 stk2 funs2 call2 >>= k2)) ->
    lr_refinesF sim ot1 (VisF (Spec_vis (inl call2)) k2)
.


(** The standard Paco nonsense **)

Hint Constructors lr_refinesF : entree_spec.

Definition lr_refines_ sim : SpecM E1 stk1 R1 -> SpecM E2 stk2 R2 -> Prop :=
  fun t1 t2 => lr_refinesF sim (observe t1) (observe t2).

Lemma monotone_lr_refinesF ot1 ot2 sim sim' (LE : sim <2= sim')
      (IN : lr_refinesF sim ot1 ot2) : lr_refinesF sim' ot1 ot2.
Proof with eauto with entree_spec.
  induction IN...
Qed.

Lemma monotone_lr_refines_: monotone2 lr_refines_.
Proof. red. intros. eapply monotone_lr_refinesF; eauto. Qed.

(* lr_refines is the coinductive closure of lr_refinesF *)
Definition lr_refines := paco2 lr_refines_ bot2.

(* letrec_refines is the padded version of lr_refines *)
Definition letrec_refines t1 t2 := lr_refines (pad t1) (pad t2).

End lr_refines.

Global Hint Resolve monotone_lr_refines_ : paco.

Global Instance eq_itree_lr_refines_Proper1 {E1 E2 : EncType} {stk1 stk2} {R1 R2}
  funs1 funs2 RPre RPost RR r :
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
    (@lr_refines_ E1 E2 stk1 stk2 R1 R2 funs1 funs2 RPre RPost RR (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) r)).
Proof.
  repeat intro. apply bisimulation_is_eq in H. apply bisimulation_is_eq in H0.
  subst. auto.
Qed.

Global Instance eq_itree_lr_refines_Proper2 {E1 E2 : EncType} {stk1 stk2} {R1 R2}
  funs1 funs2 RPre RPost RR r :
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
    (paco2 (@lr_refines_ E1 E2 stk1 stk2 R1 R2 funs1 funs2 RPre RPost RR) r).
Proof.
  repeat intro. apply bisimulation_is_eq in H. apply bisimulation_is_eq in H0.
  subst. auto.
Qed.



Section lr_refines_props.

Context {E1 E2 : EncType} {stk1 stk2 : FunStack} {R1 R2 : Type} {RR : Rel R1 R2}.
Context (funs1 : FrameTuple E1 stk1) (funs2 : FrameTuple E2 stk2).

(* Lift a relation on FunStackE events from the nil stack to arbitrary ones *)
Definition liftNilRel (R : Rel (FunStackE E1 pnil) (FunStackE E2 pnil)) :
  Rel (FunStackE E1 stk1) (FunStackE E2 stk2) :=
  fun e1 e2 => match e1,e2 with
               | inr e1', inr e2' => R (inr e1') (inr e2')
               | _,_ => False
               end.

(* Lift a postcondition on FunStackE events from the nil stack to arbitrary ones *)
Definition liftNilPostRel (R : PostRel (FunStackE E1 pnil) (FunStackE E2 pnil)) :
  PostRel (FunStackE E1 stk1) (FunStackE E2 stk2) :=
  fun e1 e2 => match e1,e2 with
               | inr e1', inr e2' => R (inr e1') (inr e2')
               | _,_ => fun _ _ => False
               end.

Lemma observing_LetRecS E R stk funs body :
  LetRecS E R stk funs body = LetRecS E R stk funs (go _ _ (observe body)).
Proof.
  reflexivity.
Qed.

Lemma observing_BindS E stk A B m (k : A -> SpecM E stk B) :
  BindS m k = BindS (go _ _ (observe m)) k.
Proof.
  reflexivity.
Qed.

(* lr_refines is sound, meaning that it implies two letrecs refine each other *)
Lemma lr_refines_soundness RPre RPost t1 t2 :
  lr_refines funs1 funs2 (liftNilRel RPre) (liftNilPostRel RPost) RR t1 t2 ->
  refines RPre RPost RR (LetRecS _ R1 _ funs1 t1) (LetRecS _ R2 _ funs2 t2).
Proof.
  revert t1 t2; pcofix CIH; intros.
  rewrite observing_LetRecS. rewrite (observing_LetRecS E2).
  punfold H0. red in H0. pstep. red.
  unfold SpecM, FunStackE, EncodingType_FunStackE in * |- *.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  clear t1 Heqot1 t2 Heqot2.
  hinduction H0 before r; intros; pclearbot; eauto.
  - constructor; assumption.
  - apply refinesF_Tau. right. apply CIH. apply H.
  - unfold liftNilRel in H.
    destruct e1; [ contradiction | ]. destruct e2; [ contradiction | ].
    cbn. eapply refinesF_Vis; [ apply H | ].
    intros. right. apply CIH.
    destruct (H0 a b H1); [ | destruct H2 ]. apply H2.
  - cbn. apply refinesF_TauL. apply IHlr_refinesF. intros. apply CIH. assumption.
  - cbn. apply refinesF_TauR. apply IHlr_refinesF. intros. apply CIH. assumption.
  - cbn. apply refinesF_forallR. intros. apply H0. intros. apply CIH. assumption.
  - cbn. eapply refinesF_existsR. apply IHlr_refinesF.
    intros. apply CIH. assumption.
  - cbn. eapply refinesF_forallL. apply IHlr_refinesF.
    intros. apply CIH. assumption.
  - cbn. apply refinesF_existsL. intros. apply H0. intros. apply CIH. assumption.
Qed.

(* lr_refines is complete, meaning that it holds whenever two letrecs refine
each other *)
Lemma lr_refines_completeness RPre RPost t1 t2 t1' t2' :
  observe t1' = observe (LetRecS _ R1 _ funs1 t1) ->
  observe t2' = observe (LetRecS _ R2 _ funs2 t2) ->
  refines RPre RPost RR t1' t2' ->
  lr_refines funs1 funs2 (liftNilRel RPre) (liftNilPostRel RPost) RR t1 t2.
Proof.
  revert t1 t2 t1' t2'; pcofix CIH; intros.
  punfold H2. red in H2. pstep. red.
  remember (observe t1') as ot1'. remember (observe t2') as ot2'.
  clear t1' Heqot1' t2' Heqot2'.
  hinduction H2 before r; intros; pclearbot; eauto.
  - destruct t1 as [[]]; destruct t2 as [[]]; try discriminate.
    + injection H0; intros; injection H1; intros. constructor.
      subst r1. subst r2. assumption.
    + admit.
Admitted.


(* Add a precondition for recursive calls *)
Definition addCallPreRel {E1 E2 : EncType} {stk1 stk2}
           (precond : Rel (FrameCall stk1) (FrameCall stk2))
           (RPre : Rel (FunStackE E1 pnil) (FunStackE E2 pnil)) :
  Rel (FunStackE E1 stk1) (FunStackE E2 stk2) :=
  fun a1 a2 => match a1,a2 with
               | inl args1, inl args2 => precond args1 args2
               | inr ev1, inr ev2 => RPre (inr ev1) (inr ev2)
               | _, _ => False
               end.

(* Add a postcondition for recursive calls *)
Definition addCallPostRel {E1 E2 : EncType} {stk1 stk2}
           (postcond : PostRel (FrameCall stk1) (FrameCall stk2))
           (RPost : PostRel (FunStackE E1 pnil) (FunStackE E2 pnil)) :
  PostRel (FunStackE E1 stk1) (FunStackE E2 stk2) :=
  fun a1 a2 => match a1,a2 with
               | inl args1, inl args2 => postcond args1 args2
               | inr ev1, inr ev2 => RPost (inr ev1) (inr ev2)
               | _, _ => fun _ _ => False
               end.


Lemma lr_refines_bind RPre RPost S1 S2 (RS : Rel S1 S2) m1 m2 k1 k2 :
  lr_refines funs1 funs2 RPre RPost RS m1 m2 ->
  (forall x1 x2, RS x1 x2 ->
                 lr_refines funs1 funs2 RPre RPost RR (k1 x1) (k2 x2)) ->
  lr_refines funs1 funs2 RPre RPost RR (m1 >>= k1) (m2 >>= k2).
Proof.
  intros mref kref; revert m1 m2 mref; pcofix CIH; intros.
  punfold mref; red in mref.
  rewrite (observing_BindS E1). rewrite (observing_BindS E2).
  unfold EncodingType_FrameCall, encodes.
  remember (observe m1) as om1. remember (observe m2) as om2.
  clear m1 m2 Heqom1 Heqom2.
  hinduction mref before om1; intros; pclearbot.
  - eapply paco2_mon.
    + setoid_rewrite bind_ret_l. apply kref; assumption.
    + intros. destruct PR.
  - pstep. apply lr_refinesF_Tau. right. apply CIH. assumption.
  - pstep. apply lr_refinesF_Vis; [ assumption | ].
    intros. right. apply CIH. remember (H0 a b H1).
    destruct u; [ assumption | destruct b0 ].
  - pstep. apply lr_refinesF_TauL. pstep_reverse.
  - pstep. apply lr_refinesF_TauR. pstep_reverse.
  - pstep. apply lr_refinesF_forallR. intros. pstep_reverse. apply H0.
  - pstep. eapply lr_refinesF_existsR. pstep_reverse. apply IHmref.
  - pstep. eapply lr_refinesF_forallL. pstep_reverse. apply IHmref.
  - pstep. apply lr_refinesF_existsL. intros. pstep_reverse. apply H0.
  - pstep. setoid_rewrite bind_vis. apply lr_refinesF_unfoldL.
    change
      (lr_refinesF funs1 funs2 RPre RPost RR
         (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) r)
         (observe (Tau (x <- applyFrameTuple E1 stk1 funs1 call1;; EnTree.bind (k0 x) k1)))
         (observe (x <- {| _observe := ot2 |};; k2 x))).
    pstep_reverse. 
    setoid_rewrite <- bind_tau. setoid_rewrite <- bind_bind.
    apply IHmref.
  - pstep. setoid_rewrite bind_vis. apply lr_refinesF_unfoldR.
    change
      (lr_refinesF funs1 funs2 RPre RPost RR
         (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) r)
         (observe (x <- {| _observe := ot1 |};; k1 x))
         (observe (Tau (x <- applyFrameTuple E2 stk2 funs2 call2;; EnTree.bind (k0 x) k2)))).
    pstep_reverse.
    setoid_rewrite <- bind_tau. setoid_rewrite <- bind_bind.
    apply IHmref.
Qed.


(* Discharge a local pre/postconditions about calls *)
Lemma lr_refines_discharge RPre RPost precond postcond t1 t2 :
  (forall call1 call2,
      (precond call1 call2 : Prop) ->
      lr_refines funs1 funs2 (addCallPreRel precond RPre)
        (addCallPostRel postcond RPost) (postcond call1 call2)
        (applyFrameTuple _ _ funs1 call1)
        (applyFrameTuple _ _ funs2 call2)) ->
  lr_refines funs1 funs2 (addCallPreRel precond RPre)
    (addCallPostRel postcond RPost) RR t1 t2 ->
  lr_refines funs1 funs2 (liftNilRel RPre) (liftNilPostRel RPost) RR t1 t2.
Proof.
  intro funsRef. revert t1 t2; pcofix CIH; intros.
  punfold H0. red in H0. pstep. red.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  clear t1 Heqot1 t2 Heqot2.
  hinduction H0 before ot1; intros; pclearbot.
  - apply lr_refinesF_Ret. assumption.
  - apply lr_refinesF_Tau. right. apply CIH. apply H.
  - destruct e1; destruct e2.
    + apply lr_refinesF_unfoldL. apply lr_refinesF_unfoldR.
      apply lr_refinesF_Tau. right. apply CIH.
      apply (lr_refines_bind _ _ _ _ (postcond f f0)).
      -- apply funsRef. assumption.
      -- intros. destruct (H0 x1 x2 H1) as [ H3 | [] ].
         assumption.
    + destruct H.
    + destruct H.
    + apply lr_refinesF_Vis; [ apply H | ]. intros.
      right. apply CIH. destruct (H0 a b H1) as [ H2 | [] ].
      assumption.
  - apply lr_refinesF_TauL. assumption.
  - apply lr_refinesF_TauR. assumption.
  - apply lr_refinesF_forallR. intros. apply H0.
  - eapply lr_refinesF_existsR. apply IHlr_refinesF.
  - eapply lr_refinesF_forallL. apply IHlr_refinesF.
  - apply lr_refinesF_existsL. intros. apply H0.
  - apply lr_refinesF_unfoldL. apply IHlr_refinesF.
  - apply lr_refinesF_unfoldR. apply IHlr_refinesF.
Qed.

(* Push a pre/postcondition onto those of a refinement *)
Lemma lr_refines_push_prepost RPre RPost precond postcond t1 t2 :
  lr_refines funs1 funs2 (liftNilRel RPre) (liftNilPostRel RPost) RR t1 t2 ->
  lr_refines funs1 funs2 (addCallPreRel precond RPre)
    (addCallPostRel postcond RPost) RR t1 t2.
Proof.
  revert t1 t2; pcofix CIH; intros.
  punfold H0. red in H0. pstep. red.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  clear t1 Heqot1 t2 Heqot2.
  hinduction H0 before ot1; intros; pclearbot.
  - apply lr_refinesF_Ret. assumption.
  - apply lr_refinesF_Tau. right. apply CIH. assumption.
  - destruct e1 as [ call1 | ]; destruct e2 as [ call2 | ];
      [ destruct H | destruct H | destruct H | ].
    apply lr_refinesF_Vis; [ assumption | ]. intros.
    right. apply CIH. destruct (H0 a b H1) as [ H2 | [] ]. assumption.
  - apply lr_refinesF_TauL. apply IHlr_refinesF.
  - apply lr_refinesF_TauR. apply IHlr_refinesF.
  - apply lr_refinesF_forallR. intros. apply (H0 a).
  - eapply lr_refinesF_existsR. apply IHlr_refinesF.
  - eapply lr_refinesF_forallL. apply IHlr_refinesF.
  - apply lr_refinesF_existsL. intros. apply (H0 a).
  - apply lr_refinesF_unfoldL. apply IHlr_refinesF.
  - apply lr_refinesF_unfoldR. apply IHlr_refinesF.
Qed.

End lr_refines_props.
