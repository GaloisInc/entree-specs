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

(* Destruct an equality on VisF constructors into a dependent equality *)
(* FIXME: move to SpecM.v *)
Lemma injection_VisF_eq {E} `{EncodingType E} {R F} {e1 e2 : E}
  {k1 : encodes e1 -> F} {k2 : encodes e2 -> F} :
  VisF (R:=R) e1 k1 = VisF e2 k2 ->
  existT (fun e => encodes e -> F) e1 k1 = existT _ e2 k2.
Proof.
  intro e. inversion e. reflexivity.
Qed.

Ltac observe_tau :=
  (lazymatch goal with
   | |- context F [TauF ?e] => replace (TauF e) with (observe (Tau e)); [ | reflexivity ]
   end).

Lemma entree_eta {E} `{EncodingType E} {R} (e : entree E R) :
  e = go _ _ (observe e).
Proof.
  destruct e. reflexivity.
Qed.

Lemma entree_beta {E} `{EncodingType E} {R} (e : entree' E R) :
  e = observe (go _ _ e).
Proof.
  reflexivity.
Qed.


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
| lr_refinesF_forallR A ot1 k : (forall a, lr_refinesF sim ot1 (TauF (k a))) ->
                                lr_refinesF sim ot1 (VisF (Spec_forall A) k)

(* (exists a, t1 |= k a) => t1 |= Exists k *)
| lr_refinesF_existsR A ot1 k a : lr_refinesF sim ot1 (TauF (k a)) ->
                                  lr_refinesF sim ot1 (VisF (Spec_exists A) k)

(* (exists a, k a |= t2) => Forall k |= t2 *)
| lr_refinesF_forallL A ot2 k a : lr_refinesF sim (TauF (k a)) ot2 ->
                                  lr_refinesF sim (VisF (Spec_forall A) k) ot2

(* (forall a, k a |= t2) => Exists k |= t2 *)
| lr_refinesF_existsL A ot2 k : (forall a, lr_refinesF sim (TauF (k a)) ot2) ->
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

(*
(* Restatement of a helper lemma about normal refinement *)
Lemma refinesF_TauR_inv_r' E1 E2 `{EncodingType E1} `{EncodingType E2}
  (RPre : Rel E1 E2) (RPost : PostRel E1 E2) R1 R2 (RR : Rel R1 R2) r t1 t2 :
  refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) r) (observe t1) (TauF t2) ->
  refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) r) (observe t1) (observe t2).
Proof.
  intro. remember (TauF t2) as x.
  remember (observe t1) as ot1; clear Heqot1.
  induction H1; inversion Heqx.
  - constructor. pstep_reverse.

induction H1.
  intros. induction H1
  intros. pstep_reverse. apply refines_TauR_inv. pstep. auto.
Qed.
*)

(* Lift a relation on FunStackE events from the nil stack to arbitrary ones *)
Definition liftNilRel {E1 E2 stk1 stk2}
  (R : Rel (FunStackE E1 pnil) (FunStackE E2 pnil)) :
  Rel (FunStackE E1 stk1) (FunStackE E2 stk2) :=
  fun e1 e2 => match e1,e2 with
               | inr e1', inr e2' => R (inr e1') (inr e2')
               | _,_ => False
               end.

(* Lift a postcondition on FunStackE events from the nil stack to arbitrary ones *)
Definition liftNilPostRel {E1 E2 stk1 stk2}
  (R : PostRel (FunStackE E1 pnil) (FunStackE E2 pnil)) :
  PostRel (FunStackE E1 stk1) (FunStackE E2 stk2) :=
  fun e1 e2 => match e1,e2 with
               | inr e1', inr e2' => R (inr e1') (inr e2')
               | _,_ => fun _ _ => False
               end.

(* Compose two liftNilRel proofs *)
Lemma liftNilRel_compose {E1 E2 E3 stk1 stk2 stk3} R12 R23 x y z :
  @liftNilRel E1 E2 stk1 stk2 R12 x y ->
  @liftNilRel E2 E3 stk2 stk3 R23 y z ->
  liftNilRel (rcompose R12 R23) x z.
Proof.
  intros. destruct x; destruct y; destruct z; cbn in *; try contradiction.
  eexists; split; eassumption.
Qed.

Lemma elim_RComposePostRel {E1 E2 E3} `{EncodingType E1} `{EncodingType E2}
  `{EncodingType E3} (R1 : Rel E1 E2) (R2 : Rel E2 E3) RPost1 RPost2
  a b c x z :
  R1 a b -> R2 b c ->
  RComposePostRel R1 R2 RPost1 RPost2 a c x z ->
  exists y, RPost1 a b x y /\ RPost2 b c y z.
Proof.
  intros. destruct H4. apply H4; assumption.
Qed.

(* Destruct the composition of two liftNilPostRel proofs *)
Lemma liftNilPostRel_compose_elim {E1 E2 E3 stk1 stk2 stk3} R12 R23 RPost12 RPost23
  (e1 : FunStackE E1 stk1) (e2 : FunStackE E2 stk2) (e3 : FunStackE E3 stk3) x z :
  liftNilRel R12 e1 e2 -> liftNilRel R23 e2 e3 ->
  liftNilPostRel (RComposePostRel R12 R23 RPost12 RPost23) e1 e3 x z ->
  exists y:encodes e2,
    liftNilPostRel RPost12 e1 e2 x y /\ liftNilPostRel RPost23 e2 e3 y z.
Proof.
  intros. destruct e1; destruct e2; destruct e3; cbn in *; try contradiction.
  destruct (elim_RComposePostRel _ _ _ _ _ _ _ _ _ H H0 H1). destruct H2.
  eexists; split; eassumption.
Qed.


(*** Inversion lemmas about refinement ***)
Section lr_refines_inv.
Context {E1 E2 : EncType} {stk1 stk2 : FunStack} {R1 R2 : Type}.
Context (funs1 : FrameTuple E1 stk1) (funs2 : FrameTuple E2 stk2).

Context (RPre : Rel (FunStackE E1 stk1) (FunStackE E2 stk2))
  (RPost : PostRel (FunStackE E1 stk1) (FunStackE E2 stk2))
  (RR : R1 -> R2 -> Prop).

Lemma lr_refines_TauL_inv t1 t2 :
  lr_refines funs1 funs2 RPre RPost RR (Tau t1) t2 ->
  lr_refines funs1 funs2 RPre RPost RR t1 t2.
Proof.
  remember (TauF t1) as x.
  intro. punfold H. red in H. simpl in H. pfold. red.
  remember (observe t2) as ot2.
  clear t2 Heqot2.
  induction H; inversion Heqx.
  - pclearbot. constructor. pstep_reverse. rewrite <- H1.
    eapply paco2_mon; [ eassumption | ]. intros x0 x1 b; destruct b.
  - rewrite <- H1. eapply monotone_lr_refinesF; [ | eassumption ].
    intros. pclearbot. left. eapply paco2_mon; [ eassumption | ].
    intros. contradiction.
  - constructor. apply IHlr_refinesF. assumption.
  - constructor. intros. apply H0. assumption.
  - econstructor. apply IHlr_refinesF. assumption.
  - constructor. apply IHlr_refinesF. assumption.
Qed.

Lemma lr_refines_TauR_inv t1 t2 :
  lr_refines funs1 funs2 RPre RPost RR t1 (Tau t2) ->
  lr_refines funs1 funs2 RPre RPost RR t1 t2.
Proof.
  remember (TauF t2) as x.
  intro. punfold H. red in H. simpl in H. pfold. red.
  remember (observe t1) as ot1. clear t1 Heqot1.
  induction H; inversion Heqx.
  - pclearbot. constructor. pstep_reverse. rewrite <- H1.
    eapply paco2_mon; [ eassumption | ]. intros x0 x1 b; destruct b.
  - constructor. apply IHlr_refinesF. assumption.
  - rewrite <- H1. eapply monotone_lr_refinesF; [ | eassumption ].
    intros. pclearbot. left. eapply paco2_mon; [ eassumption | ].
    intros. contradiction.
  - econstructor. apply IHlr_refinesF. assumption.
  - constructor. intros. apply H0. assumption.
  - constructor. apply IHlr_refinesF. assumption.
Qed.

Lemma lr_refinesF_TauR_inv t1 t2 :
  lr_refinesF funs1 funs2 RPre RPost RR (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) bot2) (observe t1) (TauF t2) ->
  lr_refinesF funs1 funs2 RPre RPost RR (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) bot2) (observe t1) (observe t2).
Proof.
  intros. pstep_reverse. apply lr_refines_TauR_inv. pstep. apply H.
Qed.

Lemma lr_refinesF_TauL_inv t1 t2 :
  lr_refinesF funs1 funs2 RPre RPost RR
    (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) bot2) (TauF t1) (observe t2) ->
  lr_refinesF funs1 funs2 RPre RPost RR
    (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) bot2) (observe t1) (observe t2).
Proof.
  intros. pstep_reverse. apply lr_refines_TauL_inv. pstep. assumption.
Qed.

Lemma lr_refines_forallR_inv A t1 k2 :
  lr_refines funs1 funs2 RPre RPost RR
    t1 (Vis (@Spec_forall (FunStackE E2 stk2) A) k2) ->
  forall a, lr_refines funs1 funs2 RPre RPost RR t1 (Tau (k2 a)).
Proof.
  intros ref12 a. punfold ref12. red in ref12. cbn in ref12. pstep. red.
  remember (observe t1) as ot1; clear t1 Heqot1.
  remember (VisF (Spec_forall A) k2) as ot2.
  induction ref12; try discriminate.
  - apply lr_refinesF_TauL. apply IHref12. assumption.
  - inversion Heqot2. revert k Heqot2 H H0 H3; rewrite H2; intros.
    inj_existT. rewrite H3 in H. apply H.
  - eapply lr_refinesF_forallL. apply IHref12. assumption.
  - apply lr_refinesF_existsL. intros. apply H0. assumption.
  - apply lr_refinesF_unfoldL. apply IHref12. assumption.
Qed.


Lemma lr_refines_existsL_inv A k1 t2 :
  lr_refines funs1 funs2 RPre RPost RR
    (Vis (@Spec_exists (FunStackE E1 stk1) A) k1) t2 ->
  forall a, lr_refines funs1 funs2 RPre RPost RR (Tau (k1 a)) t2.
Proof.
  intros ref12 a. punfold ref12. red in ref12. cbn in ref12. pstep. red.
  remember (observe t2) as ot2; clear t2 Heqot2.
  remember (VisF (Spec_exists A) k1) as ot1.
  induction ref12; try discriminate.
  - apply lr_refinesF_TauR. apply IHref12. assumption.
  - apply lr_refinesF_forallR. intros. apply H0. assumption.
  - eapply lr_refinesF_existsR. apply IHref12. assumption.
  - inversion Heqot1. revert k Heqot1 ot2 H a H0 H3; rewrite H2; intros.
    inj_existT. rewrite H3 in H. apply H.
  - apply lr_refinesF_unfoldR. apply IHref12. assumption.
Qed.


(* A version of lr_refinesF specialized to a forall on the left *)
Inductive forallLRRefinesF (sim : SpecM E1 stk1 R1 -> SpecM E2 stk2 R2 -> Prop)
  {A : QuantEnc} (k1 : encodes A -> SpecM E1 stk1 R1) : SpecM' E2 stk2 R2 -> Prop :=
  | forallLRRefines_forallR (B : QuantEnc) k2 :
    (forall b, forallLRRefinesF sim k1 (TauF (k2 b))) ->
    forallLRRefinesF sim k1 (VisF (Spec_forall B) k2)
  | forallLRRefines_forallL t (a : encodes A) :
    lr_refinesF funs1 funs2 RPre RPost RR sim (TauF (k1 a)) t ->
    forallLRRefinesF sim k1 t
  | forallLRRefines_existsR B k2 (b : encodes B) :
    forallLRRefinesF sim k1 (TauF (k2 b)) ->
    forallLRRefinesF sim k1 (VisF (Spec_exists B : SpecEvent (FunStackE _ _)) k2)
  | forallLRRefines_TauR t2 :
    forallLRRefinesF sim k1 (observe t2) ->
    forallLRRefinesF sim k1 (TauF t2)
  | forallLRRefines_unfoldR call2 k2 :
    forallLRRefinesF sim k1 (TauF (applyFrameTuple E2 stk2 funs2 call2 >>= k2)) ->
    forallLRRefinesF sim k1 (VisF (Spec_vis (inl call2)) k2)
.

Lemma lr_refinesF_forallL_inv sim A k1 t2 :
  lr_refinesF funs1 funs2 RPre RPost RR sim
    (VisF (@Spec_forall (FunStackE E1 stk1) A) k1) t2 ->
  forallLRRefinesF sim k1 t2.
Proof.
  intros. remember (VisF (Spec_forall A) k1) as ot1.
  induction H; try discriminate.
  - apply forallLRRefines_TauR; apply IHlr_refinesF; assumption.
  - apply forallLRRefines_forallR; intros. apply H0. assumption.
  - eapply forallLRRefines_existsR. apply IHlr_refinesF. assumption.
  - inversion Heqot1. revert k Heqot1 a H IHlr_refinesF H2. rewrite H1. intros.
    inj_existT. rewrite H2 in H. eapply forallLRRefines_forallL. apply H.
  - apply forallLRRefines_unfoldR. apply IHlr_refinesF. assumption.
Qed.

(* A version of lr_refinesF specialized to an exists on the right *)
Inductive existsLRRefinesF (sim : SpecM E1 stk1 R1 -> SpecM E2 stk2 R2 -> Prop)
  {A : QuantEnc} (k2 : encodes A -> SpecM E2 stk2 R2) : SpecM' E1 stk1 R1 -> Prop :=
  | existsLRRefines_existsR t (a : encodes A) :
    lr_refinesF funs1 funs2 RPre RPost RR sim t (TauF (k2 a)) ->
    existsLRRefinesF sim k2 t
  | existsLRRefines_forallL B k1 (b : encodes B) :
    existsLRRefinesF sim k2 (observe (k1 b)) ->
    existsLRRefinesF sim k2 (VisF (Spec_forall B : SpecEvent (FunStackE _ _)) k1)
  | existsLRRefines_existsL (B : QuantEnc) k1 :
    (forall b, existsLRRefinesF sim k2 (observe (k1 b))) ->
    existsLRRefinesF sim k2 (VisF (Spec_exists B) k1)
  | existsLRRefines_TauL t1 :
    existsLRRefinesF sim k2 (observe t1) ->
    existsLRRefinesF sim k2 (TauF t1)
  | existsLRRefines_unfoldL call1 k1 :
    existsLRRefinesF sim k2 (observe (applyFrameTuple E1 stk1 funs1 call1 >>= k1)) ->
    existsLRRefinesF sim k2 (VisF (Spec_vis (inl call1)) k1)
.

Lemma existsLRRefinesF_TauL_inv A k2 t1 :
  @existsLRRefinesF (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) bot2)
    A k2 (TauF t1) ->
  @existsLRRefinesF (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) bot2)
    A k2 (observe t1).
Proof.
  intro H. remember (TauF t1) as tau_t1.
  revert t1 Heqtau_t1; induction H; intros; try discriminate.
  - subst t. eapply existsLRRefines_existsR. observe_tau. pstep_reverse.
    apply lr_refines_TauL_inv. pstep. apply H.
  - inversion Heqtau_t1. rewrite <- H1. assumption.
Qed.

Lemma lr_refinesF_existsR_inv A t1 k2 :
  lr_refinesF funs1 funs2 RPre RPost RR
    (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) bot2)
    t1 (VisF (@Spec_exists (FunStackE E2 stk2) A) k2) ->
  existsLRRefinesF (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) bot2) k2 t1.
Proof.
  intros. remember (VisF (Spec_exists A) k2) as ot2.
  induction H; try discriminate.
  - apply existsLRRefines_TauL; apply IHlr_refinesF; assumption.
  - inversion Heqot2. revert k Heqot2 a H IHlr_refinesF H2; rewrite H1; intros.
    inj_existT. rewrite H2 in H. eapply existsLRRefines_existsR. apply H.
  - eapply existsLRRefines_forallL. apply existsLRRefinesF_TauL_inv.
    apply IHlr_refinesF. assumption.
  - apply existsLRRefines_existsL. intros. apply existsLRRefinesF_TauL_inv.
    apply H0. assumption.
  - apply existsLRRefines_unfoldL. apply existsLRRefinesF_TauL_inv.
    apply IHlr_refinesF. assumption.
Qed.

Lemma lr_refines_callL_inv pre post call1 k1 t2 :
  lr_refines funs1 funs2 (liftNilRel pre) (liftNilPostRel post) RR
    (Vis (Spec_vis (inl call1)) k1) t2 ->
  lr_refines funs1 funs2 (liftNilRel pre) (liftNilPostRel post) RR
    (Tau (applyFrameTuple E1 stk1 funs1 call1 >>= k1)) t2.
Proof.
  intros ref12. punfold ref12. red in ref12. cbn in ref12. pstep. red.
  remember (observe t2) as ot2; clear t2 Heqot2.
  remember (VisF (Spec_vis (inl call1)) k1) as ot1.
  induction ref12; try discriminate.
  - inversion Heqot1. rewrite H2 in H. destruct e2; destruct H.
  - apply lr_refinesF_TauR. apply IHref12. assumption.
  - apply lr_refinesF_forallR; intros. apply H0. assumption.
  - eapply lr_refinesF_existsR. apply IHref12. assumption.
  - inversion Heqot1. revert k0 Heqot1 ref12 IHref12. rewrite H0. intros.
    remember (injection_VisF_eq Heqot1) as e. clear Heqe. inj_existT.
    rewrite <- e. apply ref12.
  - apply lr_refinesF_unfoldR. apply IHref12. assumption.
Qed.


End lr_refines_inv.



(*** Proving transitivity ***)

Lemma lr_refines_trans {E1 E2 E3} {stk1 stk2 stk3} {R1 R2 R3}
  RPre1 RPre2 RPost1 RPost2
  (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
  (funs1 : FrameTuple E1 stk1) (funs2 : FrameTuple E2 stk2)
  (funs3 : FrameTuple E3 stk3)
  (t1 : SpecM E1 stk1 R1) (t2 : SpecM E2 stk2 R2) (t3 : SpecM E3 stk3 R3) :
  lr_refines funs1 funs2 (liftNilRel RPre1) (liftNilPostRel RPost1) RR1 t1 t2 ->
  lr_refines funs2 funs3 (liftNilRel RPre2) (liftNilPostRel RPost2) RR2 t2 t3 ->
  lr_refines funs1 funs3 (liftNilRel (rcompose RPre1 RPre2))
    (liftNilPostRel (RComposePostRel RPre1 RPre2 RPost1 RPost2))
    (rcompose RR1 RR2) t1 t3.
Proof.
  revert t1 t2 t3; pcofix CIH; intros t1 t2 t3 ref12 ref23.
  pfold. red. punfold ref12. red in ref12. punfold ref23. red in ref23.
  remember (observe t1) as ot1. clear t1 Heqot1.
  remember (observe t2) as ot2. clear t2 Heqot2.
  revert t3 ref23; induction ref12; intros.
  - remember (RetF r2) as x. induction ref23; inversion Heqx.
    + constructor. exists r2; split; [ assumption | ].
      rewrite <- H2. assumption.
    + constructor. apply IHref23. assumption.
    + constructor. intros. apply H1. assumption.
    + econstructor. apply IHref23. assumption.
    + constructor. apply IHref23. assumption.
  - pclearbot.
    assert (lr_refines funs2 funs3 (liftNilRel RPre2) (liftNilPostRel RPost2) RR2 t2 t3) as ref23'.
    { apply lr_refines_TauL_inv. pstep. assumption. }
    clear ref23. punfold ref23'. red in ref23'.
    remember (observe t3) as ot3; clear t3 Heqot3.
    punfold H. red in H.
    remember (observe t2) as ot2. clear t2 Heqot2.
    revert t1 H. induction ref23'; intros.
    + apply lr_refinesF_TauL.
      (* Proof that  t1 |= Ret r1 |= Ret r2  implies Tau t1 |= Ret r2 *)
      remember (observe t1) as ot1; clear t1 Heqot1.
      remember (RetF r1) as ot0. induction H0; try discriminate Heqot0.
      * inversion Heqot0. apply lr_refinesF_Ret. rewrite H2 in H0.
        eexists; split; eassumption.
      * apply lr_refinesF_TauL. apply IHlr_refinesF. assumption.
      * eapply lr_refinesF_forallL. apply IHlr_refinesF. assumption.
      * apply lr_refinesF_existsL. intros. apply H1. assumption.
      * apply lr_refinesF_unfoldL. apply IHlr_refinesF. assumption.
    + apply lr_refinesF_Tau. right. pclearbot. eapply CIH; [ | eassumption ].
      apply lr_refines_TauR_inv. pstep. apply H0.
    + apply lr_refinesF_TauL.
      (* Proof tht  t1 |= Vis e2 k2 |= Vis e3 k3  implies t1 |= Vis e3 k3 *)
      remember (observe t1) as ot1; clear t1 Heqot1.
      remember (VisF (Spec_vis e1) k1) as ot0.
      induction H1; try discriminate Heqot0.
      * set (e := injection_VisF_eq Heqot0). inversion e.
        revert k3 Heqot0 H1 H2 e; rewrite H4; intros. clear e3 H4. inj_existT.
        apply lr_refinesF_Vis; [ eapply liftNilRel_compose; eassumption | ].
        intros.
        destruct (liftNilPostRel_compose_elim _ _ _ _ _ _ _ _ _ H1 H H3)
          as [ c [ PR_ac PR_cb ]].
        remember (H2 a c PR_ac) as ref_k0_k3. clear Heqref_k0_k3.
        rewrite <- e in H0.
        remember (H0 c b PR_cb) as ref_k3_k2. clear Heqref_k3_k2.
        pclearbot.
        right. eapply CIH; eassumption.
      * apply lr_refinesF_TauL. apply IHlr_refinesF. assumption.
      * eapply lr_refinesF_forallL. apply IHlr_refinesF. assumption.
      * eapply lr_refinesF_existsL. intros. apply H2. assumption.
      * apply lr_refinesF_unfoldL. apply IHlr_refinesF. assumption.
      * inversion Heqot0. rewrite <- H3 in H. destruct e2; simpl in H; contradiction.
    + apply IHref23'. pstep_reverse. apply lr_refines_TauR_inv.
      pstep. apply H.
    + apply lr_refinesF_Tau. right.
      apply (CIH _ (go _ _ ot1)); pstep; assumption.
    + apply lr_refinesF_forallR. intros. apply H0. assumption.
    + eapply lr_refinesF_existsR. apply IHref23'. assumption.
    + apply IHref23'. observe_tau. pstep_reverse.
      apply lr_refines_forallR_inv. pstep. apply H.
    + assert (existsLRRefinesF funs1 funs2
                (liftNilRel RPre1) (liftNilPostRel RPost1) RR1
                (upaco2 (lr_refines_ funs1 funs2
                           (liftNilRel RPre1) (liftNilPostRel RPost1) RR1) bot2)
                k (observe t1))
        as ref_exR;
        [ apply lr_refinesF_existsR_inv; assumption | ].
      clear H1.
      destruct t1 as [ ot1 ]. simpl in ref_exR.
      induction ref_exR.
      * apply (H0 a). assumption.
      * apply lr_refinesF_TauL. eapply lr_refinesF_forallL.
        rewrite <- (entree_eta (k1 b)) in IHref_exR. apply IHref_exR.
      * apply lr_refinesF_TauL. eapply lr_refinesF_existsL. intros.
        rewrite (entree_eta (k1 a)). apply H2.
      * apply lr_refinesF_TauL. simpl. rewrite (entree_eta t1).
        apply IHref_exR.
      * apply lr_refinesF_TauL. apply lr_refinesF_unfoldL.
        rewrite <- entree_eta in IHref_exR. apply IHref_exR.
    + apply IHref23'.
      admit. (* t1 |= Vis call k1  implies t1 |= Tau (unfold call >>= k1) *)
    + apply lr_refinesF_unfoldR. apply IHref23'. assumption.
  - admit. (* Vis e1 k1 |= Vis e2 k2 |= t3  implies Vis e1 k1 |= t3 *)
  - apply lr_refinesF_TauL. apply IHref12. assumption.
  - apply IHref12. pstep_reverse. apply lr_refines_TauL_inv. pstep. assumption.
  - assert (forallLRRefinesF funs2 funs3
              (liftNilRel RPre2) (liftNilPostRel RPost2) RR2
              (upaco2 (lr_refines_ funs2 funs3
                         (liftNilRel RPre2) (liftNilPostRel RPost2) RR2) bot2)
              k
              (observe t3))
      as ref_allL;
      [ apply lr_refinesF_forallL_inv; assumption | ].
    clear ref23. remember (observe t3) as ot3; clear t3 Heqot3.
    induction ref_allL.
    + apply lr_refinesF_forallR; intros. apply H2.
    + apply (H0 a (go _ _ t)). apply H1.
    + eapply lr_refinesF_existsR. apply IHref_allL.
    + apply lr_refinesF_TauR. apply IHref_allL.
    + apply lr_refinesF_unfoldR. apply IHref_allL.
  - apply IHref12. observe_tau.
    pstep_reverse. apply lr_refines_existsL_inv. pstep. apply ref23.
  - eapply lr_refinesF_forallL. apply IHref12. assumption.
  - apply lr_refinesF_existsL. intros. apply H0. assumption.
  - apply lr_refinesF_unfoldL. apply IHref12. assumption.
  - apply IHref12. observe_tau. pstep_reverse.
    apply lr_refines_callL_inv. pstep. assumption.
Admitted.


(*** Proving other properties ***)


Section lr_refines_props.

Context {E1 E2 : EncType} {stk1 stk2 : FunStack} {R1 R2 : Type} {RR : Rel R1 R2}.
Context (funs1 : FrameTuple E1 stk1) (funs2 : FrameTuple E2 stk2).


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

(*
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
  - cbn. apply refinesF_forallR. intros.
    apply H0. intros. apply CIH. assumption.
  - cbn. eapply refinesF_existsR. apply IHlr_refinesF.
    intros. apply CIH. assumption.
  - cbn. eapply refinesF_forallL. apply IHlr_refinesF.
    intros. apply CIH. assumption.
  - cbn. apply refinesF_existsL. intros. apply H0. intros. apply CIH. assumption.
Qed.
*)

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
  hinduction H2 before r; intros; pclearbot.
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
  - pstep. apply lr_refinesF_forallR. intros.
    change
      (lr_refinesF funs1 funs2 RPre RPost RR
         (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) r)
         (observe (x <- go _ _ ot1;; k1 x))
         (observe ((x <- Tau (k a);; k2 x)))).
    pstep_reverse.
  - pstep. apply (lr_refinesF_existsR _ _ _ _ _ _ _ _ _ a).
    change
      (lr_refinesF funs1 funs2 RPre RPost RR
         (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) r)
         (observe (x <- go _ _ ot1;; k1 x))
         (observe ((x <- Tau (k a);; k2 x)))).
    pstep_reverse.
  - pstep. apply (lr_refinesF_forallL _ _ _ _ _ _ _ _ _ a).
    change
      (lr_refinesF funs1 funs2 RPre RPost RR
         (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) r)
         (observe ((x <- Tau (k a);; k1 x)))
         (observe (x <- go _ _ ot2;; k2 x))).
    pstep_reverse.
  - pstep. apply lr_refinesF_existsL. intros.
    change
      (lr_refinesF funs1 funs2 RPre RPost RR
         (upaco2 (lr_refines_ funs1 funs2 RPre RPost RR) r)
         (observe ((x <- Tau (k a);; k1 x)))
         (observe (x <- go _ _ ot2;; k2 x))).
    pstep_reverse.
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
