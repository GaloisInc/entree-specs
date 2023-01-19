Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.
Require Export Basics.Tactics.
From Coq Require Import
  Program
  Setoid
  Morphisms
  RelationClasses.


Require Import ITree.Basics.Basics ITree.Basics.HeterogeneousRelations.

(* should this be polymorphic ? *)
Universe entree_u.

Class EncodedType (E : Type) := encodes : E -> Type@{entree_u}.

#[global] Instance EncodedSum (E1 E2 : Type@{entree_u}) `{EncodedType E1} `{EncodedType E2} : EncodedType (sum E1 E2) :=
  fun e12 => match e12 with 
          | inl e1 => encodes e1
          | inr e2 => encodes e2 end.

Notation Rel A B := (A -> B -> Prop).
Notation PostRel E1 E2 := (forall (e1 : E1) (e2 : E2), encodes e1 -> encodes e2 -> Prop).

Notation rcompose RR1 RR2 := (rel_compose RR2 RR1).

Variant SumPostRel {E1 E2 D1 D2} `{EncodedType E1} `{EncodedType E2} `{EncodedType D1} `{EncodedType D2} 
        (RPost1 : PostRel E1 E2) (RPost2 : PostRel D1 D2) : PostRel (E1 + D1) (E2 + D2) :=
  | SumPostRel_inl (e1 : E1) (e2 : E2) a b : RPost1 e1 e2 a b -> SumPostRel RPost1 RPost2 (inl e1) (inl e2) a b
  | SumPostRel_inr (d1 : D1) (d2 : D2) a b : RPost2 d1 d2 a b -> SumPostRel RPost1 RPost2 (inr d1) (inr d2) a b
.

Variant RComposePostRel {E1 E2 E3} `{EncodedType E1} `{EncodedType E2} `{EncodedType E3}
        (RPre1 : Rel E1 E2) (RPre2 : Rel E2 E3) (RPost1 : PostRel E1 E2) (RPost2 : PostRel E2 E3) : PostRel E1 E3 :=
  | RComposePostRel_intro (e1 : E1) (e3 : E3) a c : 
    (forall e2, RPre1 e1 e2 -> RPre2 e2 e3 -> exists b, RPost1 e1 e2 a b /\ RPost2 e2 e3 b c) ->
    RComposePostRel RPre1 RPre2 RPost1 RPost2 e1 e3 a c.

Definition PostRelEq {E1 E2} `{EncodedType E1} `{EncodedType E2} :
  PostRel E1 E2 -> PostRel E1 E2 -> Prop :=
  fun RPost1 RPost2 => forall e1 e2 a b, RPost1 e1 e2 a b <-> RPost2 e1 e2 a b.

#[global] Instance PostRelEqEquiv {E1 E2} `{EncodedType E1} `{EncodedType E2} :
  Equivalence (@PostRelEq E1 E2 _ _).
Proof.
  constructor.
  - repeat intro. reflexivity.
  - repeat intro. symmetry. apply H1.
  - repeat intro. etransitivity; eauto.
Qed.

Definition FlipPostRel {E1 E2} `{EncodedType E1} `{EncodedType E2} : PostRel E1 E2 -> PostRel E2 E1 :=
  fun RPost e2 e1 b a => RPost e1 e2 a b.

Definition SymmetricPostRel {E} `{EncodedType E} (RPost : PostRel E E) : Prop :=
  forall e1 e2 a b, RPost e1 e2 a b -> RPost e2 e1 b a.

Theorem symmetric_postrel E `{enc : EncodedType E} (RPost : PostRel E E) :
  SymmetricPostRel RPost ->
  PostRelEq RPost (FlipPostRel RPost).
Proof.
  intros Hsym. split; intros.
  - red. auto.
  - apply Hsym. auto.
Qed.

(* need to think carefully about this definition *)
Definition TransitivePostRel {E : Type} `{enc : EncodedType E} (RPre : Rel E E) (RPost : PostRel E E) 
  : Prop :=
  forall (e1 e3 : E) (a : encodes e1) (c : encodes e3),
    (forall e2, RPre e1 e2 -> RPre e2 e3 -> exists b, RPost e1 e2 a b /\ RPost e2 e3 b c) <-> RPost e1 e3 a c.

Theorem transitive_rcompose_postrel E `{enc : EncodedType E} (RPre : Rel E E) (RPost : PostRel E E) :
  TransitivePostRel RPre RPost ->
  PostRelEq RPost (RComposePostRel RPre RPre RPost RPost).
Proof.
  intro H. red in H. intros e1 e3 a c.
  split.
  - intros Hac. econstructor. eapply H. auto.
  - intros. inversion H0. inj_existT. subst.
    eapply H. eauto.
Qed.
