Require Import Coq.Logic.EqdepFacts.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.

Require Import ITree.Basics.Basics ITree.Basics.HeterogeneousRelations.

(* should this be polymorphic ? *)
Universe entree_u.

(** Types whose inhabitants represent another type *)
Class EncodingType (E : Type) := encodes : E -> Type@{entree_u}.

#[global] Instance EncodingSum (E1 E2 : Type@{entree_u}) `{EncodingType E1} `{EncodingType E2} : EncodingType (sum E1 E2) :=
  fun e12 => match e12 with 
          | inl e1 => encodes e1
          | inr e2 => encodes e2 end.

Notation Rel A B := (A -> B -> Prop).
Notation PostRel E1 E2 := (forall (e1 : E1) (e2 : E2), encodes e1 -> encodes e2 -> Prop).

Notation rcompose RR1 RR2 := (rel_compose RR2 RR1).

Variant SumPostRel {E1 E2 D1 D2} `{EncodingType E1} `{EncodingType E2} `{EncodingType D1} `{EncodingType D2}
        (RPost1 : PostRel E1 E2) (RPost2 : PostRel D1 D2) : PostRel (E1 + D1) (E2 + D2) :=
  | SumPostRel_inl (e1 : E1) (e2 : E2) a b : RPost1 e1 e2 a b -> SumPostRel RPost1 RPost2 (inl e1) (inl e2) a b
  | SumPostRel_inr (d1 : D1) (d2 : D2) a b : RPost2 d1 d2 a b -> SumPostRel RPost1 RPost2 (inr d1) (inr d2) a b
.

Variant RComposePostRel {E1 E2 E3} `{EncodingType E1} `{EncodingType E2} `{EncodingType E3}
        (RPre1 : Rel E1 E2) (RPre2 : Rel E2 E3) (RPost1 : PostRel E1 E2) (RPost2 : PostRel E2 E3) : PostRel E1 E3 :=
  | RComposePostRel_intro (e1 : E1) (e3 : E3) a c : 
    (forall e2, RPre1 e1 e2 -> RPre2 e2 e3 -> exists b, RPost1 e1 e2 a b /\ RPost2 e2 e3 b c) ->
    RComposePostRel RPre1 RPre2 RPost1 RPost2 e1 e3 a c.

Class ReflexivePostRel {E} `{EncodingType E} (PR : PostRel E E) : Prop :=
  refl_postrel : forall (e : E) a b, PR e e a b -> a = b.
