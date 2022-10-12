From EnTree Require Import Basics.HeterogeneousRelations.

From Coq Require Import
     Logic.FunctionalExtensionality
     Lists.List.

(* The cardinalities representable inside Type universe 0; to avoid defining the
cardinality of a proposition, we include propositions themselves as
cardinalities; we also include some "helpers" like lists to make cardinalities
easier to define *)
Inductive Cardinality : Type :=
| Card_nat
| Card_prop (P:Prop)
| Card_pair (k1 k2:Cardinality)
| Card_list (k:Cardinality)
| Card_fun (k1 k2:Cardinality).

Fixpoint encodes_Cardinality (k: Cardinality) : Type :=
  match k with
  | Card_nat => nat
  | Card_prop P => P
  | Card_pair k1 k2 => encodes_Cardinality k1 * encodes_Cardinality k2
  | Card_list k => list (encodes_Cardinality k)
  | Card_fun k1 k2 => encodes_Cardinality k1 -> encodes_Cardinality k2
  end.
Instance EncodingType_Cardinality : EncodingType Cardinality :=
  encodes_Cardinality.

(* A type that has a cardinality is one whose elements can be enumerated by a
function from a Cardinality that is constructively surjective, i.e., where we
can constructively find an input that maps to any element of the output type *)
Class HasCard (A:Type) : Type :=
  { cardinality : Cardinality;
    card_enum : encodes cardinality -> A;
    card_enum_inv : A -> encodes cardinality;
    card_enum_surjective : forall a:A, card_enum (card_enum_inv a) = a }.

Instance HasCard_Prop (P:Prop) : HasCard P :=
  { cardinality := Card_prop P;
    card_enum := fun pf => pf;
    card_enum_inv := fun pf => pf;
    card_enum_surjective := fun pf => eq_refl pf }.

Instance HasCard_nat : HasCard nat :=
  { cardinality := Card_nat;
    card_enum := fun n => n;
    card_enum_inv := fun n => n;
    card_enum_surjective := fun n => eq_refl n }.

Program Instance HasCard_pair (A B:Type) `{HasCard A} `{HasCard B} : HasCard (A * B) :=
  { cardinality := Card_pair (cardinality (A:=A)) (cardinality (A:=B));
    card_enum := fun p => (card_enum (fst p), card_enum (snd p));
    card_enum_inv := fun p => (card_enum_inv (fst p), card_enum_inv (snd p)) }.
Next Obligation.
  repeat rewrite card_enum_surjective. reflexivity.
Defined.

Program Instance HasCard_fun (A B:Type) `{HasCard A} `{HasCard B} : HasCard (A -> B) :=
  { cardinality := Card_fun (cardinality (A:=A)) (cardinality (A:=B));
    card_enum := fun f x => card_enum (f (card_enum_inv x));
    card_enum_inv := fun f x => card_enum_inv (f (card_enum x)) }.
Next Obligation.
  apply functional_extensionality. intro x.
  repeat rewrite card_enum_surjective. reflexivity.
Defined.

Program Instance HasCard_list (A:Type) `{HasCard A} : HasCard (list A) :=
  { cardinality := Card_list (cardinality (A:=A));
    card_enum := fun l => map card_enum l;
    card_enum_inv := fun l => map card_enum_inv l }.
Next Obligation.
  etransitivity; [ | apply map_id ]. rewrite map_map. apply map_ext.
  intro. apply card_enum_surjective.
Defined.
