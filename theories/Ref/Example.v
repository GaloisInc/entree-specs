From ITree Require Import
     Basics.Basics
     Basics.Tacs
     Basics.HeterogeneousRelations
 .
From ITree Require Import Basics.Monad.
From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Core.SubEvent
     Eq.Eqit
     Ref.Padded
     Ref.EnTreeSpecDefinition
     Ref.MRecSpec
     Ref.SpecM
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope list_scope.


Variant evenoddE : Type:=
  | even (n : nat) : evenoddE
  | odd  (n : nat) : evenoddE.
Instance EncodingType_evenoddE : EncodingType evenoddE := fun _ => bool.

Variant voidE : Type :=.

Instance EncodingType_voidE : EncodingType voidE := fun _ => False.

Definition evenodd_body : forall eo : evenoddE, (entree (evenoddE + voidE)) (encodes eo) :=
  fun eo =>
    match eo with
    | even n => if Nat.eqb n 0
               then Ret true
               else trigger (odd (n - 1))
    | odd  n => if Nat.eqb n 0
               then Ret false
               else trigger (even (n - 1))
    end.
Definition evenodd : evenoddE -> entree voidE bool :=
  mrec evenodd_body.
