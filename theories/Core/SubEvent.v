Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.

Require Import ITree.Basics.Basics.
Require Import HeterogeneousRelations EnTreeDefinition.


Class ReSum (E1 E2 : Type) : Type := resum : E1 -> E2.

Class ReSumRet E1 E2 `{EncodedType E1} `{EncodedType E2} `{ReSum E1 E2} : Type :=
  resum_ret : forall (e : E1), encodes (resum e) -> encodes e.

#[global] Instance ReSum_inl E1 E2 : ReSum E1 (E1 + E2) := inl.
#[global] Instance ReSum_inr E1 E2 : ReSum E2 (E1 + E2) := inr.
#[global] Instance ReSumRet_inl E1 E2 `{EncodedType E1} `{EncodedType E2} : ReSumRet E1 (E1 + E2) :=
  fun _ e => e.
#[global] Instance ReSumRet_inr E1 E2 `{EncodedType E1} `{EncodedType E2} : ReSumRet E2 (E1 + E2) :=
  fun _ e => e.

Definition trigger {E1 E2 : Type} `{EncodedType E1} `{EncodedType E2} `{ReSum E1 E2} `{ReSumRet E1 E2} 
           (e : E1) : entree E2 (encodes e) :=
  Vis (resum e) (fun x : encodes (resum e) => Ret (resum_ret e x)).

(* Use resum and resum_ret to map the events in an entree to another type *)
CoFixpoint resumEntree {E1 E2 : Type} `{EncodedType E1} `{EncodedType E2}
           `{ReSum E1 E2} `{ReSumRet E1 E2} A (t : entree E1 A) : entree E2 A :=
  match observe t with
  | RetF r => Ret r
  | TauF t => Tau (resumEntree A t)
  | VisF e k => Vis (resum e) (fun x => resumEntree A (k (resum_ret e x)))
  end.
