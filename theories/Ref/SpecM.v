From ITree Require Import
     Basics.Basics
     Basics.Tacs
     Basics.HeterogeneousRelations
     Basics.Monad
 .
From EnTree Require Import
     Basics.HeterogeneousRelations
     Basics.QuantType
     Basics.PolyList
     Core.EnTreeDefinition
     Core.SubEvent
     Eq.Eqit
     Ref.Padded
     Ref.EnTreeSpecDefinition
     Ref.FixTree
.
From Coq Require Import
  Arith.Arith
  Strings.String
  Lists.List
  Logic.Eqdep_dec
  Logic.EqdepFacts
  Eqdep EqdepFacts
  Morphisms
.

From Paco Require Import paco.

Local Open Scope entree_scope.
Local Open Scope list_scope.

Import Monads.
Import ProperNotations.


(**
 ** EncodingType and ReSum instances for defining SpecM
 **)

(* The error event type *)
Inductive ErrorE : Set :=
| mkErrorE : string -> ErrorE.

Global Instance EncodingType_ErrorE : EncodingType ErrorE := fun _ => Empty_set.

(* The event type for SpecM computations, given an underlying event type *)
Definition SpecE (E : EvType) : Type@{entree_u} :=
  SpecEvent (ErrorE + E).

(* The return type for a SpecEE effect in a SpecM computation *)
Definition SpecERet E (e:SpecE E) : Type@{entree_u} := encodes e.

Definition SpecEv E : EvType := Build_EvType (SpecE E) _.

Global Instance EncodingType_SpecE E : EncodingType (SpecE E) := SpecERet E.

Global Instance ReSum_SpecE_E (E : EvType) : ReSum E (SpecE E) :=
  fun e => Spec_vis (inr e).

Global Instance ReSumRet_SpecE_E (E : EvType) : ReSumRet E (SpecE E) :=
  fun _ r => r.

Global Instance ReSum_SpecE_Error (E : EvType) : ReSum ErrorE (SpecE E) :=
  fun e => Spec_vis (inl e).

Global Instance ReSumRet_SpecE_Error (E : EvType) : ReSumRet ErrorE (SpecE E) :=
  fun _ r => r.


(**
 ** The SpecM monad
 **)

Section SpecM.

Context {Tp} `{IsTpDesc Tp} {E : EvType}.

(* The SpecM monad is an entree spec over SpecE events *)
Definition SpecM A : Type := fixtree Tp (SpecEv E) A.

#[global] Instance Monad_SpecM : Monad SpecM := Monad_fixtree _ _.

(* The monadic operations on SpecM *)
Definition RetS {A} (a : A) : SpecM A := ret a.
Definition BindS {A B} (m : SpecM A) (k : A -> SpecM B) := bind m k.

Definition ForallS (A : Type) `{QuantType A} : SpecM A :=
  Fx_Vis (Spec_forall quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).
Definition ExistsS (A : Type) `{QuantType A} : SpecM A :=
  Fx_Vis (Spec_exists quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).

Definition AssumeS (P : Prop) : SpecM unit :=
  BindS (ForallS P) (fun _ => ret tt).
Definition AssertS (P : Prop) : SpecM unit :=
  BindS (ExistsS P) (fun _ => ret tt).

Definition TriggerS (e : E) : SpecM (encodes e) :=
  Fx_Vis (resum e : SpecEv E) (fun x => Fx_Ret x).

Definition ErrorS {A} (str : string) : SpecM A :=
  Fx_Vis ((Spec_vis (inl (mkErrorE str))) : SpecEv E)
    (fun (x:Empty_set) => match x with end).

Definition errorEntree {R} (s : string) : entree (SpecEv E) R :=
  Vis (Spec_vis (inl (mkErrorE s))) (fun v:void => match v with end).

Definition interp_SpecM {R} (t:SpecM R) : entree (SpecEv E) R :=
  interp_fixtree (@errorEntree R "Unbound function call") nil t.

End SpecM.
