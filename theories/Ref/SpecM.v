
From EnTree Require Import
     Basics.HeterogeneousRelations
     Basics.QuantType
     Core.EnTreeDefinition
     Core.SubEvent
     Ref.EnTreeSpecDefinition
     Ref.FixTree
     Ref.TpDesc
.
From Coq Require Import
  Arith.Arith
  Strings.String
  Lists.List
.

Import Monads.


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

(* The SpecM monad is an entree spec over SpecE events *)
Definition SpecM (E:EvType) A : Type := fixtree TpDesc (SpecEv E) A.

#[global] Instance Monad_SpecM E : Monad (SpecM E) := Monad_fixtree _ _.

(* The monadic operations on SpecM *)
Definition RetS {E A} (a : A) : SpecM E A := ret a.
Definition BindS {E A B} (m : SpecM E A) (k : A -> SpecM E B) := bind m k.

Definition ForallS {E} (A : Type) `{QuantType A} : SpecM E A :=
  Fx_Vis (Spec_forall quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).
Definition ExistsS {E} (A : Type) `{QuantType A} : SpecM E A :=
  Fx_Vis (Spec_exists quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).

Definition AssumeS {E} (P : Prop) : SpecM E unit :=
  BindS (ForallS P) (fun _ => ret tt).
Definition AssertS {E} (P : Prop) : SpecM E unit :=
  BindS (ExistsS P) (fun _ => ret tt).

Definition TriggerS {E:EvType} (e : E) : SpecM E (encodes e) :=
  Fx_Vis (resum e : SpecEv E) (fun x => Fx_Ret x).

Definition ErrorS {E A} (str : string) : SpecM E A :=
  Fx_Vis ((Spec_vis (inl (mkErrorE str))) : SpecEv E)
    (fun (x:Empty_set) => match x with end).

Definition errorEntree {E R} (s : string) : entree (SpecEv E) R :=
  Vis (Spec_vis (inl (mkErrorE s))) (fun v:Empty_set => match v with end).

Definition interp_SpecM {E R} (t:SpecM E R) : entree (SpecEv E) R :=
  interp_fixtree (@errorEntree E R "Unbound function call") nil t.

Definition CallS {E T} (f : FunIx T) : funElem E nil T :=
  funInterpToElem (fun args => Fx_Call (MkFunCall T f args) (fun x => Fx_Ret x)).
