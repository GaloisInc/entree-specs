
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

(* Specification combinators as monadic operations *)
Definition ForallS {E} (A : Type) `{QuantType A} : SpecM E A :=
  Fx_Vis (Spec_forall quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).
Definition ExistsS {E} (A : Type) `{QuantType A} : SpecM E A :=
  Fx_Vis (Spec_exists quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).

(* Assumptions and assertions as monadic operations *)
Definition AssumeS {E} (P : Prop) : SpecM E unit :=
  BindS (ForallS P) (fun _ => ret tt).
Definition AssertS {E} (P : Prop) : SpecM E unit :=
  BindS (ExistsS P) (fun _ => ret tt).

(* Trigger a domain-specific event in the E type *)
Definition TriggerS {E:EvType} (e : E) : SpecM E (encodes e) :=
  Fx_Vis (resum e : SpecEv E) (fun x => Fx_Ret x).

(* Signal an error *)
Definition ErrorS {E A} (str : string) : SpecM E A :=
  Fx_Vis ((Spec_vis (inl (mkErrorE str))) : SpecEv E)
    (fun (x:Empty_set) => match x with end).

(* An error computation in the underlying entree type, to define interp_SpecM *)
Definition errorEntree {E R} (s : string) : entree (SpecEv E) R :=
  Vis (Spec_vis (inl (mkErrorE s))) (fun v:Empty_set => match v with end).

(* Interpret a SpecM computation as an entree *)
Definition interp_SpecM {E R} (t:SpecM E R) : entree (SpecEv E) R :=
  interp_fixtree (@errorEntree E R "Unbound function call") nil t.

(* An element of type T as a specification monad function *)
Definition specFun E env T := funElem (SpecEv E) env T.

(* Call a function index in a specification *)
Definition CallS {E T} (f : FunIx T) : specFun E nil T :=
  funInterpToElem (fun args => Fx_Call (MkFunCall T f args) (fun x => Fx_Ret x)).

(* Create a function index from a specification function in a specification *)
Definition LambdaS {E T} (f : specFun E nil T) : SpecM E (FunIx T) :=
  Fx_MkFuns (fun _ => mkMultiFxInterp1 T (funElemToInterp f))
    (fun ixs => Fx_Ret (headFunIx ixs)).

(* Create a lambda as a fixed-point that can call itself. Note that the type of
   f, FunIx T -> specFun E nil T, is the same as specFun E nil (Tp_Arr T T)
   when T is a monadic function type. *)
Definition FixS {E T} (f: FunIx T -> specFun E nil T) : SpecM E (FunIx T) :=
  Fx_MkFuns
    (fun ixs => mkMultiFxInterp1 T (funElemToInterp (f (headFunIx ixs))))
    (fun ixs => Fx_Ret (headFunIx ixs)).


FIXME: finish defining MultiFixS


(**
 ** Defining a multi-way fixed point
 **)

Fixpoint arrowIxs (Ts : list TpDesc) (A : Type@{entree_u}) : Type@{entree_u} :=
  match Ts with
  | nil => A
  | T :: Ts' => FunIx T -> arrowIxs Ts' A
  end.

Definition isSpecTp T : Prop :=
  match T with
  | Tp_M _ => True
  | Tp_Pi _ _ => True
  | Tp_Arr _ _ => True
  | _ => False
  end.

(* A tuple of spec functions of the given types *)
Fixpoint specFuns E Ts : Type@{entree_u} :=
  match Ts with
  | nil => unit
  | T :: Ts' => specFun E nil T * specFuns E Ts'
  end.

(* The type of a tuple of spec functions of types Us that take in FunIxs Ts *)
Fixpoint arrowSpecFuns E (Ts Us : list TpDesc) : Type@{entree_u} :=
  match Us with
  | nil => unit
  | U :: Us' => arrowIxs Ts (specFun E nil U) * arrowSpecFuns E Ts Us'
  end.

Definition MultiFixBodies E Ts : Type@{entree_u} :=
  arrowSpecFuns E Ts Ts.


Definition funIxToElem {T} : isSpecTp T -> FunIx T -> tpElem nil T :=
  match T return isSpecTp T -> FunIx T -> tpElem nil T with
  | Tp_M _ => fun _ ix => ix
  | Tp_Pi _ _ => fun _ ix => ix
  | Tp_Arr _ _ => fun _ ix => ix
  | _ => fun (pf:False) _ => match pf with end
  end.

Fixpoint multiFixS {E} (Ts : list TpDesc) : MultiFixBodies E Ts ->
                                            SpecM E (specFuns E Ts) :=
  match Ts return MultiFixBodies E Ts -> SpecM E (specFuns E Ts) with
  end.
