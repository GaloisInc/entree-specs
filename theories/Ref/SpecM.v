
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

Section SpecM.
Context {Ops:TpExprOps}.


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


(**
 ** Specification Elements of Type Descriptions
 **)

(* A finite or infinite sequence, where the latter is represented as a monadic
function from the natural number index to the element at that index *)
Definition mseq (E:EvType) len (A:Type@{entree_u}) : Type@{entree_u} :=
  match len with
  | TCNum n => VectorDef.t A n
  | TCInf => nat -> SpecM E A
  end.

(* Elements of type descriptions that use monadic functions instead of FunIxs.
If the Boolean flag is true, we are translating a monadic function type, and
should use funElem *)
Fixpoint specElemEnv (E:EvType) env isf T : Type@{entree_u} :=
  match T with
  | Tp_M R => SpecM E (specElemEnv E env false R)
  | Tp_Pi K B =>
      forall (elem:kindElem K), specElemEnv E (envConsElem elem env) true B
  | Tp_Arr A B =>
      specElemEnv E env false A -> specElemEnv E env true B
  | Tp_Kind K =>
      if isf then unit else kindElem K
  | Tp_Pair A B =>
      if isf then unit else specElemEnv E env false A * specElemEnv E env false B
  | Tp_Sum A B =>
      if isf then unit else specElemEnv E env false A + specElemEnv E env false B
  | Tp_Sigma K B =>
      if isf then unit else
        { elem: kindElem K & specElemEnv E (envConsElem elem env) false B }
  | Tp_Seq A e =>
      if isf then unit else mseq E (evalTpExpr env e) (specElemEnv E env false A)
  | Tp_Void => if isf then unit else Empty_set
  | Tp_Ind A =>
      if isf then unit else indElem nil (unfoldIndTpDesc env A)
  | Tp_Var var =>
      if isf then unit else indElem nil (evalVar 0 env Kind_Tp var)
  | Tp_TpSubst A B =>
      if isf then unit else
        specElemEnv E (envConsElem (K:=Kind_Tp) (tpSubst 0 env B) env) false A
  | Tp_ExprSubst A EK e =>
      if isf then unit else
        specElemEnv E (envConsElem (K:=Kind_Expr EK) (evalTpExpr env e) env) false A
  end.

Definition specElem E T := specElemEnv E nil false T.

Definition specFun E T := specElemEnv E nil true T.

Definition specFunElem E env T := funElem (SpecEv E) env T.

(* Call a function index in a specification *)
Definition callIx {E T} (f : FunIx T) : specFunElem E nil T :=
  funInterpToElem (fun args => Fx_Call (MkFunCall T f args) (fun x => Fx_Ret x)).

(* Create a function index from a specification function in a specification *)
Definition lambdaIx {E T} (f : specFunElem E nil T) : SpecM E (FunIx T) :=
  Fx_MkFuns (fun _ => mkMultiFxInterp1 T (funElemToInterp f))
    (fun ixs => Fx_Ret (headFunIx ixs)).

(* FIXME: maybe don't need this...? *)
Definition tpOrFunElem E env (isf:bool) T :=
  if isf then funElem E env T else tpElemEnv env T.

(* FIXME: maybe call tpElem tpIxElem and funElem ixFunElem? *)

FIXME: need a function to substitute env into T (note: they aren't equal bc of Tp_Var)

Fixpoint tpToSpecElem E env T : tpElemEnv env T ->
                                specElemEnv E env false T :=
  match T return tpElemEnv env T -> specElemEnv E env false T with
  | Tp_M R => fun ix => Functor.fmap (tpToSpecElem E env R) (callIx ix)
  | Tp_Pi K B =>
      fun ix elem =>
        funToSpecElem E (envConsElem elem env) B (callIx ix elem)
(*
  | Tp_Arr A B => FunIx (tpSubst 0 env (Tp_Arr A B))
  | Tp_Kind K => kindElem K
  | Tp_Pair A B => tpElemEnv env A * tpElemEnv env B
  | Tp_Sum A B => tpElemEnv env A + tpElemEnv env B
  | Tp_Sigma K B => { elem: kindElem K & tpElemEnv (envConsElem elem env) B }
  | Tp_Seq A e =>
      match evalTpExpr env e with
      | TCInf => FunIx (Tp_Arr Tp_Nat (tpSubst 0 env A))
      | TCNum n => VectorDef.t (tpElemEnv env A) n
      end
  | Tp_Void => Empty_set
  | Tp_Ind A => indElem nil (unfoldIndTpDesc env A)
  | Tp_Var var => indElem nil (evalVar 0 env Kind_Tp var)
  | Tp_TpSubst A B =>
      tpElemEnv (@envConsElem Kind_Tp (tpSubst 0 env B) env) A
  | Tp_ExprSubst A EK e =>
      tpElemEnv (@envConsElem (Kind_Expr EK) (evalTpExpr env e) env) A
*)
  end
with
specToTpElem E env T : specElemEnv E env false T ->
                       SpecM E (tpElemEnv env T) :=
  match T return specElemEnv E env false T -> SpecM E (tpElemEnv env T) with

  end
with
funToSpecElem E env T : specFunElem E env T ->
                        specElemEnv E env true T :=
  match T return specFunElem E env T -> specElemEnv E env true T with
  | Tp_M R => Functor.fmap (tpToSpecElem E env R)
(*
  | Tp_Pi K B => FunIx (tpSubst 0 env (Tp_Pi K B))
  | Tp_Arr A B => FunIx (tpSubst 0 env (Tp_Arr A B))
  | Tp_Kind K => kindElem K
  | Tp_Pair A B => tpElemEnv env A * tpElemEnv env B
  | Tp_Sum A B => tpElemEnv env A + tpElemEnv env B
  | Tp_Sigma K B => { elem: kindElem K & tpElemEnv (envConsElem elem env) B }
  | Tp_Seq A e =>
      match evalTpExpr env e with
      | TCInf => FunIx (Tp_Arr Tp_Nat (tpSubst 0 env A))
      | TCNum n => VectorDef.t (tpElemEnv env A) n
      end
  | Tp_Void => Empty_set
  | Tp_Ind A => indElem nil (unfoldIndTpDesc env A)
  | Tp_Var var => indElem nil (evalVar 0 env Kind_Tp var)
  | Tp_TpSubst A B =>
      tpElemEnv (@envConsElem Kind_Tp (tpSubst 0 env B) env) A
  | Tp_ExprSubst A EK e =>
      tpElemEnv (@envConsElem (Kind_Expr EK) (evalTpExpr env e) env) A
*)
  end
with
specElemToFun E env T : specElemEnv E env true T ->
                        specFunElem E env T :=
  match T return specElemEnv E env true T -> SpecM E (specFunElem E env true T) with

  end.



FIXME HERE NOW:
- make 4 corecursive functions, for tpElem -> specElem and vice versa and for
  isf = true and isf = false
- The specElem -> tpElem funs are monadic, becaause they need to call LambdaS
- for the isf = true funs, maintain an argument context / extended env that
  contains Pi and Arr args; also, the input is not a funElem T but rather a
  funElem (absArgs args T), where absArgs abstracts over the Pi and Arr types
  in args




FIXME HERE NOW: old stuff below

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


(**
 ** Defining a multi-way fixed point
 **)

(* Build the multi-arity function type FunIx T1 -> ... FunIx Tn -> A *)
Fixpoint arrowIxs (Ts : list TpDesc) (A : Type@{entree_u}) : Type@{entree_u} :=
  match Ts with
  | nil => A
  | T :: Ts' => FunIx T -> arrowIxs Ts' A
  end.

(* Apply a multi-arity function over indexes to a list of indexes *)
Fixpoint applyArrowIxs {Ts A} : arrowIxs Ts A -> FunIxs Ts -> A :=
  match Ts return arrowIxs Ts A -> FunIxs Ts -> A with
  | nil => fun f _ => f
  | T :: Ts' => fun f ixs => applyArrowIxs (f (headFunIx ixs)) (tailFunIxs ixs)
  end.

(* A tuple of spec functions of the given types *)
Fixpoint specFuns E Ts : Type@{entree_u} :=
  match Ts with
  | nil => unit
  | T :: Ts' => specFun E nil T * specFuns E Ts'
  end.

(* FIXME: move this somewhere more relevant *)
Arguments MultiFxInterp {_ _} _ _.

(* Convert a specFuns tuple to a MultiFxInterp *)
Fixpoint specFunsToMultiInterp {E Ts} : specFuns E Ts -> MultiFxInterp (SpecEv E) Ts :=
  match Ts return specFuns E Ts -> MultiFxInterp (SpecEv E) Ts with
  | nil => fun _ => mkMultiFxInterp0
  | T :: Ts' =>
      fun fs =>
        consMultiFxInterp (funElemToInterp (fst fs)) (specFunsToMultiInterp (snd fs))
  end.

(*
(* The type of a tuple of spec functions of types Us that take in FunIxs Ts *)
Fixpoint arrowIxsSpecFuns E (Ts Us : list TpDesc) : Type@{entree_u} :=
  match Us with
  | nil => unit
  | U :: Us' => arrowIxs Ts (specFun E nil U) * arrowIxsSpecFuns E Ts Us'
  end.

(* Apply an arrowIxsSpecFuns list to a list of FunIxs to get a specFuns list *)
Fixpoint applyArrowIxsSpecFuns {E Ts Us} : arrowIxsSpecFuns E Ts Us -> FunIxs Ts ->
                                           specFuns E Us :=
  match Us return arrowIxsSpecFuns E Ts Us -> FunIxs Ts -> specFuns E Us with
  | nil => fun _ _ => tt
  | U :: Us' => fun fs ixs => (applyArrowIxs (fst fs) ixs,
                                applyArrowIxsSpecFuns (snd fs) ixs)
  end.
*)

Definition MultiFixBodies E Ts : Type@{entree_u} :=
  arrowIxs Ts (specFuns E Ts).

Definition MultiFixS {E Ts} (funs : MultiFixBodies E Ts) : SpecM E (FunIxs Ts) :=
  Fx_MkFuns
    (fun ixs => specFunsToMultiInterp (applyArrowIxs funs ixs))
    (fun ixs => Fx_Ret ixs).

Definition LetRecS {E Ts A}
  (funs : MultiFixBodies E Ts) (body : arrowIxs Ts (SpecM E A)) : SpecM E A :=
  BindS (MultiFixS funs) (applyArrowIxs body).


End SpecM.
