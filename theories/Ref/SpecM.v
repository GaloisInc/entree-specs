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
     Ref.MRecSpec
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
Definition SpecE (E : EvType@{entree_u}) : Type@{entree_u} :=
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

(* The SpecM monad is an entree spec over FunStackE events *)
Definition SpecM (E:EvType) stack A : Type :=
  fixtree (SpecEv E) stack A.

#[global] Instance Monad_SpecM {E stk} : Monad (SpecM E stk) := Monad_fixtree.

(* The monadic operations on SpecM *)
Definition RetS {E} {stk A} (a : A) : SpecM E stk A := ret a.
Definition BindS {E} {stk A B} (m : SpecM E stk A) (k : A -> SpecM E stk B) :=
  bind m k.

Definition ForallS {E} {stk} (A : Type) `{QuantType A} : SpecM E stk A :=
  Fx_Vis (Spec_forall quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).
Definition ExistsS {E} {stk} (A : Type) `{QuantType A} : SpecM E stk A :=
  Fx_Vis (Spec_exists quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).

Definition AssumeS {E} {stk} (P : Prop) : SpecM E stk unit :=
  BindS (ForallS P) (fun _ => ret tt).
Definition AssertS {E} {stk} (P : Prop) : SpecM E stk unit :=
  BindS (ExistsS P) (fun _ => ret tt).

Definition TriggerS {E:EvType} {stk} (e : E) : SpecM E stk (encodes e) :=
  Fx_Vis (resum e : SpecEv E) (fun x => Fx_Ret x).

Definition ErrorS {E} {stk} A (str : string) : SpecM E stk A :=
  Fx_Vis ((Spec_vis (inl (mkErrorE str))) : SpecEv E)
    (fun (x:Empty_set) => match x with end).


(**
 ** Making and calling tpElems
 **)

(* Re-exporting tpElem from the SpecM module *)
Definition tpElem := tpElem.

(* A tpElem specifically of SpecM type *)
Definition specElem E stk R := tpElem E stk (Tp_M R).

(* A tpElem specifically of pi type *)
Definition piElem E stk A B := tpElem E stk (Tp_Pi A B).

(* A tpElem specifically of arrow type *)
Definition arrowElem E stk A B := tpElem E stk (Tp_Arr A B).


(* An element of a type description that uses SpecM for the monadic type *)
Fixpoint SpecElem E stk T : Type@{entree_u} :=
  match T with
  | Tp_M R => SpecM E stk (tpElem (SpecEv E) stk R)
  | Tp_Pi A B => forall a, SpecElem E stk (B a)
  | Tp_Arr A B => tpElem (SpecEv E) stk A -> SpecElem E stk B
  | Tp_SType A => tpElem (SpecEv E) stk (Tp_SType A)
  | Tp_Pair A B => tpElem (SpecEv E) stk (Tp_Pair A B)
  | Tp_Sum A B => tpElem (SpecEv E) stk (Tp_Sum A B)
  | Tp_Sigma A B => tpElem (SpecEv E) stk (Tp_Sigma A B)
  end.

Definition PolySpecElem E stk T : Type@{entree_u} :=
  forall stk' (incl : stackIncl stk stk'), SpecElem E stk' T.

Definition liftPolySpecElem {E stk stk' T} (incl : stackIncl stk stk')
  (elem : PolySpecElem E stk T) : PolySpecElem E stk' T :=
  fun stk'' incl' => elem stk'' (compListIncl incl incl').

Definition lift0PolySpecElem {E stk U T} (elem : PolySpecElem E stk T)
  : PolySpecElem E (U :: stk) T :=
  liftPolySpecElem (stepListIncl (incl1Base U stk)) elem.

Definition applyPolySpecElem {E stk T U}
  (f : PolySpecElem E stk (Tp_Arr T U)) (arg : tpElem (SpecEv E) stk T)
  : PolySpecElem E stk U :=
  fun stk' incl => f stk' incl (liftTpElem incl arg).

Fixpoint SpecElemToMonoInterp {E stk} T : SpecElem E stk T -> MonoInterp (SpecEv E) stk T :=
  match T return SpecElem E stk T -> MonoInterp (SpecEv E) stk T with
  | Tp_M R => fun elem args => elem
  | Tp_Pi A B =>
      fun elem args =>
        SpecElemToMonoInterp (B (projT1 args)) (elem (projT1 args)) (projT2 args)
  | Tp_Arr A B =>
      fun elem args =>
        SpecElemToMonoInterp B (elem (fst args)) (snd args)
  | Tp_SType A => fun elem args => match args with end
  | Tp_Pair A B => fun elem args => match args with end
  | Tp_Sum A B => fun elem args => match args with end
  | Tp_Sigma A B => fun elem args => match args with end
  end.

Definition SpecElemToInterp {E stk T} (elem: PolySpecElem E stk T)
  : FixTree.FxInterp (SpecEv E) stk T :=
  fun stk' incl => @SpecElemToMonoInterp E stk' T (elem stk' incl).

Fixpoint InterpToSpecElem {E stk} T
 : isFunTp T -> FxInterp (SpecEv E) stk T -> SpecElem E stk T :=
  match T return isFunTp T -> FxInterp (SpecEv E) stk T -> SpecElem E stk T with
  | Tp_M R => fun _ m => m stk (reflListIncl _) tt
  | Tp_Pi A B => fun isfun f a =>
                   InterpToSpecElem (B a) (isfun a)
                     (fun stk' incl args => f stk' incl (existT _ a args))
  | Tp_Arr A B =>
      fun isfun f arg =>
        InterpToSpecElem B isfun (fun stk' incl args =>
                                    f stk' incl (liftTpElem incl arg, args))
  | Tp_SType _ => fun isfun => match isfun with end
  | Tp_Pair _ _ => fun isfun => match isfun with end
  | Tp_Sum _ _ => fun isfun => match isfun with end
  | Tp_Sigma _ _ => fun isfun => match isfun with end
  end.

Definition callStkFun {E stk T} (stkf : StkFun stk T) : SpecElem E stk T :=
  match stkf with
  | MkStkFun _ _ n isn isfun =>
      InterpToSpecElem T isfun
        (fun stk' incl args =>
           Fx_Call (MkStackCall _ _ T
                      (applyListIncl incl n) (applyListInclNth incl isn) args)
             (fun x => Fx_Ret x))
  end.

Fixpoint CallS {E stk T} : tpElem (SpecEv E) stk T -> SpecElem E stk T :=
  match T return tpElem (SpecEv E) stk T -> SpecElem E stk T with
  | Tp_M R =>
      fun elem => match elem with
                  | inl stkf => callStkFun stkf
                  | inr m => embedEntree m
                  end
  | Tp_Pi A B =>
      fun elem => match elem with
                  | inl stkf => callStkFun stkf
                  | inr f => fun a => CallS (f a)
                  end
  | Tp_Arr A B =>
      fun elem => match elem with
                  | inl stkf => callStkFun stkf
                  | inr f => fun arg => CallS (f stk (reflListIncl _) arg)
                  end
  | Tp_SType _ => fun elem => elem
  | Tp_Pair _ _ => fun elem => elem
  | Tp_Sum _ _ => fun elem => elem
  | Tp_Sigma _ _ => fun elem => elem
  end.


Definition fixS {E stk T} (isfun : isFunTp T) (body : PolySpecElem E stk (Tp_Arr T T))
  : SpecElem E stk T :=
  InterpToSpecElem (stk:=stk) T isfun
    (fun stk' incl args =>
       Fx_Fix (SpecElemToInterp (liftPolySpecElem (consListIncl _ incl)
                                   (applyPolySpecElem
                                      (lift0PolySpecElem body)
                                      (tpElem0 isfun))))
         args (fun x => Fx_Ret x)).


FIXME: how to define mkTpElem?

Fixpoint mkTpElem {E stk T} : SpecElem E nil T -> tpElem (SpecEv E) stk T :=
  match T return SpecElem E nil T -> tpElem (SpecEv E) stk T with
  | Tp_M R => fun m => inr (interp_fixtree_nil
                              (Functor.fmap (liftTpElem (nilListIncl _)) m))
  | Tp_Pi A B => fun f => inr (fun a => mkTpElem (f a))
  | Tp_Arr A B =>
      fun f stk' incl => inr (fun arg => )
  end.
