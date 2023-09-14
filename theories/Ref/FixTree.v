
From ExtLib Require Import
  Structures.Functor
  Structures.Applicative
  Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.Tacs
     Basics.HeterogeneousRelations
     Basics.Monad
 .
From EnTree Require Import
     Basics.HeterogeneousRelations
     Basics.QuantType
     Core.EnTreeDefinition
     Core.SubEvent
     Eq.Eqit
     Ref.Padded
     Ref.EnTreeSpecDefinition
     Ref.MRecSpec
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


(** Event types **)

(* An event type = a type of events plus their return types *)
Record EvType : Type :=
  { evTypeType :> Type@{entree_u};
    evRetType : EncodingType evTypeType }.

Global Instance EncodingType_EvType (E:EvType) : EncodingType E :=
  evRetType E.

(* The error event type *)
Inductive ErrorE : Set :=
| mkErrorE : string -> ErrorE.

Global Instance EncodingType_ErrorE : EncodingType ErrorE := fun _ => Empty_set.


(** Type Descriptions **)

(* A type acts as a type description if it has a type of input and output types
for functions *)
Class IsTpDesc (Tp:Type@{entree_u}) : Type :=
  { FunInput : Tp -> Type@{entree_u};
    FunOutput : forall {T}, FunInput T -> Type@{entree_u};
    dec_eq_Tp : forall (T U : Tp), {T=U} + {T<>U} }.


(*
(* Simple, non-dependent type descriptions *)
Inductive SimpleDesc : Type@{entree_u} :=
| SimpTp_Void : SimpleDesc
| SimpTp_Unit : SimpleDesc
(* | SimpTp_Prop (P:Prop) : SimpleDesc *) (* Cannot decide equality of Props! *)
| SimpTp_Nat : SimpleDesc
| SimpTp_Sum (A B : SimpleDesc) : SimpleDesc
.

Definition dec_eq_SimpleDesc (T U:SimpleDesc) : { T = U } + {~ T = U}.
Proof. decide equality. Defined.

(* Decode a simple type description to a type *)
Fixpoint stpElem (d : SimpleDesc) : Type@{entree_u} :=
  match d with
  | SimpTp_Void => Empty_set
  | SimpTp_Unit => unit
  | SimpTp_Nat => nat
  | SimpTp_Sum A B => stpElem A + stpElem B
  end.

(* General type descriptions, parameterized by whether they are a monadic type *)
Inductive TpDesc : Type@{entree_u} :=
(* Monadic function types *)
| Tp_M (R : TpDesc) : TpDesc
| Tp_Pi (A : SimpleDesc) (B : stpElem A -> TpDesc) : TpDesc
| Tp_Arr (A : TpDesc) (B : TpDesc) : TpDesc

(* First-order types *)
| Tp_SType (A : SimpleDesc) : TpDesc
| Tp_Pair (A : TpDesc) (B : TpDesc) : TpDesc
| Tp_Sum (A : TpDesc) (B : TpDesc) : TpDesc
| Tp_Sigma (A : SimpleDesc) (B : stpElem A -> TpDesc) : TpDesc
.

Definition dec_eq_TpDesc (T U:TpDesc) : { T = U } + {~ T = U}.
Proof.
  revert U; induction T; intro U; destruct U; try (right; intro e; discriminate e).
  - destruct (IHT U) as [ e | neq ]; [ rewrite e; left; reflexivity | ].
    right; intro e; refine (neq _); inversion e; reflexivity.
Admitted.
*)

Section FixTree.

Context {Tp} `{IsTpDesc Tp} {E : EvType}.

(* A "function index" is a monadic function referred to by index. It is
essentially just a nat, but we make it a distinct type to make things clearer *)
Inductive FunIx (T:Tp) : Type@{entree_u} :=
| MkFunIx (n:nat).

Definition funIxIx {T} (f:FunIx T) : nat :=
  match f with
  | MkFunIx _ n => n
  end.

(*
Fixpoint tpElem (T : TpDesc) : Type@{entree_u} :=
  match T with
  | Tp_M R => FunIx (Tp_M R)
  | Tp_Pi A B => FunIx (Tp_Pi A B)
  | Tp_Arr A B => FunIx (Tp_Arr A B)
  | Tp_SType A => stpElem A
  | Tp_Pair A B => tpElem A * tpElem B
  | Tp_Sum A B => tpElem A + tpElem B
  | Tp_Sigma A B => { a:stpElem A & tpElem (B a) }
  end.

Fixpoint FunInput (T:TpDesc) : Type@{entree_u} :=
  match T with
  | Tp_M _ => unit
  | Tp_Pi A B => { a : stpElem A & FunInput (B a) }
  | Tp_Arr A B => tpElem A * FunInput B
  | _ => Empty_set
  end.

Fixpoint FunOutputDesc T : FunInput T -> TpDesc :=
  match T return FunInput T -> TpDesc with
  | Tp_M R => fun _ => R
  | Tp_Pi A B => fun args => FunOutputDesc (B (projT1 args)) (projT2 args)
  | Tp_Arr A B => fun args => FunOutputDesc B (snd args)
  | _ => fun _ => Tp_SType SimpTp_Void
  end.

Definition FunOutput T (args: FunInput T) : Type@{entree_u} :=
  tpElem (FunOutputDesc T args).
*)


(** Fun calls **)

Inductive FunCall : Type@{entree_u} :=
| MkFunCall (T:Tp) (f : FunIx T) (args : FunInput T).

Definition FunCallRet (call: FunCall) :=
  match call with
  | MkFunCall _ _ args => FunOutput args
  end.

Global Instance EncodingType_FunCall : EncodingType FunCall := FunCallRet.

(*
Inductive StackCall E : FunStack -> Type@{entree_u} :=
| MkStackCall T n stk (isn: isNth T n stk) (args : FunInput E stk T) stk'
  : StackCall E (app stk' stk).

Definition StackCallRet E stk (call: StackCall E stk) :=
  match call with
  | MkStackCall _ T n stk _ args _ => FunOutput E stk T args
  end.

Global Instance EncodingType_StackCall E stk : EncodingType (StackCall E stk) :=
 StackCallRet E stk.

Definition liftStackCall E stk U (call:StackCall E stk) : StackCall E (cons U stk) :=
  match call in StackCall _ stk return StackCall E (cons U stk) with
  | MkStackCall _ T n stk pf args stk' =>
      MkStackCall _ T n stk pf args (cons U stk')
  end.

Definition unliftStackCallRet E stk U call :
  StackCallRet E (cons U stk) (liftStackCall E stk U call) -> StackCallRet E stk call :=
  match call in StackCall _ stk
        return StackCallRet E (cons U stk) (liftStackCall E stk U call) ->
               StackCallRet E stk call with
  | MkStackCall _ T n stk isn args stk' =>
      fun x => x
  end.
*)


(**
 ** The definition of fixtrees
 **)

(* The functor defining a single constructor of a fixtree *)
Variant fixtreeF (F : Type@{entree_u} -> Type@{entree_u}) (R:Type@{entree_u}) : Type@{entree_u} :=
  | Fx_RetF (r : R)
  | Fx_TauF (t : F R)
  | Fx_VisF (e : E) (k : encodes e -> F R)
  | Fx_CallF (call : FunCall) (k : FunCallRet call -> F R)
  | Fx_MkFunF (T : Tp)
      (body : forall (args:FunInput T), F (FunOutput args))
      (k : FunIx T -> F R)
.

(* "Tying the knot" by defining entrees as the greatest fixed-point of fixtreeF *)
CoInductive fixtree R : Type@{entree_u} :=
  go { _fxobserve : fixtreeF fixtree R }.

(* Implicit arguments and helpful notations for fixtrees *)
Arguments Fx_RetF {_ _} _.
Arguments Fx_TauF {_ _} _.
Arguments Fx_VisF {_ _} _ _.
Arguments Fx_CallF {_ _} _ _.
Arguments Fx_MkFunF {_ _ _} _ _.
Notation fixtree' R := (fixtreeF (fixtree) R).
Notation Fx_Tau t := {| _fxobserve := Fx_TauF t |}.
Notation Fx_Ret r := {| _fxobserve := Fx_RetF r |}.
Notation Fx_Vis e k := {| _fxobserve := Fx_VisF e k |}.
Notation Fx_Call call k := {| _fxobserve := Fx_CallF call k |}.
Notation Fx_MkFun body k := {| _fxobserve := Fx_MkFunF body k |}.

(* "Observe" the top-most constructor of an fixtree by unwrapping it one step *)
Definition fxobserve {R} (t : fixtree R) : fixtree' R :=
  _fxobserve _ t.


(*** The basic operations on fixtrees ***)

(* This defines the bind operation by coinduction on the left-hand side of the
   bind; can also be seen as "substituting" an observed computation tree ot for
   the return value of a continuation k *)
Definition subst' {R S : Type@{entree_u}}
           (k : R -> fixtree S) : fixtree' R -> fixtree S  :=
  cofix _subst (ot : fixtree' R) :=
    match ot with
    | Fx_RetF r => k r
    | Fx_TauF t => Fx_Tau (_subst (fxobserve t))
    | Fx_VisF e k => Fx_Vis e (fun x => _subst (fxobserve (k x)))
    | Fx_CallF call k => Fx_Call call (fun x => _subst (fxobserve (k x)))
    | Fx_MkFunF body k => Fx_MkFun body (fun x => _subst (fxobserve (k x)))
    end.

(* Wrap up subst' so it operates on an fixtree instead of an fixtree' *)
Definition subst {R S : Type@{entree_u}}
           (k : R -> fixtree S) : fixtree R -> fixtree S :=
  fun t => subst' k (fxobserve t).

(* Monadic bind for fixtrees is just subst *)
Definition bind {R S : Type@{entree_u}} 
           (t : fixtree R) (k : R -> fixtree S) :=
  subst k t.

(* Iterate a body on successive inputs of type I until it returns an R *)
Definition iter {I R : Type@{entree_u}}
           (body : I -> fixtree (I + R)) : I -> fixtree R :=
  cofix _iter i :=
    bind (body i) (fun ir => match ir with
                          | inl i' => Fx_Tau (_iter i')
                          | inr r => Fx_Ret r
                          end).

(* Map a pure function over the return value(s) of an entree *)
Definition map {R S} (f : R -> S) (t : fixtree R) :=
  bind t (fun r => Fx_Ret (f r)).

(* Build a computation tree that performs a single event / effect in E *)
Definition trigger (e : E) : fixtree (encodes e) :=
  Fx_Vis e (fun x => Fx_Ret x).

(* The nonterminating computation that spins forever and never does anything *)
CoFixpoint spin {R} : fixtree R := Fx_Tau spin.

CoFixpoint embedEntree' {R} (ot: entree' E R) : fixtree R :=
  match ot with
  | RetF r => Fx_Ret r
  | TauF t' => Fx_Tau (embedEntree' (observe t'))
  | VisF e k => Fx_Vis e (fun x => embedEntree' (observe (k x)))
  end.

Definition embedEntree {R} (t: entree E R) : fixtree R :=
  embedEntree' (observe t).

Definition FxInterp T := forall (args:FunInput T), fixtree (FunOutput args).

Definition SomeFxInterp := { T & FxInterp T }.

Definition caseSomeFxInterp T (d : SomeFxInterp) : option (FxInterp T) :=
  match dec_eq_Tp (projT1 d) T with
  | left e => Some (eq_rect (projT1 d) FxInterp (projT2 d) T e)
  | right _ => None
  end.

Definition FxInterps : Type@{entree_u} := list SomeFxInterp.

Definition nthSomeFxInterp (defs : FxInterps) n : option SomeFxInterp :=
  nth_error defs n.

Definition getFxInterp (defs : FxInterps) {T} (f : FunIx T) : option (FxInterp T) :=
  match nthSomeFxInterp defs (funIxIx f) with
  | Some d => caseSomeFxInterp T d
  | None => None
  end.

Definition callFxInterp (defs : FxInterps) (call : FunCall)
  : option (fixtree (FunCallRet call)) :=
  match call with
  | MkFunCall _ f args =>
      match getFxInterp defs f with
      | Some d => Some (d args)
      | None => None
      end
  end.

Definition consFxInterp (defs : FxInterps) {T} (d : FxInterp T) : FxInterps :=
  app defs (existT FxInterp T d :: nil).

CoFixpoint interp_fixtree' {R} (err:entree E R) (defs : FxInterps)
  (ot : fixtree' R) : entree E R :=
  match ot with
  | Fx_RetF r => Ret r
  | Fx_TauF t => Tau (interp_fixtree' err defs (fxobserve t))
  | Fx_VisF e k => Vis e (fun x => interp_fixtree' err defs (fxobserve (k x)))
  | Fx_CallF call k =>
      match callFxInterp defs call with
      | Some m =>
          Tau (interp_fixtree' err defs (fxobserve (FixTree.bind m k)))
      | None => err
      end
  | Fx_MkFunF body k =>
      Tau (interp_fixtree' err (consFxInterp defs body)
             (fxobserve (k (MkFunIx _ (length defs)))))
  end.

Definition interp_fixtree {R} (err:entree E R) (defs : FxInterps) (t : fixtree R)
  : entree E R :=
  interp_fixtree' err defs (fxobserve t).

End FixTree.

Arguments fixtree _ {_} _ _.
Arguments fixtreeF _ {_} _ _.
Arguments Fx_RetF {_ _ _ _ _} _.
Arguments Fx_TauF {_ _ _ _ _} _.
Arguments Fx_VisF {_ _ _ _ _} _ _.
Arguments Fx_CallF {_ _ _ _ _} _ _.
Arguments Fx_MkFunF {_ _ _ _ _ _} _ _.
Notation fixtree' Tp E R := (fixtreeF Tp E (fixtree Tp E) R).
Notation Fx_Tau t := {| _fxobserve := Fx_TauF t |}.
Notation Fx_Ret r := {| _fxobserve := Fx_RetF r |}.
Notation Fx_Vis e k := {| _fxobserve := Fx_VisF e k |}.
Notation Fx_Call call k := {| _fxobserve := Fx_CallF call k |}.
Notation Fx_MkFun body k := {| _fxobserve := Fx_MkFunF body k |}.


(*** Notations for monadic computations ***)
Module FixTreeNotations.

Notation "t1 >>= k2" := (FixTree.bind t1 k2)
                        (at level 58, left associativity) : entree_scope.
Notation "x <- t1 ;; t2" := (FixTree.bind t1 (fun x => t2))
                        (at level 61, t1 at next level, right associativity) : entree_scope.
Notation "t1 ;; t2" := (FixTree.bind t1 (fun _ => t2))
                       (at level 61, right associativity) : entree_scope.
Notation "' p <- t1 ;; t2" :=
  (FixTree.bind t1 (fun x_ => match x_ with p => t2 end))
  (at level 61, t1 at next level, p pattern, right associativity) : entree_scope.


End FixTreeNotations.


(*** Instances to show that entrees form a monad ***)

#[global] Instance Functor_fixtree Tp `{IsTpDesc Tp} E : Functor (fixtree Tp E) :=
  { fmap := @FixTree.map Tp _ E }.

#[global] Instance Applicative_fixtree Tp `{IsTpDesc Tp} E : Applicative (fixtree Tp E) :=
  {
    pure := fun _  x => Fx_Ret x;
    ap := fun _ _ f x =>
            FixTree.bind f (fun f => FixTree.bind x (fun x => Fx_Ret (f x)) );

  }.

#[global] Instance Monad_fixtree Tp `{IsTpDesc Tp} E : Monad (fixtree Tp E) :=
  {
    ret := fun _ x => Fx_Ret x;
    bind := @FixTree.bind Tp _ E;
  }.

#[global] Instance MonadIter_fixtree Tp `{IsTpDesc Tp} E : MonadIter (fixtree Tp E) :=
  fun _ _ => FixTree.iter.
