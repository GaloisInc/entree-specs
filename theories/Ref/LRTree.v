
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


(* A version of nth_default that does primary recursion on the list *)
Fixpoint nth_default' {A} (d : A) (l : list A) n : A :=
  match l with
  | nil => d
  | cons x l' => match n with
                 | 0 => x
                 | S n' => nth_default' d l' n'
                 end
  end.

(* Build the right-nested tuple type of a list of types formed by mapping a
function across a list *)
Polymorphic Fixpoint mapTuple@{u v} {T:Type@{v}} (f : T -> Type@{u}) (xs : list T) : Type@{u} :=
  match xs with
  | nil => unit
  | cons x xs' => f x * mapTuple f xs'
  end.

Polymorphic Fixpoint mapMapTuple@{u v} {T:Type@{v}} (f g : T -> Type@{u})
  (fg : forall t, f t -> g t) (xs : list T) : mapTuple f xs -> mapTuple g xs :=
  match xs return mapTuple f xs -> mapTuple g xs with
  | nil => fun u => u
  | cons x xs' => fun tup => (fg x (fst tup), mapMapTuple f g fg xs' (snd tup))
  end.

(* Append two mapTuple tuples *)
Polymorphic Fixpoint appMapTuple@{u v} {T:Type@{v}} (f : T -> Type@{u}) (xs ys : list T) :
  mapTuple f xs -> mapTuple f ys -> mapTuple f (app xs ys) :=
  match xs return mapTuple f xs -> mapTuple f ys -> mapTuple f (app xs ys) with
  | nil => fun _ tup2 => tup2
  | cons x xs' =>
      fun tup1 tup2 => (fst tup1, appMapTuple f xs' ys (snd tup1) tup2)
  end.

(* Project the nth element of a mapTuple *)
Polymorphic Fixpoint nthProjDefault@{u v} {T:Type@{v}} (f : T -> Type@{u}) (dT:T) (d:f dT) xs
  : forall n, mapTuple f xs -> f (nth_default' dT xs n) :=
  match xs return forall n, mapTuple f xs -> f (nth_default' dT xs n) with
  | nil => fun _ _ => d
  | cons x xs' =>
      fun n =>
        match n return mapTuple f (cons x xs') -> f (nth_default' dT (cons x xs') n) with
        | 0 => fun tup => fst tup
        | S n' => fun tup => nthProjDefault f dT d xs' n' (snd tup)
        end
  end.


(** Event types **)

(* An event type = a type of events plus their return types *)
Polymorphic Record EvType@{u} : Type :=
  { evTypeType :> Type@{u};
    evRetType : EncodingType evTypeType }.

Global Instance EncodingType_EvType (ET:EvType) : EncodingType ET :=
  evRetType ET.

(* The error event type *)
Inductive ErrorE : Set :=
| mkErrorE : string -> ErrorE.

Global Instance EncodingType_ErrorE : EncodingType ErrorE := fun _ => Empty_set.


(** Type Descriptions **)

(* FIXME: if this approach works, we will want to make the kind and type
descriptions extensible and/or instantiatable *)

(* Simple, non-dependent type descriptions *)
Inductive SimpleDesc : Type@{entree_u} :=
| SimpTp_Void : SimpleDesc
| SimpTp_Unit : SimpleDesc
| SimpTp_Nat : SimpleDesc
| SimpTp_Sum (A B : SimpleDesc) : SimpleDesc
.

(* Interpret a simple type description to a type *)
Fixpoint interpSType (d : SimpleDesc) : Type@{entree_u} :=
  match d with
  | SimpTp_Void => Empty_set
  | SimpTp_Unit => unit
  | SimpTp_Nat => nat
  | SimpTp_Sum A B => interpSType A + interpSType B
  end.

(* General type descriptions *)
Inductive TpDesc : Type@{entree_u} :=
| Tp_M (R : TpDesc) : TpDesc
| Tp_FunDep (A : SimpleDesc) (B : interpSType A -> TpDesc) : TpDesc
| Tp_Fun (A : TpDesc) (B : TpDesc) : TpDesc
| Tp_SType (A : SimpleDesc) : TpDesc
| Tp_Pair (A : TpDesc) (B : TpDesc) : TpDesc
| Tp_Sum (A : TpDesc) (B : TpDesc) : TpDesc
| Tp_Sigma (A : SimpleDesc) (B : interpSType A -> TpDesc) : TpDesc
.

Definition FunStack := list TpDesc.

(* A trivially inhabited "default" function type *)
Definition default_tp : TpDesc :=
  Tp_FunDep SimpTp_Void (fun _ => Tp_M (Tp_SType SimpTp_Void)).

(* Get the nth element of a list of function types, or default_fun_tp if n is too big *)
Definition nthTp (stk : FunStack) n : TpDesc :=
  nth_default' default_tp stk n.

Inductive Clos stk : TpDesc -> Type@{entree_u} :=
| MkClos (n:nat) : Clos stk (nthTp stk n).

Fixpoint interpType stk (T : TpDesc) : Type@{entree_u} :=
  match T with
  | Tp_M R => Clos stk (Tp_M R)
  | Tp_FunDep A B => Clos stk (Tp_FunDep A B)
  | Tp_Fun A B => Clos stk (Tp_Fun A B)
  | Tp_SType A => interpSType A
  | Tp_Pair A B => interpType stk A * interpType stk B
  | Tp_Sum A B => interpType stk A + interpType stk B
  | Tp_Sigma A B => { a:interpSType A & interpType stk (B a) }
  end.

Fixpoint FunInput stk T : Type@{entree_u} :=
  match T with
  | Tp_M _ => unit
  | Tp_FunDep A B => { a : interpSType A & FunInput stk (B a) }
  | Tp_Fun A B => interpType stk A * FunInput stk B
  | _ => Empty_set
  end.

Fixpoint FunOutput stk T : FunInput stk T -> Type@{entree_u} :=
  match T return FunInput stk T -> Type@{entree_u} with
  | Tp_M R => fun _ => interpType stk R
  | Tp_FunDep A B => fun args => FunOutput stk (B (projT1 args)) (projT2 args)
  | Tp_Fun A B => fun args => FunOutput stk B (snd args)
  | _ => fun v => match v with end
  end.

Inductive StackCall stk : Type@{entree_u} :=
| MkStackCall n (args : FunInput stk (nthTp stk n)).

Definition StackCallRet stk (call: StackCall stk) :=
  match call with
  | MkStackCall _ n args => FunOutput stk (nthTp stk n) args
  end.

Global Instance EncodingType_StackCall stk : EncodingType (StackCall stk) :=
 StackCallRet stk.


(*** The definition of fixtrees ***)
Section fixtree.

Context (E : EvType).

(* The functor defining a single constructor of a fixtree *)
Variant fixtreeF (F : FunStack -> Type@{entree_u} -> Type@{entree_u})
  (stk:FunStack) (R:Type@{entree_u}) : Type@{entree_u} :=
  | FxTr_RetF (r : R)
  | FxTr_TauF (t : F stk R)
  | FxTr_VisF (e : E) (k : encodes e -> F stk R)
  | FxTr_CallF (call : StackCall stk) (k : StackCallRet stk call -> F stk R)
  | FxTr_FixF (T : TpDesc)
      (body : forall stk' (args:FunInput (app stk' (cons T stk)) T),
          F (app stk' (cons T stk)) (FunOutput (app stk' (cons T stk)) T args))
      (args : FunInput (cons T stk) T)
      (k : FunOutput stk T args -> F stk R)
.

(* "Tying the knot" by defining entrees as the greatest fixed-point of fixtreeF *)
CoInductive fixtree stk R : Type@{entree_u} :=
  go { _fobserve : fixtreeF fixtree stk R }.

End fixtree.

(* Implicit arguments and helpful notations for fixtrees *)
Arguments FxTr_RetF {_ _ _ _} _.
Arguments FxTr_TauF {_ _ _ _} _.
Arguments FxTr_VisF {_ _ _ _} _ _.
Arguments FxTr_CallF {_ _ _ _} _ _.
Arguments FxTr_FixF {_ _ _ _ _} _ _ _.
Notation fixtree' E stk R := (fixtreeF E (fixtree E) stk R).
Notation FxTr_Tau t := {| _fobserve := FxTr_TauF t |}.
Notation FxTr_Ret r := {| _fobserve := FxTr_RetF r |}.
Notation FxTr_Vis e k := {| _fobserve := FxTr_VisF e k |}.
Notation FxTr_Call call k := {| _fobserve := FxTr_CallF call k |}.
Notation FxTr_Fix body args k := {| _fobserve := FxTr_FixF body args k |}.

(* "Observe" the top-most constructor of an fixtree by unwrapping it one step *)
Definition fobserve {E stk R} (t : fixtree E stk R) : fixtree' E stk R :=
  _fobserve _ _ _ t.


(*** The basic operations on fixtrees ***)

Module FixTree.

(* This defines the bind operation by coinduction on the left-hand side of the
   bind; can also be seen as "substituting" an observed computation tree ot for
   the return value of a continuation k *)
Definition subst' {E : EvType} {stk} {R S : Type@{entree_u}}
           (k : R -> fixtree E stk S) : fixtree' E stk R -> fixtree E stk S  :=
  cofix _subst (ot : fixtree' E stk R) :=
    match ot with
    | FxTr_RetF r => k r
    | FxTr_TauF t => FxTr_Tau (_subst (fobserve t))
    | FxTr_VisF e k => FxTr_Vis e (fun x => _subst (fobserve (k x)))
    | FxTr_CallF call k => FxTr_Call call (fun x => _subst (fobserve (k x)))
    | FxTr_FixF body args k => FxTr_Fix body args (fun x => _subst (fobserve (k x)))
    end.

(* Wrap up subst' so it operates on an fixtree instead of an fixtree' *)
Definition subst {E : EvType} {stk} {R S : Type@{entree_u}}
           (k : R -> fixtree E stk S) : fixtree E stk R -> fixtree E stk S :=
  fun t => subst' k (fobserve t).

(* Monadic bind for fixtrees is just subst *)
Definition bind {E stk} {R S : Type@{entree_u}} 
           (t : fixtree E stk R) (k : R -> fixtree E stk S) :=
  subst k t.

(* Iterate a body on successive inputs of type I until it returns an R *)
Definition iter {E stk} {I R : Type@{entree_u}}
           (body : I -> fixtree E stk (I + R)) : I -> fixtree E stk R :=
  cofix _iter i :=
    bind (body i) (fun ir => match ir with
                          | inl i' => FxTr_Tau (_iter i')
                          | inr r => FxTr_Ret r
                          end).

(* Map a pure function over the return value(s) of an entree *)
Definition map {E stk} {R S} (f : R -> S) (t : fixtree E stk R) :=
  bind t (fun r => FxTr_Ret (f r)).

(* Build a computation tree that performs a single event / effect in E *)
Definition trigger {E:EvType} {stk} (e : E) : fixtree E stk (encodes e) :=
  FxTr_Vis e (fun x => FxTr_Ret x).

(* The nonterminating computation that spins forever and never does anything *)
CoFixpoint spin {E stk R} : fixtree E stk R := FxTr_Tau spin.

(* NOTE: cannot lift the stack of a fixtree, because the continuation for a call
expects the output of that call to be in the original, not the lifted, stack *)
(*
CoFixpoint liftFixTree' {E stk R} T (ot : fixtree' E stk R) : fixtree E (cons T stk) R :=
  match ot with
  | FxTr_RetF r => FxTr_Ret r
  | FxTr_TauF t => FxTr_Tau (liftFixTree' T (fobserve t))
  | FxTr_VisF e k => FxTr_Vis e (fun x => liftFixTree' T (fobserve (k x)))
  | FxTr_CallF call k =>
      FxTr_Call (liftStackCall stk T call) (fun x => liftFixTree' T (fobserve (k x))) end.
  | FxTr_FixF body args k => FxTr_Fix body args (fun x => _subst (fobserve (k x)))
  end.
*)

Definition FunInterp E stk T : Type@{entree_u} :=
  forall stk' (args:FunInput (app stk' stk) T),
    fixtree E (app stk' stk) (FunOutput (app stk' stk) T args).

Definition default_interp E stk : FunInterp E stk default_tp :=
  fun _ v => match projT1 v with end.

Definition StackInterp E stk : Type@{entree_u} :=
  mapTuple (FunInterp E stk) stk.

Definition liftFunInterp E stk U T (interp : FunInterp E stk T) : FunInterp E (cons U stk) T.
Admitted.

Definition consStackInterp E stk T (f : FunInterp E (cons T stk) T)
  (interps : StackInterp E stk) : StackInterp E (cons T stk) :=
  (f, mapMapTuple _ _ (liftFunInterp E stk T) stk interps).

(* Get the nth function in a StackInterp *)
Definition nthStackInterp E stk n (defs : StackInterp E stk)
  : FunInterp E stk (nthTp stk n) :=
  nthProjDefault (FunInterp E stk) default_tp
    (default_interp E stk) stk n defs.


CoFixpoint interp_fixtree' {E stk R} (defs : StackInterp E stk) (ot : fixtree' E stk R)
  : entree E R :=
  match ot with
  | FxTr_RetF r => Ret r
  | FxTr_TauF t => Tau (interp_fixtree' defs (fobserve t))
  | FxTr_VisF e k => Vis e (fun x => interp_fixtree' defs (fobserve (k x)))
  | FxTr_CallF (MkStackCall _ n args) k =>
      Tau (interp_fixtree' defs
             (fobserve (FixTree.bind (nthStackInterp E stk n defs nil args) k)))
  | FxTr_FixF body args k =>
      Tau (EnTree.bind
             (interp_fixtree' (consStackInterp E stk _ body defs)
                (body args))
             (fun x => interp_fixtree' defs (fobserve (k x))))
  end.
  


Section mrec_spec.
Context {D E} `{EncodingType D} `{EncodingType E}.
Context (bodies : forall (d : D), entree_spec (D + E) (encodes d) ).
CoFixpoint interp_mrec_spec' {R} (ot : entree_spec' (D + E) R) : entree_spec E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mrec_spec' (observe t) )
  | VisF (Spec_vis (inl d)) k => Tau (interp_mrec_spec' (observe (EnTree.bind (bodies d) k )) )
  | VisF (Spec_vis (inr e)) k => Vis (Spec_vis e) (fun x => interp_mrec_spec' (observe (k x))) 
  | VisF (Spec_forall _) k => Vis (@Spec_forall E _) (fun x => interp_mrec_spec' (observe (k x)))
  | VisF (Spec_exists _) k => Vis (@Spec_exists E _) (fun x => interp_mrec_spec' (observe (k x)))
end.
Definition interp_mrec_spec {R} (t : entree_spec (D + E) R) : entree_spec E R :=
  interp_mrec_spec' (observe t).
Definition mrec_spec (d : D) := interp_mrec_spec (bodies d).


End FixTree.


(*** Notations for monadic computations ***)
Module FixTreeNotations.

Notation "t1 >>= k2" := (FixTree.bind t1 k2)
                        (at level 58, left associativity) : entree_scope.
Notation "x <- t1 ;; t2" := (FixTree.bind t1 (fun x => t2) )
                        (at level 61, t1 at next level, right associativity) : entree_scope.
Notation "t1 ;; t2" := (FixTree.bind t1 (fun _ => t2))
                       (at level 61, right associativity) : entree_scope.
Notation "' p <- t1 ;; t2" :=
  (FixTree.bind t1 (fun x_ => match x_ with p => t2 end) )
  (at level 61, t1 at next level, p pattern, right associativity) : entree_scope.


End FixTreeNotations.


(*** Instances to show that entrees form a monad ***)

#[global] Instance Functor_entree {E stk} : Functor (fixtree E stk) :=
  { fmap := @FixTree.map E _ }.

#[global] Instance Applicative_entree {E stk} : Applicative (fixtree E stk) :=
  {
    pure := fun _  x => FxTr_Ret x;
    ap := fun _ _ f x =>
            FixTree.bind f (fun f => FixTree.bind x (fun x => FxTr_Ret (f x)) );

  }.

#[global] Instance Monad_entree {E stk} : Monad (fixtree E stk) :=
  {
    ret := fun _ x => FxTr_Ret x;
    bind := @FixTree.bind E _;
  }.

#[global] Instance MonadIter_entree {E stk} : MonadIter (fixtree E stk) :=
  fun _ _ => FixTree.iter.
