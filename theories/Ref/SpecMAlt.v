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
Inductive FunTpDesc : Type@{entree_u} :=
| FunTp_M (R : TpDesc) : FunTpDesc
| FunTp_FunDep (A : SimpleDesc) (B : interpSType A -> FunTpDesc) : FunTpDesc
| FunTp_Fun (A : TpDesc) (B : FunTpDesc) : FunTpDesc
with TpDesc : Type@{entree_u} :=
| Tp_Fun (FT:FunTpDesc) : TpDesc
| Tp_SType (A : SimpleDesc) : TpDesc
| Tp_Pair (A : TpDesc) (B : TpDesc) : TpDesc
| Tp_Sum (A : TpDesc) (B : TpDesc) : TpDesc
| Tp_Sigma (A : SimpleDesc) (B : interpSType A -> TpDesc) : TpDesc
.

Definition FunStack := list FunTpDesc.

(* A trivially inhabited "default" function type *)
Definition default_fun_tp : FunTpDesc :=
  FunTp_FunDep SimpTp_Void (fun _ => FunTp_M (Tp_SType SimpTp_Void)).

(* Get the nth element of a list of function types, or default_fun_tp if n is too big *)
Definition nthFunTp (stk : FunStack) n : FunTpDesc :=
  nth_default' default_fun_tp stk n.

Inductive Clos stk : FunTpDesc -> Type@{entree_u} :=
| MkClos (n:nat) : Clos stk (nthFunTp stk n).

Fixpoint interpType stk (T : TpDesc) : Type@{entree_u} :=
  match T with
  | Tp_Fun FT => Clos stk FT
  | Tp_SType A => interpSType A
  | Tp_Pair A B => interpType stk A * interpType stk B
  | Tp_Sum A B => interpType stk A + interpType stk B
  | Tp_Sigma A B => { a:interpSType A & interpType stk (B a) }
  end.

Fixpoint FTInput stk (FT : FunTpDesc) : Type@{entree_u} :=
  match FT with
  | FunTp_M M => unit
  | FunTp_FunDep A B => { a : interpSType A & FTInput stk (B a) }
  | FunTp_Fun A B => interpType stk A * FTInput stk B
  end.

Fixpoint FTOutput stk FT : FTInput stk FT -> Type@{entree_u} :=
  match FT return FTInput stk FT -> Type@{entree_u} with
  | FunTp_M R => fun _ => interpType stk R
  | FunTp_FunDep A B => fun args => FTOutput stk (B (projT1 args)) (projT2 args)
  | FunTp_Fun A B => fun args => FTOutput stk B (snd args)
  end.


Inductive StackCall stk : Type@{entree_u} :=
| MkStackCall (FT : FunTpDesc) (clos : Clos stk FT) (args : FTInput stk FT).

Definition StackCallRet stk (call: StackCall stk) :=
  match call with
  | MkStackCall _ FT _ args => FTOutput stk FT args
  end.

Global Instance EncodingType_StackCall stk : EncodingType (StackCall stk) :=
 StackCallRet stk.


(*** The definition of lrtrees ***)
Section lrtree.

Context (E : EvType).

(* The functor defining a single constructor of an lrtree *)
Variant lrtreeF (F : FunStack -> Type@{entree_u} -> Type@{entree_u})
  (stk:FunStack) (R:Type@{entree_u}) : Type@{entree_u} :=
  | LR_RetF (r : R)
  | LR_TauF (t : F stk R)
  | LR_VisF (e : E) (k : encodes e -> F stk R)
  | LR_Call (call : StackCall stk) (k : StackCallRet stk call -> F stk R)
  | LR_LetRec (FT : FunTpDesc) (R' : TpDesc)
      (f : forall (args:FTInput (cons FT stk) FT),
          F (cons FT stk) (FTOutput _ FT args))
      (body : Clos (cons FT stk) FT -> F (cons FT stk) (interpType (cons FT stk) R'))
      (k : interpType stk R' -> F stk R)
.

(* "Tying the knot" by defining entrees as the greatest fixed-point of lrtreeF *)
CoInductive lrtree stk R : Type@{entree_u} :=
  go { _lrobserve : lrtreeF lrtree stk R }.

End lrtree.

(* Implicit arguments and helpful notations for entrees *)
Arguments LR_RetF {_ _ _ _} _.
Arguments LR_TauF {_ _ _ _} _.
Arguments LR_VisF {_ _ _ _} _ _.
Arguments LR_Call {_ _ _ _} _ _.
Arguments LR_LetRec {_ _ _ _} _ _ _.
Notation lrtree' E stk R := (lrtreeF E (lrtree E) stk R).
Notation LR_Tau t := {| _observe := LR_TauF t |}.
Notation LR_Ret r := {| _observe := LR_RetF r |}.
Notation LR_Vis e k := {| _observe := VisF e k |}.

(* "Observe" the top-most constructor of an entree by unwrapping it one step *)
Definition lrobserve {E stk R} (t : lrtree E stk R) : lrtree' E stk R :=
  _lrobserve _ _ _ t.



(*** The basic operations on entrees ***)

Module LRTree.

FIXME HERE NOW

(* This defines the bind operation by coinduction on the left-hand side of the
   bind; can also be seen as "substituting" an observed computation tree ot for
   the return value of a continuation k *)
Definition subst' {E : EvType} {stk} {R S : Type@{entree_u}}
           (k : R -> entree E S) : lrtree' E R -> lrtree E S  :=
  cofix _subst (ot : entree' E R) :=
    match ot with
    | RetF r => k r
    | TauF t => Tau (_subst (observe t))
    | VisF e k => Vis e (fun x => _subst (observe (k x)))
    end.

(* Wrap up subst' so it operates on an entree instead of an entree' *)
Definition subst {E : Type@{entree_u}} `{EncodingType E} {R S : Type@{entree_u}}
           (k : R -> entree E S) : entree E R -> entree E S :=
  fun t => subst' k (observe t).

(* Monadic bind for entrees is just subst *)
Definition bind {E} `{EncodingType E} {R S : Type@{entree_u}} 
           (t : entree E R) (k : R -> entree E S) :=
  subst k t.

(* Iterate a body on successive inputs of type I until it returns an R *)
Definition iter {E} `{EncodingType E} {I R : Type@{entree_u}}
           (body : I -> entree E (I + R) ) : I -> entree E R :=
  cofix _iter i :=
    bind (body i) (fun ir => match ir with
                          | inl i' => Tau (_iter i')
                          | inr r => Ret r
                          end).

(* Map a pure function over the return value(s) of an entree *)
Definition map {E} `{EncodingType E} {R S} (f : R -> S) (t : entree E R) :=
  bind t (fun r => Ret (f r)).

(* Build a computation tree that performs a single event / effect in E *)
Definition trigger {E} `{EncodingType E} (e : E) : entree E (encodes e) :=
  Vis e (fun x => Ret x).

(* The nonterminating computation that spins forever and never does anything *)
CoFixpoint spin {E R} `{EncodingType E} : entree E R := Tau spin.

End EnTree.


(*** Notations for monadic computations ***)
Module EnTreeNotations.

Notation "t1 >>= k2" := (EnTree.bind t1 k2)
                        (at level 58, left associativity) : entree_scope.
Notation "x <- t1 ;; t2" := (EnTree.bind t1 (fun x => t2) )
                        (at level 61, t1 at next level, right associativity) : entree_scope.
Notation "t1 ;; t2" := (EnTree.bind t1 (fun _ => t2))
                       (at level 61, right associativity) : entree_scope.
Notation "' p <- t1 ;; t2" :=
  (EnTree.bind t1 (fun x_ => match x_ with p => t2 end) )
  (at level 61, t1 at next level, p pattern, right associativity) : entree_scope.


End EnTreeNotations.


(*** Instances to show that entrees form a monad ***)

#[global] Instance Functor_entree {E} `{EncodingType E} : Functor (entree E) :=
  { fmap := @EnTree.map E _ }.

#[global] Instance Applicative_entree {E} `{EncodingType E} : Applicative (entree E) :=
  {
    pure := fun _  x => Ret x;
    ap := fun _ _ f x =>
            EnTree.bind f (fun f => EnTree.bind x (fun x => Ret (f x)) );

  }.

#[global] Instance Monad_entree {E} `{EncodingType E} : Monad (entree E) :=
  {
    ret := fun _ x => Ret x;
    bind := @EnTree.bind E _;
  }.

#[global] Instance MonadIter_entree {E} `{EncodingType E} : MonadIter (entree E) :=
  fun _ _ => EnTree.iter.












(* The SpecM event type *)
Inductive SpecMEvent (E:EvType) : Type@{entree_u} :=
| SpecMEv_E (e:E)
| SpecMEv_Err (err:ErrorE)
| SpecMEv_Call (call:StackCall)
| SpecMEv_LetFun (FT:FunTpDesc)
| SpecMEv_LetRec (FTs:list FunTpDesc)
.

Definition SpecMEventRet E (ev:SpecMEvent E) : Type@{entree_u} :=
  match ev with
  | SpecMEv_E e => evRetType e
  | SpecMEv_Err _ => Empty_set
  | SpecMEv_Call call => StackCallRet call
  | SpecMEv_LetFun FT => FTInput FT + Clos FT
  | SpecMEv_LetRec FTs => { n & 
  end.


(* Create an event type for either an event in E or a recursive call in a stack
   stk of recursive functions in scope *)
Definition FunStackE (E : EvType@{entree_u}) (stack : FunStack) : Type@{entree_u} :=
  StackCall E stack + (ErrorE + E).

(* The return type for a FunStackE effect in a SpecM computation *)
Definition FunStackERet E stack (e:FunStackE E stack) : Type@{entree_u} :=
  encodes e.

Global Instance EncodingType_FunStackE E stack : EncodingType (FunStackE E stack) :=
  FunStackERet E stack.

Global Instance ReSum_FunStackE_E (E : EvType) stk : ReSum E (FunStackE E stk) :=
  fun e => inr (inr e).

Global Instance ReSumRet_FunStackE_E (E : EvType) stk :
  ReSumRet E (FunStackE E stk) :=
  fun _ r => r.

Global Instance ReSum_FunStackE_Error (E : EvType) stk : ReSum ErrorE (FunStackE E stk) :=
  fun e => inr (inl e).

Global Instance ReSumRet_FunStackE_Error (E : EvType) stk :
  ReSumRet ErrorE (FunStackE E stk) :=
  fun _ r => r.

(* An interpretation of a FunType with corecursive call events *)
Definition FunTypeInterp (E:EvType) stk ftp : Type@{entree_u} :=
  forall (args:FTInput E ftp), entree_spec (FunStackE E stk) (FTOutput E ftp args).

(* An interpretation for all the functions in a FunStack *)
Definition FunStackInterp (E:EvType) stk : Type@{entree_u} :=
  mapTuple (FunTypeInterp E stk) stk.

(* The SpecM monad is an entree spec over FunStackE events *)
Definition SpecM (E:EvType) stack A : Type :=
  entree_spec (FunStackE E stack) A.

