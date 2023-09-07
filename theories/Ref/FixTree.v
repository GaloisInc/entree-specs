
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

(* A proof that x is the nth element of a list *)
Inductive isNth {A} (a:A) : nat -> list A -> Prop :=
| isNth_base l : isNth a 0 (cons a l)
| isNth_cons n x l : isNth a n l -> isNth a (S n) (cons x l).

Lemma not_isNth_nil {A} (a:A) n : isNth a n nil -> False.
Proof.
  induction n; intros; inversion H.
Qed.

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

(* Project the nth element of a mapTuple, using a default if n is too big *)
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

(* Project the nth element of a mapTuple using an isNth proof for the index *)
Polymorphic Fixpoint nthProj@{u v} {T:Type@{v}} (f : T -> Type@{u}) t n :
  forall l, isNth t n l -> f t.
Admitted.

(*
Polymorphic Fixpoint nthProj@{u v} {T:Type@{v}} (f : T -> Type@{u}) t n :
  forall l, isNth t n l -> f t :=
  match n return forall l, isNth t n l -> f t with
  | 0 => 
  end.
*)

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
| SimpTp_Prop (P:Prop) : SimpleDesc
| SimpTp_Nat : SimpleDesc
| SimpTp_Sum (A B : SimpleDesc) : SimpleDesc
.

(* Decode a simple type description to a type *)
Fixpoint stpElem (d : SimpleDesc) : Type@{entree_u} :=
  match d with
  | SimpTp_Void => Empty_set
  | SimpTp_Unit => unit
  | SimpTp_Prop P => P
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

Definition FunStack := list TpDesc.

(* A trivially inhabited "default" function type *)
Definition default_tp : TpDesc :=
  Tp_Pi SimpTp_Void (fun _ => Tp_M (Tp_SType SimpTp_Void)).

(* Get the nth element of a list of function types, or default_fun_tp if n is too big *)
Definition nthTp (stk : FunStack) n : TpDesc :=
  nth_default' default_tp stk n.

Inductive StkFun stk : TpDesc -> Type@{entree_u} :=
| MkStkFun (n:nat) (pf:n < length stk) : StkFun stk (nthTp stk n).

(*
Inductive StkFun stk (T:TpDesc) : Type@{entree_u} :=
| MkStkFun (n:nat) (pf: isNth T n stk) : StkFun stk T.
*)

Lemma noNilStkFun T (clos : StkFun nil T) : False.
  destruct clos. inversion pf.
Qed.

Definition liftStkFun stk U T (clos : StkFun stk T) : StkFun (cons U stk) T :=
  match clos with
  | MkStkFun _ n pf => MkStkFun (cons U stk) (S n) (lt_n_S _ _ pf)
  end.

Fixpoint tpElem (E:EvType) stk (T : TpDesc) : Type@{entree_u} :=
  match T with
  | Tp_M R => StkFun stk (Tp_M R) + entree E (tpElem E stk R)
  | Tp_Pi A B => StkFun stk (Tp_Pi A B) + forall a, tpElem E stk (B a)
  | Tp_Arr A B =>
      StkFun stk (Tp_Arr A B) + (tpElem E stk A -> tpElem E stk B)
  | Tp_SType A => stpElem A
  | Tp_Pair A B => tpElem E stk A * tpElem E stk B
  | Tp_Sum A B => tpElem E stk A + tpElem E stk B
  | Tp_Sigma A B => { a:stpElem A & tpElem E stk (B a) }
  end.


(* An interpretation of a monadic function type *)
(* NOTE: this treats a non-monadic return type as M Empty_set *)
Fixpoint FunInterp (E:EvType) stk (T : TpDesc) : Type@{entree_u} :=
  match T with
  | Tp_M R => entree E (tpElem E stk R)
  | Tp_Pi A B => forall a, FunInterp E stk (B a)
  | Tp_Arr A B => (tpElem E stk A -> FunInterp E stk B)
  | _ => entree E Empty_set
  end.

Definition defaultFunInterp E stk : FunInterp E stk default_tp :=
  fun v => match v with end.

Definition FunInterpToElem E stk T : FunInterp E stk T -> tpElem E stk T.
Admitted.

(*
Fixpoint FunInterpToElem E stk T : FunInterp E stk T -> tpElem E stk T :=
  match T return FunInterp E stk T -> tpElem E stk T with
  end.
*)

Fixpoint FunInput E stk (T:TpDesc) : Type@{entree_u} :=
  match T with
  | Tp_M _ => unit
  | Tp_Pi A B => { a : stpElem A & FunInput E stk (B a) }
  | Tp_Arr A B => tpElem E stk A * FunInput E stk B
  | _ => unit
  end.

Fixpoint FunOutput E stk T : FunInput E stk T -> Type@{entree_u} :=
  match T return FunInput E stk T -> Type@{entree_u} with
  | Tp_M R => fun _ => tpElem E stk R
  | Tp_Pi A B => fun args => FunOutput E stk (B (projT1 args)) (projT2 args)
  | Tp_Arr A B => fun args => FunOutput E stk B (snd args)
  | _ => fun _ => Empty_set
  end.

Fixpoint applyFunInterp {E stk T} :
  FunInterp E stk T -> forall args:FunInput E stk T, entree E (FunOutput E stk T args) :=
  match T return FunInterp E stk T ->
                 forall args:FunInput E stk T, entree E (FunOutput E stk T args)
  with
  | Tp_M R => fun m _ => m
  | Tp_Pi A B =>
      fun f args =>
        @applyFunInterp E stk (B (projT1 args)) (f (projT1 args)) (projT2 args)
  | Tp_Arr A B =>
      fun f args =>
        @applyFunInterp E stk B (f (fst args)) (snd args)
  | Tp_SType A => fun m _ => m
  | Tp_Pair A B => fun m _ => m
  | Tp_Sum A B => fun m _ => m
  | Tp_Sigma A B => fun m _ => m
  end.

Fixpoint lambdaFunInterp E stk T :
  (forall args:FunInput E stk T,
      entree E (FunOutput E stk T args)) -> FunInterp E stk T :=
  match T return (forall args:FunInput E stk T,
                     entree E (FunOutput E stk T args)) -> FunInterp E stk T
  with
  | Tp_M R => fun f => f tt
  | Tp_Pi A B =>
      fun f a => lambdaFunInterp E stk (B a) (fun args => f (existT _ a args))
  | Tp_Arr A B =>
      fun f arg => lambdaFunInterp E stk B (fun args => f (arg, args))
  | Tp_SType A => fun f => f tt
  | Tp_Pair A B => fun f => f tt
  | Tp_Sum A B => fun f => f tt
  | Tp_Sigma A B => fun f => f tt
  end.


(**
 ** Substitution and Lifting for tpElem
 **)

Definition substStkFun E stk U (I : FunInterp E (cons U stk) U)
  T (clos : StkFun (cons U stk) T) : StkFun stk T + FunInterp E (cons U stk) T :=
  match clos with
  | MkStkFun _ 0 _ => inr I
  | MkStkFun _ (S n) pf => inl (MkStkFun _ n (lt_S_n _ _ pf))
  end.


Fixpoint substLiftTpElem E stk U (I : FunInterp E (cons U stk) U) T :
  (tpElem E (cons U stk) T -> tpElem E stk T)
  * (tpElem E stk T -> tpElem E (cons U stk) T) :=
  match T in TpDesc
        return (tpElem E (cons U stk) T -> tpElem E stk T)
               * (tpElem E stk T -> tpElem E (cons U stk) T)
  with
  | Tp_M R =>
      ((fun elem =>
          match elem with
          | inl clos =>
              match substStkFun E stk U I _ clos with
              | inl clos' => inl clos'
              | inr m =>
                  inr (fmap (fst (substLiftTpElem E stk U I R)) m)
              end
          | inr m =>
              inr (fmap (fst (substLiftTpElem E stk U I R)) m)
          end)
        ,
        (fun elem =>
           match elem with
           | inl clos => inl (liftStkFun stk U (Tp_M R) clos)
           | inr m => inr (fmap (snd (substLiftTpElem E stk U I R)) m)
           end))
  | Tp_Pi A B =>
      ((fun elem =>
          match elem with
          | inl clos =>
              match substStkFun E stk U I (Tp_Pi A B) clos with
              | inl clos' => inl clos'
              | inr f =>
                  inr (fun a => fst (substLiftTpElem E stk U I (B a))
                                  (FunInterpToElem E _ _ (f a)))
              end
          | inr f =>
              inr (fun a => fst (substLiftTpElem E stk U I (B a)) (f a))
          end)
        ,
        (fun elem =>
           match elem with
           | inl clos => inl (liftStkFun stk U (Tp_Pi A B) clos)
           | inr f => inr (fun a => snd (substLiftTpElem E stk U I (B a)) (f a))
           end))
  | Tp_Arr A B =>
      ((fun elem =>
          match elem with
          | inl clos =>
              match substStkFun E stk U I (Tp_Arr A B) clos with
              | inl clos' => inl clos'
              | inr f =>
                  inr (fun arg =>
                         fst (substLiftTpElem E stk U I B)
                             (FunInterpToElem E _ _
                                (f
                                   (snd (substLiftTpElem E stk U I A) arg))))
              end
          | inr f =>
              inr (fun arg =>
                         fst (substLiftTpElem E stk U I B)
                           (f
                              (snd (substLiftTpElem E stk U I A) arg)))
          end)
        ,
        (fun elem =>
          match elem with
          | inl clos => inl (liftStkFun stk U (Tp_Arr A B) clos)
          | inr f =>
              inr (fun arg =>
                         snd (substLiftTpElem E stk U I B)
                           (f
                              (fst (substLiftTpElem E stk U I A) arg)))
          end))
  | Tp_SType A =>
      (id, id)
  | Tp_Pair A B =>
      ((fun elem =>
          (fst (substLiftTpElem E stk U I A) (fst elem),
            fst (substLiftTpElem E stk U I B) (snd elem)))
        ,
        (fun elem =>
           (snd (substLiftTpElem E stk U I A) (fst elem),
             snd (substLiftTpElem E stk U I B) (snd elem))))
  | Tp_Sum A B =>
      ((fun elem =>
          match elem with
          | inl x => inl (fst (substLiftTpElem E stk U I A) x)
          | inr y => inr (fst (substLiftTpElem E stk U I B) y)
          end)
        ,
        (fun elem =>
          match elem with
          | inl x => inl (snd (substLiftTpElem E stk U I A) x)
          | inr y => inr (snd (substLiftTpElem E stk U I B) y)
          end))
  | Tp_Sigma A B =>
      ((fun elem =>
          existT _ (projT1 elem)
            (fst (substLiftTpElem E stk U I (B (projT1 elem))) (projT2 elem)))
        ,
        (fun elem =>
           existT _ (projT1 elem)
             (snd (substLiftTpElem E stk U I (B (projT1 elem))) (projT2 elem))))
  end.

Definition substTpElem E stk U (I : FunInterp E (cons U stk) U) T :
  tpElem E (cons U stk) T -> tpElem E stk T :=
  fst (substLiftTpElem E stk U I T).

Definition liftTpElem E stk U (I : FunInterp E (cons U stk) U) T :
  tpElem E stk T -> tpElem E (cons U stk) T :=
  snd (substLiftTpElem E stk U I T).

Fixpoint liftFunInput E stk U (I : FunInterp E (cons U stk) U) T :
  FunInput E stk T -> FunInput E (cons U stk) T.
Admitted.

Fixpoint substFunOutput E stk U (I : FunInterp E (cons U stk) U) T :
  forall args:FunInput E stk T, FunOutput E stk T args ->
                                FunOutput E (cons U stk) T (liftFunInput E stk U I T args).
Admitted.

Fixpoint liftFunInterp E stk U (I : FunInterp E (cons U stk) U) T :
  FunInterp E stk T -> FunInterp E (cons U stk) T :=
  match T return FunInterp E stk T -> FunInterp E (cons U stk) T with
  | Tp_M R => fun m => fmap (liftTpElem E stk U I R) m
  | Tp_Pi A B => fun f a => liftFunInterp E stk U I (B a) (f a)
  | Tp_Arr A B => fun f arg =>
                    liftFunInterp E stk U I B (f (substTpElem E stk U I A arg))
  | _ => fun m => m
  end.


Definition StackInterp E stk : Type@{entree_u} := mapTuple (FunInterp E stk) stk.

Definition consStackInterp E stk T (Is : StackInterp E stk)
  (I : FunInterp E (cons T stk) T) : StackInterp E (cons T stk) :=
  (I, mapMapTuple _ _ (liftFunInterp E stk T I) _ Is).

Definition nthFunInterp E stk n (Is : StackInterp E stk) : FunInterp E stk (nthTp stk n) :=
  nthProjDefault _ default_tp (defaultFunInterp E stk) stk n Is.


Inductive StackCall E stk : Type@{entree_u} :=
| MkStackCall n (pf : n < length stk) (args : FunInput E stk (nthTp stk n)).

Definition StackCallRet E stk (call: StackCall E stk) :=
  match call with
  | MkStackCall _ _ n _ args => FunOutput E stk (nthTp stk n) args
  end.

Global Instance EncodingType_StackCall E stk : EncodingType (StackCall E stk) :=
 StackCallRet E stk.


(**
 ** The definition of fixtrees
 **)
Section fixtree.

Context (E : EvType).

(* The functor defining a single constructor of a fixtree *)
Variant fixtreeF (F : FunStack -> Type@{entree_u} -> Type@{entree_u})
  (stk:FunStack) (R:Type@{entree_u}) : Type@{entree_u} :=
  | Fx_RetF (r : R)
  | Fx_TauF (t : F stk R)
  | Fx_VisF (e : E) (k : encodes e -> F stk R)
  | Fx_CallF (call : StackCall E stk) (k : StackCallRet E stk call -> F stk R)
  | Fx_FixF (T : TpDesc)
      (body : forall (args:FunInput E (cons T stk) T),
          F (cons T stk) (FunOutput E (cons T stk) T args))
      (args : FunInput E stk T)
      (k : FunOutput E stk T args -> F stk R)
.

(* "Tying the knot" by defining entrees as the greatest fixed-point of fixtreeF *)
CoInductive fixtree stk R : Type@{entree_u} :=
  go { _fxobserve : fixtreeF fixtree stk R }.

End fixtree.

(* Implicit arguments and helpful notations for fixtrees *)
Arguments Fx_RetF {_ _ _ _} _.
Arguments Fx_TauF {_ _ _ _} _.
Arguments Fx_VisF {_ _ _ _} _ _.
Arguments Fx_CallF {_ _ _ _} _ _.
Arguments Fx_FixF {_ _ _ _ _} _ _ _.
Notation fixtree' E stk R := (fixtreeF E (fixtree E) stk R).
Notation Fx_Tau t := {| _fxobserve := Fx_TauF t |}.
Notation Fx_Ret r := {| _fxobserve := Fx_RetF r |}.
Notation Fx_Vis e k := {| _fxobserve := Fx_VisF e k |}.
Notation Fx_Call call k := {| _fxobserve := Fx_CallF call k |}.
Notation Fx_Fix body args k := {| _fxobserve := Fx_FixF body args k |}.

(* "Observe" the top-most constructor of an fixtree by unwrapping it one step *)
Definition fxobserve {E stk R} (t : fixtree E stk R) : fixtree' E stk R :=
  _fxobserve _ _ _ t.


(*** The basic operations on fixtrees ***)

Module FixTree.

(* This defines the bind operation by coinduction on the left-hand side of the
   bind; can also be seen as "substituting" an observed computation tree ot for
   the return value of a continuation k *)
Definition subst' {E : EvType} {stk} {R S : Type@{entree_u}}
           (k : R -> fixtree E stk S) : fixtree' E stk R -> fixtree E stk S  :=
  cofix _subst (ot : fixtree' E stk R) :=
    match ot with
    | Fx_RetF r => k r
    | Fx_TauF t => Fx_Tau (_subst (fxobserve t))
    | Fx_VisF e k => Fx_Vis e (fun x => _subst (fxobserve (k x)))
    | Fx_CallF call k => Fx_Call call (fun x => _subst (fxobserve (k x)))
    | Fx_FixF body args k => Fx_Fix body args (fun x => _subst (fxobserve (k x)))
    end.

(* Wrap up subst' so it operates on an fixtree instead of an fixtree' *)
Definition subst {E : EvType} {stk} {R S : Type@{entree_u}}
           (k : R -> fixtree E stk S) : fixtree E stk R -> fixtree E stk S :=
  fun t => subst' k (fxobserve t).

(* Monadic bind for fixtrees is just subst *)
Definition bind {E stk} {R S : Type@{entree_u}} 
           (t : fixtree E stk R) (k : R -> fixtree E stk S) :=
  subst k t.

(* Iterate a body on successive inputs of type I until it returns an R *)
Definition iter {E stk} {I R : Type@{entree_u}}
           (body : I -> fixtree E stk (I + R)) : I -> fixtree E stk R :=
  cofix _iter i :=
    bind (body i) (fun ir => match ir with
                          | inl i' => Fx_Tau (_iter i')
                          | inr r => Fx_Ret r
                          end).

(* Map a pure function over the return value(s) of an entree *)
Definition map {E stk} {R S} (f : R -> S) (t : fixtree E stk R) :=
  bind t (fun r => Fx_Ret (f r)).

(* Build a computation tree that performs a single event / effect in E *)
Definition trigger {E:EvType} {stk} (e : E) : fixtree E stk (encodes e) :=
  Fx_Vis e (fun x => Fx_Ret x).

(* The nonterminating computation that spins forever and never does anything *)
CoFixpoint spin {E stk R} : fixtree E stk R := Fx_Tau spin.

(* NOTE: cannot lift the stack of a fixtree, because the continuation for a call
expects the output of that call to be in the original, not the lifted, stack *)
(*
CoFixpoint liftFixTree' {E stk R} T (ot : fixtree' E stk R) : fixtree E (cons T stk) R :=
  match ot with
  | Fx_RetF r => Fx_Ret r
  | Fx_TauF t => Fx_Tau (liftFixTree' T (fxobserve t))
  | Fx_VisF e k => Fx_Vis e (fun x => liftFixTree' T (fxobserve (k x)))
  | Fx_CallF call k =>
      Fx_Call (liftStackCall stk T call) (fun x => liftFixTree' T (fxobserve (k x))) end.
  | Fx_FixF body args k => Fx_Fix body args (fun x => _subst (fxobserve (k x)))
  end.
*)

FIXME: the StackInterp has to contain fixtree interps, not entree interps

CoFixpoint interp_fixtree' {E stk R} (defs : StackInterp E stk) (ot : fixtree' E stk R)
  : entree E R :=
  match ot with
  | Fx_RetF r => Ret r
  | Fx_TauF t => Tau (interp_fixtree' defs (fxobserve t))
  | Fx_VisF e k => Vis e (fun x => interp_fixtree' defs (fxobserve (k x)))
  | Fx_CallF (MkStackCall _ _ n _ args) k =>
      Tau (EnTree.bind
             (applyFunInterp (nthFunInterp E stk n defs) args)
             (fun x =>
                interp_fixtree' defs (fxobserve (k x))))
  | Fx_FixF body args k =>
      Tau (EnTree.bind
             (interp_fixtree' (consStackInterp E stk _ body defs)
                (body args))
             (fun x => interp_fixtree' defs (fxobserve (k x))))
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
    pure := fun _  x => Fx_Ret x;
    ap := fun _ _ f x =>
            FixTree.bind f (fun f => FixTree.bind x (fun x => Fx_Ret (f x)) );

  }.

#[global] Instance Monad_entree {E stk} : Monad (fixtree E stk) :=
  {
    ret := fun _ x => Fx_Ret x;
    bind := @FixTree.bind E _;
  }.

#[global] Instance MonadIter_entree {E stk} : MonadIter (fixtree E stk) :=
  fun _ _ => FixTree.iter.
