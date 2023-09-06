
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
Fixpoint decodeSType (d : SimpleDesc) : Type@{entree_u} :=
  match d with
  | SimpTp_Void => Empty_set
  | SimpTp_Unit => unit
  | SimpTp_Prop P => P
  | SimpTp_Nat => nat
  | SimpTp_Sum A B => decodeSType A + decodeSType B
  end.

(* General type descriptions, parameterized by whether they are a monadic type *)
Inductive TpDesc : bool -> Type@{entree_u} :=
(* Monadic function types *)
| Tp_M (R : TpDesc false) : TpDesc true
| Tp_Pi (A : SimpleDesc) (B : decodeSType A -> TpDesc true) : TpDesc true
| Tp_Arr (A : TpDesc false) (B : TpDesc true) : TpDesc true

(* First-order types *)
| Tp_Fun (A : TpDesc true) : TpDesc false
| Tp_SType (A : SimpleDesc) : TpDesc false
| Tp_Pair (A : TpDesc false) (B : TpDesc false) : TpDesc false
| Tp_Sum (A : TpDesc false) (B : TpDesc false) : TpDesc false
| Tp_Sigma (A : SimpleDesc) (B : decodeSType A -> TpDesc false) : TpDesc false
.

Definition MonTp := TpDesc true.
Definition ValTp := TpDesc false.

Definition FunStack := list MonTp.

(* A trivially inhabited "default" function type *)
Definition default_tp : MonTp :=
  Tp_Pi SimpTp_Void (fun _ => Tp_M (Tp_SType SimpTp_Void)).

(* Get the nth element of a list of function types, or default_fun_tp if n is too big *)
Definition nthTp (stk : FunStack) n : MonTp :=
  nth_default' default_tp stk n.

Inductive Clos stk : MonTp -> Type@{entree_u} :=
| MkClos (n:nat) (pf:n < length stk) : Clos stk (nthTp stk n).

(*
Inductive Clos stk (T:MonTp) : Type@{entree_u} :=
| MkClos (n:nat) (pf: isNth T n stk) : Clos stk T.
*)

Lemma noNilClos T (clos : Clos nil T) : False.
  destruct clos. inversion pf.
Qed.

Definition liftClos stk U T (clos : Clos stk T) : Clos (cons U stk) T :=
  match clos with
  | MkClos _ n pf => MkClos (cons U stk) (S n) (lt_n_S _ _ pf)
  end.

Fixpoint decodeType (E:EvType) stk isM (T : TpDesc isM) : Type@{entree_u} :=
  match T with
  | Tp_M R => Clos stk (Tp_M R) + entree E (decodeType E stk false R)
  | Tp_Pi A B => Clos stk (Tp_Pi A B) + forall a, decodeType E stk true (B a)
  | Tp_Arr A B =>
      Clos stk (Tp_Arr A B) + (decodeType E stk false A -> decodeType E stk true B)
  | Tp_Fun A => decodeType E stk true A
  | Tp_SType A => decodeSType A
  | Tp_Pair A B => decodeType E stk false A * decodeType E stk false B
  | Tp_Sum A B => decodeType E stk false A + decodeType E stk false B
  | Tp_Sigma A B => { a:decodeSType A & decodeType E stk false (B a) }
  end.

(* The same as a decoding but the top-level constructor cannot be a closure *)
Definition MonInterp (E:EvType) stk isM (T : TpDesc isM) : Type@{entree_u} :=
  match T with
  | Tp_M R => entree E (decodeType E stk false R)
  | Tp_Pi A B => forall a, decodeType E stk true (B a)
  | Tp_Arr A B => (decodeType E stk false A -> decodeType E stk true B)
  | Tp_Fun A => decodeType E stk true A
  | Tp_SType A => decodeSType A
  | Tp_Pair A B => decodeType E stk false A * decodeType E stk false B
  | Tp_Sum A B => decodeType E stk false A + decodeType E stk false B
  | Tp_Sigma A B => { a:decodeSType A & decodeType E stk false (B a) }
  end.

Definition substClos E stk U (I : MonInterp E (cons U stk) true U)
  T (clos : Clos (cons U stk) T) : Clos stk T + MonInterp E (cons U stk) true T :=
  match clos with
  | MkClos _ 0 _ => inr I
  | MkClos _ (S n) pf => inl (MkClos _ n (lt_S_n _ _ pf))
  end.


Fixpoint substLiftDecoding E stk U (I : MonInterp E (cons U stk) true U) isM T :
  (decodeType E (cons U stk) isM T -> decodeType E stk isM T)
  * (decodeType E stk isM T -> decodeType E (cons U stk) isM T) :=
  match T in TpDesc isM
        return (decodeType E (cons U stk) isM T -> decodeType E stk isM T)
               * (decodeType E stk isM T -> decodeType E (cons U stk) isM T)
  with
  | Tp_M R =>
      ((fun elem =>
          match elem with
          | inl clos =>
              match substClos E stk U I _ clos with
              | inl clos' => inl clos'
              | inr m =>
                  inr (fmap (fst (substLiftDecoding E stk U I false R)) m)
              end
          | inr m =>
              inr (fmap (fst (substLiftDecoding E stk U I false R)) m)
          end)
        ,
        (fun elem =>
           match elem with
           | inl clos => inl (liftClos stk U (Tp_M R) clos)
           | inr m => inr (fmap (snd (substLiftDecoding E stk U I false R)) m)
           end))
  | Tp_Pi A B =>
      ((fun elem =>
          match elem with
          | inl clos =>
              match substClos E stk U I (Tp_Pi A B) clos with
              | inl clos' => inl clos'
              | inr f =>
                  inr (fun a => fst (substLiftDecoding E stk U I true (B a)) (f a))
              end
          | inr f =>
              inr (fun a => fst (substLiftDecoding E stk U I true (B a)) (f a))
          end)
        ,
        (fun elem =>
           match elem with
           | inl clos => inl (liftClos stk U (Tp_Pi A B) clos)
           | inr f => inr (fun a => snd (substLiftDecoding E stk U I true (B a)) (f a))
           end))
  | Tp_Arr A B =>
      ((fun elem =>
          match elem with
          | inl clos =>
              match substClos E stk U I (Tp_Arr A B) clos with
              | inl clos' => inl clos'
              | inr f =>
                  inr (fun arg =>
                         fst (substLiftDecoding E stk U I true B)
                           (f
                              (snd (substLiftDecoding E stk U I false A) arg)))
              end
          | inr f =>
              inr (fun arg =>
                         fst (substLiftDecoding E stk U I true B)
                           (f
                              (snd (substLiftDecoding E stk U I false A) arg)))
          end)
        ,
        (fun elem =>
          match elem with
          | inl clos => inl (liftClos stk U (Tp_Arr A B) clos)
          | inr f =>
              inr (fun arg =>
                         snd (substLiftDecoding E stk U I true B)
                           (f
                              (fst (substLiftDecoding E stk U I false A) arg)))
          end))
  | Tp_Fun A =>
      (fst (substLiftDecoding E stk U I true A),
        snd (substLiftDecoding E stk U I true A))
  | Tp_SType A =>
      (id, id)
  | Tp_Pair A B =>
      ((fun elem =>
          (fst (substLiftDecoding E stk U I false A) (fst elem),
            fst (substLiftDecoding E stk U I false B) (snd elem)))
        ,
        (fun elem =>
           (snd (substLiftDecoding E stk U I false A) (fst elem),
             snd (substLiftDecoding E stk U I false B) (snd elem))))
  | Tp_Sum A B =>
      ((fun elem =>
          match elem with
          | inl x => inl (fst (substLiftDecoding E stk U I false A) x)
          | inr y => inr (fst (substLiftDecoding E stk U I false B) y)
          end)
        ,
        (fun elem =>
          match elem with
          | inl x => inl (snd (substLiftDecoding E stk U I false A) x)
          | inr y => inr (snd (substLiftDecoding E stk U I false B) y)
          end))
  | Tp_Sigma A B =>
      ((fun elem =>
          existT _ (projT1 elem)
            (fst (substLiftDecoding E stk U I false (B (projT1 elem))) (projT2 elem)))
        ,
        (fun elem =>
           existT _ (projT1 elem)
             (snd (substLiftDecoding E stk U I false (B (projT1 elem))) (projT2 elem))))
  end.









Lemma neq_true_false : false <> true.
  intro. inversion H.
Qed.

Print TpDesc_rect. Print eq_rect. Print eq.

Definition MonTp_case (P : forall (T:MonTp), Type)
  (f : forall R, P (Tp_M R))
  (g : forall A B, (forall (a:decodeSType A), P (B a)) -> P (Tp_Pi A B))
  (h : forall A B, P B -> P (Tp_Arr A B)) :
  forall T, P T.
Proof.
  unfold MonTp. remember true as b.

Definition MonTp_case (P : forall (T:MonTp), Type)
  (f : forall R, P (Tp_M R))
  (g : forall A B, (forall (a:decodeSType A), P (B a)) -> P (Tp_Pi A B))
  (h : forall A B, P B -> P (Tp_Arr A B)) :
  forall T, P T :=
  TpDesc_rect
    (fun b U => forall (e:b=true), P (eq_rect b TpDesc U true e))
    (fun R _ _ => f R)
    (fun A B rec _ => g A B (fun a => rec a (eq_refl true)))
    (fun A _ B rec _ => h A B (rec (eq_refl true)))
    (fun _ _ e => neq_true_false e)
    (fun _ _ _ _ e => neq_true_false e)
    (fun _ _ _ _ e => neq_true_false e)
    (fun _ _ _ e => neq_true_false e).

Definition MonInterp E stk (T : MonTp) : Type@{entree_u} :=
  match T with
  end.

  forall (args:FunInput E stk T), entree E (FunOutput E stk T args).

Definition default_interp E stk : FunInterp E stk default_tp :=
  fun v => match projT1 v with end.

Definition StackInterp E stk : Type@{entree_u} :=
  mapTuple (FunInterp E stk) stk.

(* FIXME: this would be straightforward if we used reverse-append in the def of FunInterp *)
Definition liftFunInterp E stk U T (interp : FunInterp E stk T) : FunInterp E (cons U stk) T.
Admitted.

Definition consStackInterp E stk T (f : FunInterp E (cons T stk) T)
  (interps : StackInterp E stk) : StackInterp E (cons T stk) :=
  (f, mapMapTuple _ _ (liftFunInterp E stk T) stk interps).

(* Get the nth function in a StackInterp *)
Definition nthStackInterp E stk T n (isn : isNth T n stk) (defs : StackInterp E stk)
  : FunInterp E stk T :=
  nthProj (FunInterp E stk) T n stk isn.


Fixpoint substLiftDecoding E stk (defs : StackInterp E stk) T :
  (decodeType E stk T -> decodeType E nil T) * (decodeType E nil T -> decodeType E stk T) :=
  match T return (decodeType E stk T -> decodeType E nil T)
                 * (decodeType E nil T -> decodeType E stk T) with
  | Tp_M R =>
      ((fun elem =>
          match elem with
          | inl (MkClos _ _ n pf) =>
            inr (fmap (fst (substLiftDecoding E stk defs R))
                   (nthStackInterp E stk (Tp_M R) n pf defs tt))
          | inr m =>
              inr (fmap (fst (substLiftDecoding E stk defs R)) m)
          end)
        ,
        (fun elem =>
           match elem with
           | inl clos => match noNilClos _ clos with end
           | inr m => inr (fmap (snd (substLiftDecoding E stk defs R)) m)
           end))
  | Tp_FunDep A B =>
      ((fun elem =>
          match elem with
          | inl (MkClos _ _ n pf) =>
          end))
  end.


  | Tp_M R => Clos stk (Tp_M R) + entree E (decodeType E stk R)
  | Tp_FunDep A B => Clos stk (Tp_FunDep A B) + forall a, decodeType E stk (B a)
  | Tp_Fun A B => Clos stk (Tp_Fun A B) + (decodeType E stk A -> decodeType E stk B)
  | Tp_SType A => decodeSType A
  | Tp_Pair A B => decodeType E stk A * decodeType E stk B
  | Tp_Sum A B => decodeType E stk A + decodeType E stk B
  | Tp_Sigma A B => { a:decodeSType A & decodeType E stk (B a) }
  end.




Fixpoint FunInput E stk (T:MonTp) : Type@{entree_u} :=
  match T with
  | Tp_M _ => unit
  | Tp_Pi A B => { a : decodeSType A & FunInput E stk (B a) }
  | Tp_Arr A B => decodeType E stk false A * FunInput E stk B
  end.

(* FIXME: dependent pattern-matching on a MonTp *)
Fixpoint FunOutput E stk (T:MonTp) : FunInput E stk T -> Type@{entree_u} :=
  match T as MonTp return FunInput E stk T -> Type@{entree_u} with
  | Tp_M R => fun _ => decodeType E stk false R
  | Tp_Pi A B => fun args => FunOutput E stk (B (projT1 args)) (projT2 args)
  | Tp_Arr A B => fun args => FunOutput E stk B (snd args)
  end.




Definition FunInterp E stk T : Type@{entree_u} :=
  forall stk' (args:FunInput E (app stk' stk) T),
    entree E (FunOutput E (app stk' stk) T args).

Definition default_interp E stk : FunInterp E stk default_tp :=
  fun _ v => match projT1 v with end.

Definition StackInterp E stk : Type@{entree_u} :=
  mapTuple (FunInterp E stk) stk.

(* FIXME: this would be straightforward if we used reverse-append in the def of FunInterp *)
Definition liftFunInterp E stk U T (interp : FunInterp E stk T) : FunInterp E (cons U stk) T.
Admitted.

Definition consStackInterp E stk T (f : FunInterp E (cons T stk) T)
  (interps : StackInterp E stk) : StackInterp E (cons T stk) :=
  (f, mapMapTuple _ _ (liftFunInterp E stk T) stk interps).

(* Get the nth function in a StackInterp *)
Definition nthStackInterp E stk T n (isn : isNth T n stk) (defs : StackInterp E stk)
  : FunInterp E stk T :=
  nthProj (FunInterp E stk) T n stk isn.

Lemma noNilMClos R (clos : Clos nil (Tp_M R)) : False.
  remember (Tp_M R) as T. destruct clos. induction n; inversion HeqT.
Qed.

Lemma noNilFunClos A B (clos : Clos nil (Tp_Fun A B)) : False.
  remember (Tp_Fun A B) as T. destruct clos. induction n; inversion HeqT.
Qed.

Definition liftNilClos T stk (clos : Clos nil T) : Clos stk T.
Admitted.

Fixpoint liftNilTpElem E stk T : decodeType E nil T -> decodeType E stk T :=
  match T return decodeType E nil T -> decodeType E stk T with
  | Tp_M R =>
      fun elem => match elem with
                  | inl clos => inl (liftNilClos (Tp_M R) stk clos)
                  | inr m => inr (fmap (liftNilTpElem E stk R) m)
                  end
  | Tp_FunDep A B =>
      fun elem => match elem with
                  | inl clos => inl (liftNilClos (Tp_FunDep A B) stk clos)
                  | inr f => inr (fun a => liftNilTpElem E stk (B a) (f a))
                  end
  | Tp_Fun A B =>
      fun elem => match elem with
                  | inl clos => inl (liftNilClos (Tp_Fun A B) stk clos)
                  | inr f => inr (fun a => liftNilTpElem E stk (B a) (f a))
                  end
  | Tp_SType A => fun elem => elem
  | Tp_Pair A B => fun p => (liftNilTpElem E stk A (fst p), liftNilTpElem E stk B (snd p))
  | Tp_Sum A B => fun elem =>
                    match elem with
                    | inl x => inl (liftNilTpElem E stk A x)
                    | inr y => inr (liftNilTpElem E stk B y)
                    end
  | Tp_Sigma A B =>
      fun elem => existT _ (projT1 elem) (liftNilTpElem E stk (B (projT1 elem)) (projT2 elem))
  end.



Inductive StackCall E stk : Type@{entree_u} :=
| MkStackCall n (args : FunInput E stk (nthTp stk n)).

Definition StackCallRet E stk (call: StackCall E stk) :=
  match call with
  | MkStackCall _ _ n args => FunOutput E stk (nthTp stk n) args
  end.

Global Instance EncodingType_StackCall E stk : EncodingType (StackCall E stk) :=
 StackCallRet E stk.


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
