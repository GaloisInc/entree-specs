
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


(***
 *** List utilities
 ***)

(* A version of nth_default that does primary recursion on the list *)
Fixpoint nth_default' {A} (d : A) (l : list A) n : A :=
  match l with
  | nil => d
  | cons x l' => match n with
                 | 0 => x
                 | S n' => nth_default' d l' n'
                 end
  end.

(* Reverse the first list and append the second *)
Fixpoint rev_app {A} (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons x l1' => rev_app l1' (cons x l2)
  end.

(* Reverse and prepend each list in a list of lists *)
Fixpoint revs_app {A} (ls : list (list A)) (l2 : list A) : list A :=
  match ls with
  | nil => l2
  | cons l1 ls' => rev_app l1 (revs_app ls' l2)
  end.

(* Delete the nth element of a list *)
Fixpoint deleteNth {A} n (l : list A) {struct l} : list A :=
  match l with
  | nil => nil
  | cons a l' => match n with
                 | 0 => l'
                 | S n' => cons a (deleteNth n' l')
                 end
  end.

(* Insert an element at the nth position in a list, or at the end if n is too big *)
Fixpoint insertNth {A} (a:A) n l {struct n} : list A :=
  match n with
  | 0 => a :: l
  | S n' => match l with
            | nil => a :: nil
            | b :: l' => b :: insertNth a n' l'
            end
  end.

(* Drop the first n elements of a list *)
Fixpoint drop {A} n (l:list A) {struct n} : list A :=
  match n with
  | 0 => l
  | S n' => match l with
            | nil => nil
            | _ :: l' => drop n' l'
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

Lemma isNthHead {A} {a:A} {b l} (isn : isNth a 0 (cons b l)) : a = b.
Proof.
  inversion isn. reflexivity.
Qed.

Lemma isNthTail {A} {a:A} {n b l} (isn : isNth a (S n) (cons b l)) : isNth a n l.
Proof.
  inversion isn. assumption.
Qed.

Lemma isNthEq {A} {a b:A} {n l} (isn_a : isNth a n l) (isn_b : isNth b n l) : a = b.
Proof.
  revert isn_b; induction isn_a; intros; inversion isn_b.
  - reflexivity.
  - apply IHisn_a; assumption.
Qed.

Definition isNthDelete {A} {a:A} {n l} (isn: isNth a n l) m :
  (m = n) + { n' | isNth a n' (deleteNth m l) }.
Proof.
  revert m l isn; induction n; intros; destruct l.
  - elimtype False; inversion isn.
  - destruct m; [ left; reflexivity | ]. right. exists 0. inversion isn. constructor.
  - elimtype False; inversion isn.
  - destruct m; [ right; exists n; eapply isNthTail; eassumption | ].
    destruct (IHn m l (isNthTail isn)).
    + left; subst m; reflexivity.
    + right; destruct s. exists (S x). econstructor; eassumption.
Defined.

Definition isNthUnInsert {A} {a:A} {b n m l}
  (isn: isNth a n (insertNth b m l)) : (a = b) + { n' | isNth a n' l }.
Proof.
  revert m l isn; induction n; intros.
  - destruct m; [ left; inversion isn; reflexivity | ].
    destruct l; [ left; inversion isn; reflexivity | ].
    right. exists 0. inversion isn. constructor.
  - destruct m.
    + right; exists n. inversion isn. assumption.
    + destruct l; [ elimtype False; inversion isn; inversion H1 | ].
      destruct (IHn m l (isNthTail isn)); [ left; assumption | ].
      destruct s. right; exists (S x); constructor; assumption.
Qed.


(* Build the right-nested tuple type of a list of types formed by mapping a
function across a list *)
Polymorphic Fixpoint mapTuple@{u v} {T:Type@{v}} (f : T -> Type@{u}) (xs : list T) : Type@{u} :=
  match xs with
  | nil => unit
  | cons x xs' => f x * mapTuple f xs'
  end.

Polymorphic Fixpoint mapMapTuple@{u v} {T:Type@{v}} {f g : T -> Type@{u}}
  (fg : forall t, f t -> g t) (xs : list T) : mapTuple f xs -> mapTuple g xs :=
  match xs return mapTuple f xs -> mapTuple g xs with
  | nil => fun u => u
  | cons x xs' => fun tup => (fg x (fst tup), mapMapTuple fg xs' (snd tup))
  end.

(* Append two mapTuple tuples *)
Polymorphic Fixpoint appMapTuple@{u v} {T:Type@{v}} {f : T -> Type@{u}} (xs ys : list T) :
  mapTuple f xs -> mapTuple f ys -> mapTuple f (app xs ys) :=
  match xs return mapTuple f xs -> mapTuple f ys -> mapTuple f (app xs ys) with
  | nil => fun _ tup2 => tup2
  | cons x xs' =>
      fun tup1 tup2 => (fst tup1, appMapTuple xs' ys (snd tup1) tup2)
  end.

(* Split a mapTuple on an append in two *)
Polymorphic Fixpoint splitMapTuple@{u v} {T:Type@{v}} {f : T -> Type@{u}} {xs ys : list T} :
  mapTuple f (app xs ys) -> mapTuple f xs * mapTuple f ys :=
  match xs return mapTuple f (app xs ys) -> mapTuple f xs * mapTuple f ys with
  | nil => fun tup => (tt, tup)
  | cons x xs' =>
      fun tup => ((fst tup, fst (splitMapTuple (snd tup))),
                   snd (splitMapTuple (snd tup)))
  end.

(* Drop the first n elements from a mapTuple *)
Polymorphic Fixpoint dropMapTuple@{u v} {T:Type@{v}} {f : T -> Type@{u}}
  n {xs : list T} : mapTuple f xs -> mapTuple f (drop n xs) :=
  match n return mapTuple f xs -> mapTuple f (drop n xs) with
  | 0 => fun tup => tup
  | S n' =>
      match xs return mapTuple f xs -> mapTuple f (drop (S n') xs) with
      | nil => fun tup => tup
      | _ :: xs' => fun tup => dropMapTuple n' (snd tup)
      end
  end.

(* Project the nth element of a mapTuple, using a default if n is too big *)
Polymorphic Fixpoint nthProjDefault@{u v} {T:Type@{v}} {f : T -> Type@{u}} {dT:T} (d:f dT) {xs}
  : forall n, mapTuple f xs -> f (nth_default' dT xs n) :=
  match xs return forall n, mapTuple f xs -> f (nth_default' dT xs n) with
  | nil => fun _ _ => d
  | cons x xs' =>
      fun n =>
        match n return mapTuple f (cons x xs') -> f (nth_default' dT (cons x xs') n) with
        | 0 => fun tup => fst tup
        | S n' => fun tup => nthProjDefault d n' (snd tup)
        end
  end.


Polymorphic Fixpoint nthProj@{u v} {T:Type@{v}} {f : T -> Type@{u}} {t n} :
  forall {l}, isNth t n l -> mapTuple f l -> f t.
Proof.
  induction n; intro l; destruct l; intros isn mtup.
  - elimtype False; inversion isn.
  - destruct mtup. rewrite (isNthHead isn). assumption.
  - elimtype False; inversion isn.
  - destruct mtup. apply (IHn l (isNthTail isn) m).
Defined.


(*
Polymorphic Fixpoint nthProj@{u v} {T:Type@{v}} (f : T -> Type@{u}) t n :
  forall l, isNth t n l -> mapTuple f l -> f t :=
  match n return forall l, isNth t n l -> mapTuple f l -> f t with
  | 0 => fun l =>
           match l return isNth t 0 l -> mapTuple f l -> f t with
           | nil => fun isn => match not_isNth_nil t 0 isn with end
           | cons b l' =>
               fun isn 
  end.
*)


(**
 ** List Inclusions
 **)

(* A single step of list inclusion, which adds an element into a list; note that
this in in Type, not in Prop, because we care about the contents *)
Inductive listIncl1 {A} : list A -> list A -> Type :=
| incl1Base a l2 : listIncl1 l2 (cons a l2)
| incl1Step a l1 l2 : listIncl1 l1 l2 -> listIncl1 (cons a l1) (cons a l2)
.

(* Map an index through a single step of list inclusion *)
Fixpoint applyListIncl1 {A l1 l2} (incl: @listIncl1 A l1 l2) n : nat :=
  match incl with
  | incl1Base _ _ => S n
  | incl1Step _ l1' l2' incl' =>
      match n with
      | 0 => 0
      | S n' => S (applyListIncl1 incl' n')
      end
  end.

(* Map an isNth proof through a single step of list inclusion *)
Lemma applyListIncl1Nth {A l1 l2} (incl: @listIncl1 A l1 l2) a n :
  isNth a n l1 -> isNth a (applyListIncl1 incl n) l2.
Proof.
  revert n; induction incl; intros; [ | destruct n ].
  - constructor; assumption.
  - inversion H. constructor.
  - constructor. apply IHincl. inversion H. assumption.
Qed.

(* This is the reflexive-transitive closure of listIncl1, except we need it in
Type, not Prop, because we care about the contents *)
Inductive listIncl {A} : list A -> list A -> Type :=
| reflListIncl l : listIncl l l
| stepListIncl {l1 l2} (incl: listIncl1 l1 l2) : listIncl l1 l2
| compListIncl {l1 l2 l3} (incl1 : listIncl l1 l2) (incl2 : listIncl l2 l3)
  : listIncl l1 l3
.

Fixpoint applyListIncl {A l1 l2} (incl: @listIncl A l1 l2) : nat -> nat :=
  match incl with
  | reflListIncl _ => fun n => n
  | stepListIncl incl1 => applyListIncl1 incl1
  | compListIncl incl1 incl2 => fun n => applyListIncl incl2 (applyListIncl incl1 n)
  end.

Fixpoint applyListInclNth {A l1 l2} (incl: @listIncl A l1 l2) :
  forall {a n}, isNth a n l1 -> isNth a (applyListIncl incl n) l2 :=
  match incl in listIncl l1 l2
        return forall a n, isNth a n l1 ->
                           isNth a (applyListIncl incl n) l2 with
  | reflListIncl _ => fun _ _ isn => isn
  | stepListIncl incl1 => applyListIncl1Nth incl1
  | compListIncl incl1 incl2 =>
      fun a n isn => applyListInclNth incl2 (applyListInclNth incl1 isn)
  end.

(* Build an inclusion from nil into any list *)
Fixpoint nilListIncl {A} (l:list A) : listIncl nil l :=
  match l return listIncl nil l with
  | nil => reflListIncl nil
  | a :: l' => compListIncl (nilListIncl l') (stepListIncl (incl1Base a l'))
  end.

(* Prefix a listIncl1 with a single element that stays constant *)
Definition consListIncl1 {A} (a:A) {l1 l2} (incl : listIncl1 l1 l2) :
  listIncl1 (cons a l1) (cons a l2) :=
  incl1Step a _ _ incl.

(* Prefix a listIncl with a single element that stays constant *)
Fixpoint consListIncl {A} (a:A) {l1 l2} (incl : listIncl l1 l2) :
  listIncl (cons a l1) (cons a l2) :=
  match incl in listIncl l1 l2 return listIncl (cons a l1) (cons a l2) with
  | reflListIncl l => reflListIncl (cons a l)
  | stepListIncl incl1 => stepListIncl (consListIncl1 a incl1)
  | compListIncl incl1 incl2 =>
      compListIncl (consListIncl a incl1) (consListIncl a incl2)
  end.

(* Cons an element onto the right side of a listIncl *)
Definition consListInclR {A} (a:A) {l1 l2} (incl : listIncl l1 l2)
  : listIncl l1 (cons a l2) :=
  compListIncl incl (stepListIncl (incl1Base a l2)).

(* Un-cons an element onto the right side of a listIncl *)
Definition consListInclL {A} (a:A) {l1 l2} (incl : listIncl (cons a l1) l2)
  : listIncl l1 l2 :=
  compListIncl (stepListIncl (incl1Base a l1)) incl.


Definition pushoutListIncl1 {A} {l1 l2 l3}
  (incl1 : listIncl1 l1 l2) (incl2 : listIncl1 l1 l3) :
  { l4:list A & listIncl1 l2 l4 & listIncl1 l3 l4 }.
Proof.
  revert l3 incl2; induction incl1; intros; [ | inversion incl2 ].
  - exists (a :: l3); [ apply (incl1Step a _ _ incl2) | apply incl1Base ].
  - subst l3. subst l0. exists (a0 :: a :: l2); [ apply incl1Base | ].
    eapply incl1Step; eapply incl1Step; eassumption.
  - subst l3. subst a0. subst l0.
    destruct (IHincl1 l4 X) as [ l5 incl1' incl2' ].
    exists (a :: l5); eapply incl1Step; eassumption.
Qed.

Definition pushoutListInclOne {A} {l1 l2 l3}
  (incl1 : listIncl1 l1 l2) (incl2 : listIncl l1 l3) :
  { l4:list A & listIncl l2 l4 & listIncl1 l3 l4 }.
Proof.
  revert l2 incl1; induction incl2; intros.
  - exists l2; [ constructor | assumption ].
  - destruct (pushoutListIncl1 incl incl1) as [ l4 incl1' incl2' ].
    exists l4; [ apply stepListIncl | ]; assumption.
  - destruct (IHincl2_1 l0 incl1) as [ l4 incl1' incl2' ].
    destruct (IHincl2_2 _ incl2') as [ l5 incl1'' incl2'' ].
    exists l5; [ | assumption ].
    eapply compListIncl; eassumption.
Defined.

Definition pushoutListIncl {A} {l1 l2 l3}
  (incl1 : listIncl l1 l2) (incl2 : listIncl l1 l3) :
  { l4:list A & listIncl l2 l4 & listIncl l3 l4 }.
Proof.
  revert l3 incl2; induction incl1; intros.
  - exists l3; try assumption; constructor.
  - destruct (pushoutListInclOne incl incl2) as [ l4 incl1' incl2' ].
    exists l4; try assumption; apply stepListIncl; assumption.
  - destruct (IHincl1_1 l0 incl2) as [ l4 incl1' incl2' ].
    destruct (IHincl1_2 l4 incl1') as [ l5 incl1'' incl2'' ].
    exists l5; [ assumption | eapply compListIncl; eassumption ].
Defined.

Definition pushoutListInclList {A l1 l2 l3}
  (incl1 : listIncl l1 l2) (incl2 : listIncl l1 l3) : list A :=
  match pushoutListIncl incl1 incl2 with
  | existT2 _ _ l _ _ => l
  end.

Definition pushoutListInclIncl1 {A l1 l2 l3}
  (incl1 : listIncl l1 l2) (incl2 : listIncl l1 l3)
  : @listIncl A l2 (pushoutListInclList incl1 incl2) :=
  projT2 (sigT_of_sigT2 (pushoutListIncl incl1 incl2)).

Definition pushoutListInclIncl2 {A l1 l2 l3}
  (incl1 : listIncl l1 l2) (incl2 : listIncl l1 l3)
  : @listIncl A l3 (pushoutListInclList incl1 incl2) :=
  projT3 (pushoutListIncl incl1 incl2).


Definition deleteNthIncl {A} n (l:list A) : listIncl (deleteNth n l) l.
Proof.
  revert n; induction l; intros; [ | destruct n ].
  - apply reflListIncl.
  - apply stepListIncl; apply incl1Base.
  - apply consListIncl. apply IHl.
Defined.

Definition undeleteIncl {A l1 l2 n} (incl : @listIncl A (deleteNth n l1) l2) :
  { l3 & listIncl l1 l3 & listIncl l2 l3 } :=
  pushoutListIncl (deleteNthIncl n l1) incl.

Definition insertListIncl1 {A l1 l2} n a (incl : @listIncl1 A l1 l2) :
  listIncl1 (insertNth a n l1) (insertNth a (applyListIncl1 incl n) l2).
Proof.
  revert n; induction incl; intros; [ | destruct n ].
  - constructor.
  - constructor; constructor; assumption.
  - simpl. constructor. apply IHincl.
Defined.

Definition insertListIncl {A l1 l2} n a (incl : @listIncl A l1 l2) :
  listIncl (insertNth a n l1) (insertNth a (applyListIncl incl n) l2).
Proof.
  revert n; induction incl; intros.
  - constructor.
  - apply stepListIncl; apply (insertListIncl1 n a incl).
  - eapply compListIncl; [ apply IHincl1 | apply IHincl2 ].
Defined.

Definition insertListInclR {A} (a:A) n l : listIncl l (insertNth a n l).
Proof.
  apply stepListIncl; revert l; induction n; intro l;
    [ | destruct l ]; constructor.
  apply IHn.
Defined.


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

(* Proof that a TpDesc is a monadic function type *)
Fixpoint isFunTp (T:TpDesc) : Prop :=
  match T with
  | Tp_M _ => True
  | Tp_Pi A B => forall a, isFunTp (B a)
  | Tp_Arr A B => isFunTp B
  | _ => False
  end.


(* A "function index" is a monadic function referred to by index. It is
essentially just a nat, but we make it a distinct type to make things clearer *)
Inductive FunIx (T:TpDesc) : Type@{entree_u} :=
| MkFunIx (n:nat).

Definition funIxIx {T} (f:FunIx T) : nat :=
  match f with
  | MkFunIx _ n => n
  end.

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


(** Fun calls **)


Inductive FunCall : Type@{entree_u} :=
| MkFunCall T (f : FunIx T) (args : FunInput T).

Definition FunCallRet (call: FunCall) :=
  match call with
  | MkFunCall _ _ args => FunOutput _ args
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
Section fixtree.

Context (E : EvType).

(* The functor defining a single constructor of a fixtree *)
Variant fixtreeF (F : Type@{entree_u} -> Type@{entree_u}) (R:Type@{entree_u}) : Type@{entree_u} :=
  | Fx_RetF (r : R)
  | Fx_TauF (t : F R)
  | Fx_VisF (e : E) (k : encodes e -> F R)
  | Fx_CallF (call : FunCall) (k : FunCallRet call -> F R)
  | Fx_MkFunF (T : TpDesc)
      (body : forall (args:FunInput T), F (FunOutput T args))
      (k : FunIx T -> F R)
.

(* "Tying the knot" by defining entrees as the greatest fixed-point of fixtreeF *)
CoInductive fixtree R : Type@{entree_u} :=
  go { _fxobserve : fixtreeF fixtree R }.

End fixtree.

(* Implicit arguments and helpful notations for fixtrees *)
Arguments Fx_RetF {_ _ _} _.
Arguments Fx_TauF {_ _ _} _.
Arguments Fx_VisF {_ _ _} _ _.
Arguments Fx_CallF {_ _ _} _ _.
Arguments Fx_MkFunF {_ _ _ _} _ _.
Notation fixtree' E R := (fixtreeF E (fixtree E) R).
Notation Fx_Tau t := {| _fxobserve := Fx_TauF t |}.
Notation Fx_Ret r := {| _fxobserve := Fx_RetF r |}.
Notation Fx_Vis e k := {| _fxobserve := Fx_VisF e k |}.
Notation Fx_Call call k := {| _fxobserve := Fx_CallF call k |}.
Notation Fx_MkFun body k := {| _fxobserve := Fx_MkFunF body k |}.

(* "Observe" the top-most constructor of an fixtree by unwrapping it one step *)
Definition fxobserve {E R} (t : fixtree E R) : fixtree' E R :=
  _fxobserve _ _ t.


(*** The basic operations on fixtrees ***)

Module FixTree.

(* This defines the bind operation by coinduction on the left-hand side of the
   bind; can also be seen as "substituting" an observed computation tree ot for
   the return value of a continuation k *)
Definition subst' {E : EvType} {R S : Type@{entree_u}}
           (k : R -> fixtree E S) : fixtree' E R -> fixtree E S  :=
  cofix _subst (ot : fixtree' E R) :=
    match ot with
    | Fx_RetF r => k r
    | Fx_TauF t => Fx_Tau (_subst (fxobserve t))
    | Fx_VisF e k => Fx_Vis e (fun x => _subst (fxobserve (k x)))
    | Fx_CallF call k => Fx_Call call (fun x => _subst (fxobserve (k x)))
    | Fx_MkFunF body k => Fx_MkFun body (fun x => _subst (fxobserve (k x)))
    end.

(* Wrap up subst' so it operates on an fixtree instead of an fixtree' *)
Definition subst {E : EvType} {R S : Type@{entree_u}}
           (k : R -> fixtree E S) : fixtree E R -> fixtree E S :=
  fun t => subst' k (fxobserve t).

(* Monadic bind for fixtrees is just subst *)
Definition bind {E} {R S : Type@{entree_u}} 
           (t : fixtree E R) (k : R -> fixtree E S) :=
  subst k t.

(* Iterate a body on successive inputs of type I until it returns an R *)
Definition iter {E} {I R : Type@{entree_u}}
           (body : I -> fixtree E (I + R)) : I -> fixtree E R :=
  cofix _iter i :=
    bind (body i) (fun ir => match ir with
                          | inl i' => Fx_Tau (_iter i')
                          | inr r => Fx_Ret r
                          end).

(* Map a pure function over the return value(s) of an entree *)
Definition map {E} {R S} (f : R -> S) (t : fixtree E R) :=
  bind t (fun r => Fx_Ret (f r)).

(* Build a computation tree that performs a single event / effect in E *)
Definition trigger {E:EvType} (e : E) : fixtree E (encodes e) :=
  Fx_Vis e (fun x => Fx_Ret x).

(* The nonterminating computation that spins forever and never does anything *)
CoFixpoint spin {E R} : fixtree E R := Fx_Tau spin.

End FixTree.

CoFixpoint embedEntree' {E:EvType} {R} (ot: entree' E R) : fixtree E R :=
  match ot with
  | RetF r => Fx_Ret r
  | TauF t' => Fx_Tau (embedEntree' (observe t'))
  | VisF e k => Fx_Vis e (fun x => embedEntree' (observe (k x)))
  end.

Definition embedEntree {E:EvType} {R} (t: entree E R) : fixtree E R :=
  embedEntree' (observe t).

Definition FxInterp E T :=
 forall (args:FunInput T), fixtree E (FunOutput T args).

Definition SomeFxInterp E := { T & FxInterp E T }.

Definition caseSomeFxInterp {E} T (d : SomeFxInterp E) : option (FxInterp E T) :=
  match dec_eq_TpDesc (projT1 d) T with
  | left e => Some (eq_rect (projT1 d) (FxInterp E) (projT2 d) T e)
  | right _ => None
  end.

Definition FxInterps E : Type@{entree_u} := list (SomeFxInterp E).

Definition nthSomeFxInterp {E} (defs : FxInterps E) n : option (SomeFxInterp E) :=
  nth_error defs n.

Definition getFxInterp {E} (defs : FxInterps E) {T} (f : FunIx T) : option (FxInterp E T) :=
  match nthSomeFxInterp defs (funIxIx f) with
  | Some d => caseSomeFxInterp T d
  | None => None
  end.

Definition callFxInterp {E} (defs : FxInterps E) (call : FunCall)
  : option (fixtree E (FunCallRet call)) :=
  match call with
  | MkFunCall _ f args =>
      match getFxInterp defs f with
      | Some d => Some (d args)
      | None => None
      end
  end.

Definition consFxInterp {E} (defs : FxInterps E) {T} (d : FxInterp E T) : FxInterps E :=
  app defs (existT (FxInterp E) T d :: nil).

CoFixpoint interp_fixtree' {E:EvType} {R} (err:entree E R) (defs : FxInterps E)
  (ot : fixtree' E R) : entree E R :=
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

Definition interp_fixtree {E:EvType} {R}
  (err:entree E R) (defs : FxInterps E) (t : fixtree E R) : entree E R :=
  interp_fixtree' err defs (fxobserve t).


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

#[global] Instance Functor_fixtree {E} : Functor (fixtree E) :=
  { fmap := @FixTree.map E }.

#[global] Instance Applicative_fixtree {E} : Applicative (fixtree E) :=
  {
    pure := fun _  x => Fx_Ret x;
    ap := fun _ _ f x =>
            FixTree.bind f (fun f => FixTree.bind x (fun x => Fx_Ret (f x)) );

  }.

#[global] Instance Monad_fixtree {E} : Monad (fixtree E) :=
  {
    ret := fun _ x => Fx_Ret x;
    bind := @FixTree.bind E;
  }.

#[global] Instance MonadIter_fixtree {E} : MonadIter (fixtree E) :=
  fun _ _ => FixTree.iter.
