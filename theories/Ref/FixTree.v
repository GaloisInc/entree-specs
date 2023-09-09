
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


Polymorphic Fixpoint nthProj@{u v} {T:Type@{v}} (f : T -> Type@{u}) t n :
  forall l, isNth t n l -> mapTuple f l -> f t.
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


(** Syntactic subterms of type descriptions **)

(* The notion that a type description is a structural subterm of another *)
Inductive ImmDescSubterm : TpDesc -> TpDesc -> Prop :=
| Subt_M R : ImmDescSubterm R (Tp_M R)
| Subt_Pi A B a : ImmDescSubterm (B a) (Tp_Pi A B)
| Subt_ArrL A B : ImmDescSubterm A (Tp_Arr A B)
| Subt_ArrR A B : ImmDescSubterm B (Tp_Arr A B)
| Subt_PairL A B : ImmDescSubterm A (Tp_Pair A B)
| Subt_PairR A B : ImmDescSubterm B (Tp_Pair A B)
| Subt_SumL A B : ImmDescSubterm A (Tp_Sum A B)
| Subt_SumR A B : ImmDescSubterm B (Tp_Sum A B)
| Subt_Sigma A B a : ImmDescSubterm (B a) (Tp_Sigma A B)
.

Inductive DescSubterm (T U : TpDesc) : Prop :=
| Subt1 : ImmDescSubterm T U -> DescSubterm T U
| SubtTrans V : DescSubterm T V -> ImmDescSubterm V U -> DescSubterm T U
.

Definition castDescSubtLeft T U V (e : T = U) (subt: DescSubterm T V) : DescSubterm U V :=
  eq_rect T (fun x => DescSubterm x V) subt U e.

Global Instance transDescSubterm : Transitive DescSubterm.
Proof.
  intros T U V subTU subUV. revert T subTU; induction subUV; intros.
  - eapply SubtTrans; eassumption.
  - eapply SubtTrans; [ | eassumption ]. apply IHsubUV. assumption.
Qed.

Lemma wfDescSubterm : well_founded DescSubterm.
Proof.
  intro T; induction T; constructor; intros.
  - inversion H.
    + inversion H0. apply IHT.
    + destruct IHT; apply H2. inversion H1. rewrite <- H5; assumption.
  - inversion H0; clear H0.
    + revert H; inversion H1; intros. apply H0.
    + revert H H1; inversion H2; intros. destruct (H0 a0). apply H5. assumption.
  - inversion H; clear H.
    + inversion H0; assumption.
    + inversion H1; [ destruct IHT1 as [acc] | destruct IHT2 as [acc] ];
        apply acc; subst V; subst A; subst B; assumption.
  - inversion H; [ inversion H0 | inversion H1 ].
  - inversion H; clear H.
    + inversion H0; assumption.
    + inversion H1; [ destruct IHT1 as [acc] | destruct IHT2 as [acc] ];
        apply acc; subst V; subst A; subst B; assumption.
  - inversion H; clear H.
    + inversion H0; assumption.
    + inversion H1; [ destruct IHT1 as [acc] | destruct IHT2 as [acc] ];
        apply acc; subst V; subst A; subst B; assumption.
  - inversion H0; clear H0.
    + revert H; inversion H1; intros. apply H0.
    + revert H H1; inversion H2; intros. destruct (H0 a0). apply H5. assumption.
Qed.

Lemma not_self_DescSubterm T : DescSubterm T T -> False.
Proof.
  refine (well_founded_ind wfDescSubterm (fun T => DescSubterm T T -> False) _ T).
  intros.
  apply (H x H0 H0).
Qed.


(** Function variables as indexes into a function type stack **)

Definition FunStack := list TpDesc.

(* A trivially inhabited "default" function type *)
Definition default_tp : TpDesc :=
  Tp_Pi SimpTp_Void (fun _ => Tp_M (Tp_SType SimpTp_Void)).

(* Get the nth element of a list of function types, or default_fun_tp if n is too big *)
Definition nthTp (stk : FunStack) n : TpDesc :=
  nth_default' default_tp stk n.

(*
Inductive StkFun stk : TpDesc -> Type@{entree_u} :=
| MkStkFun (n:nat) (pf:n < length stk) : StkFun stk (nthTp stk n).
*)

Inductive StkFun stk (T:TpDesc) : Type@{entree_u} :=
| MkStkFun (n:nat) (isn: isNth T n stk) : StkFun stk T.

Lemma noNilStkFun T (stkf : StkFun nil T) : False.
  destruct stkf. inversion isn.
Qed.

Definition liftStkFun {stk stk'} (incl: listIncl stk stk') {T} (stkf : StkFun stk T)
  : StkFun stk' T :=
  match stkf with
  | MkStkFun _ _ n isn =>
      MkStkFun _ _ (applyListIncl incl n) (applyListInclNth incl isn)
  end.

Definition lowerStkFun {stk T m U} (stkf : StkFun (insertNth U m stk) T) :
  StkFun stk T + (T = U).
Proof.
  destruct stkf. destruct (isNthUnInsert isn).
  - right; assumption.
  - destruct s. left. exact (MkStkFun _ _ x i).
Defined.

(*
Definition lowerStkFun {stk T} m (stkf : StkFun stk T) :
  StkFun (deleteNth m stk) T + isNth T m stk.
Proof.
  destruct stkf. destruct (isNthDelete isn m).
  - subst m; right; assumption.
  - destruct s. left. exact (MkStkFun _ _ x i).
Defined.
*)

Definition case0StkFun {stk U T} (stkf : StkFun (cons U stk) T) :
  StkFun stk T + (T = U).
Proof.
  destruct (@lowerStkFun stk T 0 U stkf).
  - left; assumption.
  - right; assumption.
Defined.

(*
Definition case0StkFun {stk U T} (stkf : StkFun (cons U stk) T) :
  StkFun stk T + (T = U).
Proof.
  destruct (@lowerStkFun (cons U stk) T 0 stkf).
  - left; assumption.
  - right. eapply isNthEq; try eassumption. constructor.
Defined.
*)

(*
Definition case0StkFun stk U T (clos : StkFun (cons U stk) T) :
  StkFun stk T + (T = U) :=
  match clos in StkFun _ T return StkFun stk T + (T = U) with
  | MkStkFun _ 0 _ => inr (eq_refl U)
  | MkStkFun _ (S n) pf => inl (MkStkFun _ n (lt_S_n _ _ pf))
  end.

Definition caseNStkFun stk stks U T :
  StkFun (revs_app stks (cons U stk)) T -> StkFun (revs_app stks stk) T + (T = U).
Admitted.
*)


(** Elements of type descriptions **)

Fixpoint tpElem (E:EvType) stk (T : TpDesc) : Type@{entree_u} :=
  match T with
  | Tp_M R => StkFun stk (Tp_M R) + entree E (tpElem E stk R)
  | Tp_Pi A B => StkFun stk (Tp_Pi A B) + forall a, tpElem E stk (B a)
  | Tp_Arr A B =>
      StkFun stk (Tp_Arr A B) +
        (forall stk' (incl : listIncl stk stk'), tpElem E stk' A -> tpElem E stk' B)
  | Tp_SType A => stpElem A
  | Tp_Pair A B => tpElem E stk A * tpElem E stk B
  | Tp_Sum A B => tpElem E stk A + tpElem E stk B
  | Tp_Sigma A B => { a:stpElem A & tpElem E stk (B a) }
  end.


Fixpoint liftTpElem {E stk stk'} (incl: listIncl stk stk') {T} :
  tpElem E stk T -> tpElem E stk' T :=
  match T return tpElem E stk T -> tpElem E stk' T with
  | Tp_M R => fun elem => match elem with
                          | inl stkf => inl (liftStkFun incl stkf)
                          | inr m => inr (fmap (liftTpElem incl (T:=R)) m)
                          end
  | Tp_Pi A B => fun elem => match elem with
                             | inl stkf => inl (liftStkFun incl stkf)
                             | inr f => inr (fun a => liftTpElem incl (f a))
                             end
  | Tp_Arr A B => fun elem =>
                    match elem with
                    | inl stkf => inl (liftStkFun incl stkf)
                    | inr f => inr (fun stk' incl' arg =>
                                      f stk' (compListIncl incl incl') arg)
                    end
  | Tp_SType A => fun elem => elem
  | Tp_Pair A B => fun elem => (liftTpElem incl (fst elem),
                                 liftTpElem incl (snd elem))
  | Tp_Sum A B => fun elem => match elem with
                              | inl x => inl (liftTpElem incl x)
                              | inr y => inr (liftTpElem incl y)
                              end
  | Tp_Sigma A B =>
      fun elem =>
        existT _ (projT1 elem) (liftTpElem incl (projT2 elem))
  end.


(** Interpretations of function types **)

(* An interpretation of a monadic function type *)
(* NOTE: this treats a non-monadic return type as M Empty_set *)
Fixpoint FunInterp (E:EvType) stk (T : TpDesc) : Type@{entree_u} :=
  match T with
  | Tp_M R => entree E (tpElem E stk R)
  | Tp_Pi A B => forall a, FunInterp E stk (B a)
  | Tp_Arr A B => (forall stk', tpElem E (rev_app stk' stk) A ->
                                FunInterp E (rev_app stk' stk) B)
  | _ => entree E Empty_set
  end.

(*
Definition defaultFunInterp E stk : FunInterp E stk default_tp :=
  fun v => match v with end.
*)

(*
Definition FunInterpToElem E stk T : FunInterp E stk T -> tpElem E stk T.
Admitted.
*)

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

Fixpoint FunOutputDesc E stk T : FunInput E stk T -> TpDesc :=
  match T return FunInput E stk T -> TpDesc with
  | Tp_M R => fun _ => R
  | Tp_Pi A B => fun args => FunOutputDesc E stk (B (projT1 args)) (projT2 args)
  | Tp_Arr A B => fun args => FunOutputDesc E stk B (snd args)
  | _ => fun _ => Tp_SType SimpTp_Void
  end.

Definition FunOutput E stk T (args: FunInput E stk T) : Type@{entree_u} :=
  tpElem E stk (FunOutputDesc E stk T args).

Lemma FunOutputSubterm {E stk T} (args: FunInput E stk T) :
  DescSubterm (FunOutputDesc _ _ _ args) T
  + (FunOutputDesc _ _ _ args = Tp_SType SimpTp_Void).
Proof.
  revert args; induction T; intros.
  - left; apply Subt1; constructor.
  - destruct args as [ a args ]. destruct (X a args); [ | right; assumption ].
    left; etransitivity; [ eassumption | ]. apply Subt1; constructor.
  - destruct args as [ arg args ].
    destruct (IHT2 args); [ | right; assumption ].
    left; etransitivity; [ eassumption | ]. apply Subt1; constructor.
  - right; reflexivity.
  - right; reflexivity.
  - right; reflexivity.
  - right; reflexivity.
Qed.


Fixpoint liftFunInput {E stk stk' T} (incl: listIncl stk stk') :
  FunInput E stk T -> FunInput E stk' T :=
  match T return FunInput E stk T -> FunInput E stk' T with
  | Tp_M R => fun args => args
  | Tp_Pi A B =>
      fun args =>
        existT _ (projT1 args) (liftFunInput incl (projT2 args))
  | Tp_Arr A B =>
      fun args => (liftTpElem incl (fst args),
                    liftFunInput incl (snd args))
  | Tp_SType A => fun args => args
  | Tp_Pair A B => fun args => args
  | Tp_Sum A B => fun args => args
  | Tp_Sigma A B => fun args => args
  end.

Definition lift0FunInput {E stk U T}
  : FunInput E stk T -> FunInput E (cons U stk) T :=
  liftFunInput (insertListInclR U 0 stk).

Lemma liftFunOutputEq {E stk stk' T} (incl: listIncl stk stk') :
  forall args, FunOutputDesc E stk' T (liftFunInput incl args)
               = FunOutputDesc E stk T args.
Proof.
  induction T; intros; try reflexivity; simpl.
  - apply H.
  - apply IHT2.
Qed.


(* If T is a syntactic subterm of some type U in the corecursive function
context, then an element of type T cannot make a call at type U, so we can
remove U from its context *)
Fixpoint lowerSubtermTpElem (E:EvType) stk U n T :
  DescSubterm T U -> tpElem E (insertNth U n stk) T -> tpElem E stk T :=
  match T return DescSubterm T U -> tpElem E (insertNth U n stk) T ->
                 tpElem E stk T with
  | Tp_M R =>
      fun subt elem =>
        match elem with
        | inl stkf =>
            match lowerStkFun stkf with
            | inl stkf' => inl stkf'
            | inr e =>
                match not_self_DescSubterm U
                        (castDescSubtLeft (Tp_M R) U U e subt) with end
            end
        | inr comp =>
            inr (fmap (lowerSubtermTpElem E stk U n R
                         (transitivity (Subt1 _ _ (Subt_M R)) subt)) comp)
        end
  | Tp_Pi A B =>
      fun subt elem =>
        match elem with
        | inl stkf =>
            match lowerStkFun stkf with
            | inl stkf' => inl stkf'
            | inr e =>
                match not_self_DescSubterm U
                        (castDescSubtLeft _ U U e subt) with end
            end
        | inr f =>
            inr (fun a =>
                   lowerSubtermTpElem E stk U n (B a)
                     (transitivity (Subt1 _ _ (Subt_Pi _ _ a)) subt) (f a))
        end
  | Tp_Arr A B =>
      fun subt elem =>
        match elem with
        | inl stkf =>
            match lowerStkFun stkf with
            | inl stkf' => inl stkf'
            | inr e =>
                match not_self_DescSubterm U
                        (castDescSubtLeft _ U U e subt) with end
            end
        | inr f =>
            inr (fun stk' (incl : listIncl stk stk') arg =>
                   lowerSubtermTpElem E _ U _ B
                     (transitivity (Subt1 _ _ (Subt_ArrR A B)) subt)
                     (f _ (insertListIncl n U incl)
                        (liftTpElem (insertListInclR U (applyListIncl incl n) stk') arg)))
        end
  | Tp_SType _ => fun _ elem => elem
  | Tp_Pair A B =>
      fun subt elem =>
        (lowerSubtermTpElem E stk U n A
           (transitivity (Subt1 _ _ (Subt_PairL A B)) subt)
           (fst elem),
          lowerSubtermTpElem E stk U n B
            (transitivity (Subt1 _ _ (Subt_PairR A B)) subt)
            (snd elem))
  | Tp_Sum A B =>
      fun subt elem =>
        match elem with
        | inl x =>
            inl (lowerSubtermTpElem E stk U n A
                   (transitivity (Subt1 _ _ (Subt_SumL A B)) subt)
                   x)
        | inr y =>
            inr (lowerSubtermTpElem E stk U n B
                   (transitivity (Subt1 _ _ (Subt_SumR A B)) subt)
                   y)
        end
  | Tp_Sigma A B =>
      fun subt elem =>
        existT _ (projT1 elem)
          (lowerSubtermTpElem E stk U n (B (projT1 elem))
             (transitivity (Subt1 _ _ (Subt_Sigma A B (projT1 elem))) subt)
             (projT2 elem))
  end.


(* Need a subterm relation on type descriptions and a proof that no type
description can be a subterm of itself *)
Definition lowerOutputElem E stk T args
  (elem : tpElem E (cons T stk)
            (FunOutputDesc E (cons T stk) T (lift0FunInput args)))
  : tpElem E stk (FunOutputDesc E stk T args).
Proof.
  unfold lift0FunInput in elem; rewrite liftFunOutputEq in elem.
  destruct (FunOutputSubterm args) as [ subt | e ];
    [ | rewrite e in elem; destruct elem ].
  exact (lowerSubtermTpElem _ _ T 0 _ subt elem).
Defined.

(*
Definition applyFunInterp {E stk T} :
  FunInterp E stk T ->
  forall stk' (args:FunInput E (rev_app stk' stk) T),
    entree E (FunOutput E (rev_app stk' stk) T args).
Admitted.

(*
Fixpoint applyFunInterp {E stk T} :
  FunInterp E stk T ->
  forall stk' (args:FunInput E (rev_app stk' stk) T),
    entree E (FunOutput E (rev_app stk' stk) T args) :=
  match T return FunInterp E stk T ->
                 forall stk' (args:FunInput E (rev_app stk' stk) T),
                   entree E (FunOutput E (rev_app stk' stk) T args)
  with
  | Tp_M R => fun m stk' _ => fmap (liftTpElemMulti E stk stk' _) m
  | Tp_Pi A B =>
      fun f stk' args =>
        @applyFunInterp E stk (B (projT1 args)) (f (projT1 args)) stk' (projT2 args)
  | Tp_Arr A B =>
      fun f stk' args =>
        @applyFunInterp E stk B (f (fst args)) (snd args)
  | Tp_SType A => fun m _ => m
  | Tp_Pair A B => fun m _ => m
  | Tp_Sum A B => fun m _ => m
  | Tp_Sigma A B => fun m _ => m
  end.
*)

Definition lambdaFunInterp E stk T :
  (forall stk' (args:FunInput E (rev_app stk' stk) T),
      entree E (FunOutput E (rev_app stk' stk) T args)) -> FunInterp E stk T.
Admitted.

(*
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
*)
*)


(**
 ** Substitution of function interpretations for stack functions
 **)

(*
Definition substStkFun E stk U (I : FunInterp E (cons U stk) U)
  T (clos : StkFun (cons U stk) T) : StkFun stk T + FunInterp E (cons U stk) T :=
  match clos with
  | MkStkFun _ 0 _ => inr I
  | MkStkFun _ (S n) pf => inl (MkStkFun _ n (lt_S_n _ _ pf))
  end.

Definition substTpElem E stk U (I : FunInterp E (cons U stk) U) T :
  tpElem E (cons U stk) T -> tpElem E stk T.
Admitted.
*)

(*
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
*)

(*
Fixpoint liftFunInput E stk U (I : FunInterp E (cons U stk) U) T :
  FunInput E stk T -> FunInput E (cons U stk) T.
Admitted.

Fixpoint substFunOutput E stk U (I : FunInterp E (cons U stk) U) T :
  forall args:FunInput E stk T, FunOutput E stk T args ->
                                FunOutput E (cons U stk) T (liftFunInput E stk U I T args).
Admitted.
*)

(*
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
*)

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
      (body : forall stk' (args:FunInput E (rev_app stk' (cons T stk)) T),
          F (rev_app stk' (cons T stk))
            (FunOutput E (rev_app stk' (cons T stk)) T args))
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

Definition liftFixTree' {E stk R} T (ot : fixtree' E stk R) : fixtree E (cons T stk) R.
Admitted.

(* FIXME: need to insert a type at an arbitrary point in the stack, to handle fix bodies *)
(*
CoFixpoint liftFixTree' {E stk R} T (ot : fixtree' E stk R) : fixtree E (cons T stk) R :=
  match ot with
  | Fx_RetF r => Fx_Ret r
  | Fx_TauF t => Fx_Tau (liftFixTree' T (fxobserve t))
  | Fx_VisF e k => Fx_Vis e (fun x => liftFixTree' T (fxobserve (k x)))
  | Fx_CallF call k =>
      Fx_Call (liftStackCall E stk T call)
        (fun x => liftFixTree' T (fxobserve (k (unliftStackCallRet E stk T call x))))
  | Fx_FixF body args k => Fx_Fix body args (fun x => _subst (fxobserve (k x)))
  end.
*)


Definition FxInterp (E:EvType) stk (T : TpDesc) : Type@{entree_u} :=
  forall stk' (args: FunInput E (rev_app stk' stk) T),
    fixtree E (rev_app stk' stk) (FunOutput E (rev_app stk' stk) T args).

Definition default_FxInterp E stk : FxInterp E stk default_tp :=
  fun _ args => match projT1 args with end.

Definition liftFxInterp E stk U T (I: FxInterp E stk T) : FxInterp E (cons U stk) T :=
  fun stk' => I (cons U stk').

Definition FxInterps E stk : Type@{entree_u} :=
  mapTuple (FxInterp E stk) stk.

Definition consFxInterp E stk T (Is : FxInterps E stk)
  (I : FxInterp E (cons T stk) T) : FxInterps E (cons T stk) :=
  (I, mapMapTuple _ _ (liftFxInterp E stk T) _ Is).

Definition nthFxInterp E stk (defs : FxInterps E stk) n : FxInterp E stk (nthTp stk n) :=
  nthProjDefault (FxInterp E stk) default_tp (default_FxInterp E stk) stk n defs.

Definition doStackCall {E stk} (call : StackCall E stk)
  : FxInterps E stk -> fixtree E stk (StackCallRet E stk call).
Admitted.
(*
Definition doStackCall {E stk} (call : StackCall E stk)
  : FxInterps E stk -> fixtree E stk (StackCallRet E stk call) :=
  match call in StackCall _ stk
        return FxInterps E stk -> fixtree E stk (StackCallRet E stk call)
  with
    MkStackCall _ stk1 n pf args stk2 =>
      fun defs => nthFxInterp E _ defs n _ nil (liftFunInput E stk1 stk2 _ args)
  end.
*)


CoFixpoint interp_fixtree' {E stk R} (defs : FxInterps E stk) (ot : fixtree' E stk R)
  : entree E R :=
  match ot with
  | Fx_RetF r => Ret r
  | Fx_TauF t => Tau (interp_fixtree' defs (fxobserve t))
  | Fx_VisF e k => Vis e (fun x => interp_fixtree' defs (fxobserve (k x)))
  | Fx_CallF call k =>
      Tau (interp_fixtree' defs
             (fxobserve
                (FixTree.bind
                   (doStackCall call defs)
                   k)))
  | Fx_FixF body args k =>
      Tau (interp_fixtree'
             (consFxInterp E stk _ defs body)
             (fxobserve
                (FixTree.bind
                   (body nil (lift0FunInput args))
                   (fun x =>
                      liftFixTree' _ (fxobserve (k (lowerOutputElem _ _ _ _ x)))))))
  end.


FIXME: define a mkLambda function that calls interp_fixtree' to translate fixtrees in
the empty context into tpElems  


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
