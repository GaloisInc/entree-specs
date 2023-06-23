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


(* Examples of higher-order functions we want to write *)
Section HOExamples.

Context M `{Monad M}.

(* An inconsistent fix, used to write our examples with the least fuss *)
Variable fixM : forall {A B}, ((A -> M B) -> A -> M B) -> A -> M B.
Variable fixM2 : forall {A B C}, ((A -> B -> M C) -> A -> B -> M C) -> A -> B -> M C.

Definition incrStream (str : nat -> M nat) n : M nat :=
  bind (str n) (fun x => ret (x + 1)).

Definition foo : (nat -> M nat) -> nat -> M nat :=
  fixM2 (fun rec str n =>
          match n with
          | 0 => str 0
          | S n' => rec (rec (incrStream str)) n'
          end).

Definition fibMap : (nat -> M nat) -> nat -> M nat :=
  fixM2 (fun rec str n =>
           match n with
           | 0 => str 0
           | S 0 => bind (rec str 0) (fun x => ret (x + 1))
           | S (S n') =>
               bind (rec str n')
                 (fun x =>
                    bind (rec str (S n'))
                         (fun y => ret (x + y)))
           end).

End HOExamples.


(** Event types **)

(* An event type = a type of events plus their return types *)
Polymorphic Record EvType@{u} : Type :=
  { evTypeType :> Type@{u};
    evRetType : EncodingType evTypeType }.

Global Instance EncodingType_EvType (ET:EvType) : EncodingType ET :=
  evRetType ET.


(** Utilities for nat-indexed types, i.e., types indexed by "levels" **)

(* Apply a level-incrementing function to increment from level 0 *)
Fixpoint levelIncFrom0 (A : nat -> Type@{entree_u}) (incA : forall n, A n -> A (S n))
  n (a : A 0) : A n :=
  match n with
  | 0 => a
  | S n' => incA n' (levelIncFrom0 A incA n' a)
  end.

(* Apply a level-incrementing function multiple times, adding on the left *)
Fixpoint levelAddL (A : nat -> Type@{entree_u}) (incA : forall n, A n -> A (S n))
  n m (a : A m) : A (n + m) :=
  match n return A (n + m) with
  | 0 => a
  | S n' => incA (n' + m) (levelAddL A incA n' m a)
  end.

(* Apply a level-incrementing function multiple times, adding on the right *)
Fixpoint levelAddR n :
  forall (A : nat -> Type@{entree_u}) (incA : forall n, A n -> A (S n)) m,
    A n -> A (n + m) :=
  match n return forall A incA m, A n -> A (n + m) with
  | 0 => fun A incA m a => levelIncFrom0 A incA m a
  | S n' =>
      fun A incA m a =>
        levelAddR n' (fun lvl => A (S lvl)) (fun lvl => incA (S lvl)) m a
  end.

(* Lift the level m of a type to the level max n m with a new level n on the left *)
Fixpoint levelMaxL n m :
  forall (A : nat -> Type@{entree_u}) (incA : forall n, A n -> A (S n)),
    A m -> A (max n m) :=
  match n return forall A incA, A m -> A (max n m) with
  | 0 => fun _ _ a => a
  | S n' =>
      match m return forall A incA, A m -> A (max (S n') m) with
      | 0 => fun A incA a => levelIncFrom0 A incA (S n') a
      | S m' =>
          fun A incA a =>
            levelMaxL n' m' (fun lvl => A (S lvl)) (fun lvl => incA (S lvl)) a
      end
  end.

(* Lift the level n of a type to the level max n m with a new level m on the right *)
Fixpoint levelMaxR n m :
  forall (A : nat -> Type@{entree_u}) (incA : forall n, A n -> A (S n)),
    A n -> A (max n m) :=
  match n return forall A incA, A n -> A (max n m) with
  | 0 => fun A incA a => levelIncFrom0 A incA m a
  | S n' =>
      match m return forall A incA, A (S n') -> A (max (S n') m) with
      | 0 => fun _ _ a => a
      | S m' =>
          fun A incA a =>
            levelMaxR n' m' (fun lvl => A (S lvl)) (fun lvl => incA (S lvl)) a
      end
  end.

Lemma elimLevelIncFrom0 A incA n B (f : forall n, A n -> B) :
  (forall n a, f n a = f (S n) (incA n a)) ->
  forall a, f n (levelIncFrom0 A incA n a) = f 0 a.
Proof.
  intros; induction n.
  - reflexivity.
  - simpl. rewrite <- H. apply IHn.
Qed.

Lemma elimLevelMaxL n m A incA B (f : forall n, A n -> B) :
  (forall n a, f n a = f (S n) (incA n a)) ->
  forall a, f (max n m) (levelMaxL n m A incA a) = f m a.
Proof.
  revert m A incA B f; induction n; intros; [ | destruct m ].
  - reflexivity.
  - apply elimLevelIncFrom0. assumption.
  - apply (IHn m (fun lvl : nat => A (S lvl)) (fun lvl : nat => incA (S lvl))
             B (fun n => f (S n))).
    intros. apply H.
Qed.

Lemma elimLevelMaxR n m A incA B (f : forall n, A n -> B) :
  (forall n a, f n a = f (S n) (incA n a)) ->
  forall a, f (max n m) (levelMaxR n m A incA a) = f n a.
Proof.
  revert m A incA B f; induction n; intros; [ | destruct m ].
  - apply elimLevelIncFrom0. assumption.
  - reflexivity.
  - apply (IHn m (fun lvl : nat => A (S lvl)) (fun lvl : nat => incA (S lvl))
             B (fun n => f (S n))).
    intros. apply H.
Qed.

(* Lift the level of a type to a level that is at least as big *)
Program Definition levelLift A incA n m (l: n <= m) (a:A n) : A m :=
  eq_rect _ A (levelAddL A incA (m - n) n a) _ _.
Next Obligation.
  rewrite Nat.add_comm. apply le_plus_minus_r. assumption.
Defined.

(* Map a level-polymorphic function over an object at a given level *)
Definition levelMap A B (f : forall n:nat, A n -> B n) (a: { n & A n })
  : { n & B n } :=
  existT B (projT1 a) (f (projT1 a) (projT2 a)).

(* Apply a level-polymorphic function to combine to level objects, incrementing
their levels if necessary *)
Definition levelCombine (A B C : nat -> Type@{entree_u}) incA incB
  (f : forall n, A n -> B n -> C n) (a : { n & A n}) (b : { n & B n})
  : { n & C n } :=
  existT C
    (max (projT1 a) (projT1 b))
    (f (max (projT1 a) (projT1 b))
       (levelMaxR (projT1 a) (projT1 b) A incA (projT2 a))
       (levelMaxL (projT1 a) (projT1 b) B incB (projT2 b))).

(* Move a successor from the type functor to the level argument *)
Definition levelIncr (A : nat -> Type@{entree_u}) (a : { n & A (S n) })
  : { n & A n } :=
  existT A (S (projT1 a)) (projT2 a).

(* Ensure the level of an object is at least some given lvl by mapping the
object to the supremum of lvl and its current level *)
Definition levelSup A incA lvl (a : { n & A n }) : { n & A n } :=
  existT A (max (projT1 a) lvl)
    (levelMaxR (projT1 a) lvl A incA (projT2 a)).

(* An object whose level has been explicitly lifted to n *)
Inductive Lifted (A : nat -> Type@{entree_u}) lvl : Type@{entree_u} :=
| MkLifted lvl' (le : lvl' <= lvl) (a : A lvl').

Definition mkLifted (A : nat -> Type@{entree_u}) lvl (a:A lvl) : Lifted A lvl :=
  MkLifted A lvl lvl (le_n lvl) a.

(* Inject from { n & A n } into a lifted type *)
Definition injLifted (A : nat -> Type@{entree_u}) (a : { n & A n })
  : Lifted A (projT1 a) :=
  mkLifted A (projT1 a) (projT2 a).

(* Increment the level of a Lifted object *)
Definition incLifted A lvl (l: Lifted A lvl) : Lifted A (S lvl) :=
  match l with
  | MkLifted _ _ lvl' le a => MkLifted A (S lvl) lvl' (le_S lvl' lvl le) a
  end.

(* Lift the level of a Lifted object *)
Definition liftLifted A lvl lvl' (leq : lvl <= lvl') (l: Lifted A lvl)
  : Lifted A lvl' :=
  match l with
  | MkLifted _ _ lvl'' leq' a =>
      MkLifted A lvl' lvl'' (le_trans _ _ _ leq' leq) a
  end.

(* Map a Lifted object back to an object with a level *)
Definition elimLifted A lvl (l: Lifted A lvl) : { n & A n } :=
  match l with
  | MkLifted _ _ lvl' le a => existT A lvl' a
  end.

(* Incrementing the level of a Lifted does not change what it eliminates to *)
Definition elimIncLiftedEq A lvl l :
  elimLifted A (S lvl) (incLifted A lvl l) = elimLifted A lvl l :=
  match l return elimLifted A (S lvl) (incLifted A lvl l) = elimLifted A lvl l with
  | MkLifted _ _ lvl' le a => eq_refl (existT A lvl' a)
  end.

(* Make a Lifted with an existentially quantified level from an { n & A n } *)
Definition mkExLifted (A : nat -> Type@{entree_u}) (a : { n & A n })
  : { n & Lifted A n } :=
  existT (Lifted A) (projT1 a) (mkLifted A (projT1 a) (projT2 a)).

(* Combine two Lifted with existentially quantified levels *)
Definition exLiftedCombine A B C
  (f : forall n, Lifted A n -> Lifted B n -> C n)
  (a : { n & Lifted A n}) (b : { n & Lifted B n})
  : { n & C n } :=
  existT C
    (max (projT1 a) (projT1 b))
    (f (max (projT1 a) (projT1 b))
       (liftLifted A (projT1 a) (max (projT1 a) (projT1 b))
          (Nat.le_max_l (projT1 a) (projT1 b))
          (projT2 a))
       (liftLifted B (projT1 b) (max (projT1 a) (projT1 b))
          (Nat.le_max_r (projT1 a) (projT1 b))
          (projT2 b))).


(** Binary functors that preserve colimits **)

(* The class of binary functors that preserve countable colimits, i.e., such
that F A B is a colimit of countably many types whenever A and B are both
colimits of countably many types. Since the type { n & A n } is always a colimit
and colimits are unique up to isomorphism, this is equivalent to saying that F
of two types of this form is isomorphic to a type of this form. We call the
morphism to this colimit type "fmapMax2" because the first projection
intuitively gives the maximum level contained in the object. *)
Class ColimFunctor2 (F : Type@{entree_u} -> Type@{entree_u} -> Type@{entree_u}) :=
  { fmap2 : forall A1 A2 B1 B2, (A1 -> A2) -> (B1 -> B2) -> F A1 B1 -> F A2 B2;
    fmapMax2 : forall (A B : nat -> Type@{entree_u}),
      (forall n, A n -> A (S n)) -> (forall n, B n -> B (S n)) ->
      F ({ n:nat & A n}) ({ n:nat & B n}) ->
      { n & F (A n) (B n) };
    fmap2Proper : forall A1 A2 B1 B2,
      Proper ((eq ==> eq) ==> (eq ==> eq) ==> eq ==> eq) (fmap2 A1 A2 B1 B2);
    fmap2Id : forall A B fab, fmap2 A A B B (fun x => x) (fun x => x) fab = fab;
    fmap2Comp : forall A1 A2 A3 B1 B2 B3 f1 f2 g1 g2 fab,
      fmap2 A2 A3 B2 B3 f2 g2 (fmap2 A1 A2 B1 B2 f1 g1 fab) =
        fmap2 A1 A3 B1 B3 (fun x => f2 (f1 x)) (fun x => g2 (g1 x)) fab;
    fmapMax2Eq :
    forall A B C D incA incB (f: forall n, A n -> C) (g: forall n, B n -> D) fab,
      (forall n a, f n a = f (S n) (incA n a)) ->
      (forall n b, g n b = g (S n) (incB n b)) ->
      fmap2
        (A (projT1 (fmapMax2 A B incA incB fab))) C
        (B (projT1 (fmapMax2 A B incA incB fab))) D
        (f (projT1 (fmapMax2 A B incA incB fab)))
        (g (projT1 (fmapMax2 A B incA incB fab)))
        (projT2 (fmapMax2 A B incA incB fab))
      =
        fmap2 { n & A n } C { n & B n } D
          (fun a => f (projT1 a) (projT2 a))
          (fun b => g (projT1 b) (projT2 b))
          fab;
  }.

(* The constant functor preserves colimits *)
#[global] Program Instance Const_ColimFunctor2 T : ColimFunctor2 (fun _ _ => T) :=
  {|
    fmap2 := fun _ _ _ _ f g (t:T) => t;
    fmapMax2 := fun A B _ _ (t:T) => existT _ 0 t
  |}.
Next Obligation.
  repeat intro. assumption.
Defined.


(* The pair functor preserves colimits *) Print Nat.max.
#[global]
Program Instance Pair_ColimFunctor2 : ColimFunctor2 (fun A B => prod A B) :=
  {|
    fmap2 := fun _ _ _ _ f g p => (f (fst p), g (snd p));
    fmapMax2 :=
      fun A B incA incB p =>
        levelCombine _ _ _ incA incB (fun _ a b => (a, b)) (fst p) (snd p);
  |}.
Next Obligation.
  repeat intro. f_equal.
  - apply H; f_equal; assumption.
  - apply H0; f_equal; assumption.
Defined.
Next Obligation.
  simpl. f_equal; [ apply elimLevelMaxR | apply elimLevelMaxL ]; assumption.
Defined.

#[global]
Program Instance Compose_ColimFunctor2 F G H
  `{ColimFunctor2 F} `{ColimFunctor2 G} `{ColimFunctor2 H}
  : ColimFunctor2 (fun A B => F (G A B) (H A B)) :=
  {|
    fmap2 := fun A B C D f g (x:F (G A C) (H A C)) =>
                    fmap2 (G A C) (G B D) (H A C) (H B D)
                               (fmap2 A B C D f g)
                               (fmap2 A B C D f g) x;
    fmapMax2 :=
      fun A B incA incB x =>
        fmapMax2
          (F:=F)
          (fun n => G (A n) (B n))
          (fun n => H (A n) (B n))
          (fun n => fmap2 (A n) (A (S n)) (B n) (B (S n)) (incA n) (incB n))
          (fun n => fmap2 (A n) (A (S n)) (B n) (B (S n)) (incA n) (incB n))
          (fmap2
             (F:=F)
             (G { n & A n} { n & B n}) { n & G (A n) (B n) }
             (H { n & A n} { n & B n}) { n & H (A n) (B n) }
             (fmapMax2 A B incA incB)
             (fmapMax2 A B incA incB)
             x)
  |}.
Next Obligation.
  repeat intro.
  apply fmap2Proper; [ apply fmap2Proper | apply fmap2Proper | ]; assumption.
Defined.
Next Obligation.
  etransitivity; [ | apply fmap2Id ].
  apply fmap2Proper; [ | | reflexivity ];
    repeat intro; subst x; apply fmap2Id.
Defined.
Next Obligation.
  repeat rewrite fmap2Comp.
  apply fmap2Proper; [ | | reflexivity ];
    repeat intro; subst x; apply fmap2Comp.
Defined.
Next Obligation.
  etransitivity;
    [ apply
        (fmapMax2Eq (F:=F) _ _ _ _
           (fun n => fmap2 (F:=G) (A n) (A (S n)) (B n) (B (S n)) (incA n) (incB n))
           (fun n => fmap2 (F:=H) (A n) (A (S n)) (B n) (B (S n)) (incA n) (incB n))
           (fun n => fmap2 (F:=G) (A n) C (B n) D (f n) (g n))
           (fun n => fmap2 (F:=H) (A n) C (B n) D (f n) (g n)))
    | ].
  - intros. rewrite fmap2Comp.
    apply fmap2Proper; [ | | reflexivity ];
      repeat intro; subst x; [ apply H3 | apply H4 ].
  - intros. rewrite fmap2Comp.
    apply fmap2Proper; [ | | reflexivity ];
      repeat intro; subst x; [ apply H3 | apply H4 ].
  - rewrite fmap2Comp.
    apply fmap2Proper; [ | | reflexivity ];
      repeat intro; subst x; apply fmapMax2Eq; assumption.
Defined.


(** An inductive description of recursive function types and their arguments **)

(* An encoded argument type for a recursive function and its arguments *)
Inductive LetRecType : Type@{entree_u + 1} :=
(* These three constructors represent functions of 0 or more arguments *)
| LRT_SpecM (R : LetRecType) : LetRecType
| LRT_FunDep (A : Type@{entree_u}) (rest : A -> LetRecType) : LetRecType
| LRT_FunClos (A : LetRecType) (rest : LetRecType) : LetRecType
(* These constructors represent the argument types used in functions *)
| LRT_Unit : LetRecType
| LRT_BinOp F `{ColimFunctor2 F} (A B : LetRecType) : LetRecType
| LRT_Sigma (A : Type@{entree_u}) (B : A -> LetRecType) : LetRecType
.

(* The LetRecType that decodes to a specific type *)
Definition LRT_Type (A : Type@{entree_u}) : LetRecType :=
  LRT_BinOp (fun _ _ => A) LRT_Unit LRT_Unit.

(* A FunStack is a list of LetRecTypes representing all of the functions bound
   by multiFixS that are currently in scope *)
Definition FunStack := plist LetRecType.

(* A trivially inhabited "default" LetRecType *)
Definition default_lrt : LetRecType :=
  LRT_FunDep void (fun _ => LRT_SpecM (LRT_Type void)).

(* Get the nth element of a FunStack list, or void -> void if n is too big *)
Definition nthLRT (stk : FunStack) n : LetRecType :=
  nth_default' default_lrt stk n.

(* An argument to a recursive function call, which is a decoding of a LetRecType
to its corresponding Coq type except that functions are interpreted using the
supplied type functor *)
Fixpoint LRTArgF (Clos : LetRecType -> Type@{entree_u}) (argTp : LetRecType)
  : Type@{entree_u} :=
  match argTp with
  | LRT_SpecM R => Clos (LRT_SpecM R)
  | LRT_FunDep A B => Clos (LRT_FunDep A B)
  | LRT_FunClos A B => Clos (LRT_FunClos A B)
  | LRT_Unit => unit
  | LRT_BinOp F A B => F (LRTArgF Clos A) (LRTArgF Clos B)
  | LRT_Sigma A B => { x:A & LRTArgF Clos (B x) }
  end.

Fixpoint LRTDepArgs n lrt : Type@{entree_u} :=
  match n with
  | 0 => unit
  | S n' =>
      match lrt with
      | LRT_SpecM R => void
      | LRT_FunDep A B => { a:A & LRTDepArgs n' (B a) }
      | LRT_FunClos A B => LRTDepArgs n' B
      | LRT_Unit => void
      | LRT_BinOp F A B => void
      | LRT_Sigma A B => void
      end
  end.

Fixpoint LRTClosArgsF Clos n lrt : LRTDepArgs n lrt -> Type@{entree_u} :=
  match n with
  | 0 => fun _ => unit
  | S n' =>
      match lrt return LRTDepArgs (S n') lrt -> Type with
      | LRT_SpecM R => fun bot => match bot with end
      | LRT_FunDep A B =>
          fun args => LRTClosArgsF Clos n' (B (projT1 args)) (projT2 args)
      | LRT_FunClos A B =>
          fun args => prod (LRTArgF Clos A) (LRTClosArgsF Clos n' B args)
      | LRT_Unit => fun bot => match bot with end
      | LRT_BinOp F A B => fun bot => match bot with end
      | LRT_Sigma A B => fun bot => match bot with end
      end
  end.

Fixpoint LRTDepArgsOut n lrt : LRTDepArgs n lrt -> LetRecType :=
  match n with
  | 0 => fun _ => lrt
  | S n' =>
      match lrt return LRTDepArgs (S n') lrt -> LetRecType with
      | LRT_SpecM R => fun bot => match bot with end
      | LRT_FunDep A B =>
          fun args => LRTDepArgsOut n' (B (projT1 args)) (projT2 args)
      | LRT_FunClos A B =>
          fun args => LRTDepArgsOut n' B args
      | LRT_Unit => fun bot => match bot with end
      | LRT_BinOp F A B => fun bot => match bot with end
      | LRT_Sigma A B => fun bot => match bot with end
      end
  end.

Definition LRTArgsF Clos n lrt : Type@{entree_u} :=
  { dep_args:LRTDepArgs n lrt & LRTClosArgsF Clos n lrt dep_args }.

Definition LRTArgsFOut Clos n lrt : LRTArgsF Clos n lrt -> LetRecType :=
  fun args => LRTDepArgsOut n lrt (projT1 args).


(* A "closure type" is a type of a closure plus a map to the LetRecType of a
closure of that type *)
Definition ClosType := { T : Type@{entree_u} & T -> LetRecType }.

(* A closure of a LetRecType for a given ClosType *)
Definition ClosOfType (CT : ClosType) lrt : Type@{entree_u} :=
  { clos:projT1 CT & projT2 CT clos = lrt }.

Record LRTClosF (CT : ClosType) : Type@{entree_u} :=
  { lrtClosClos : projT1 CT;
    lrtClosNumArgs : nat;
    lrtClosDepArgs  : LRTDepArgs lrtClosNumArgs (projT2 CT lrtClosClos);
    lrtClosArgs : LRTClosArgsF (ClosOfType CT) lrtClosNumArgs
                    (projT2 CT lrtClosClos) lrtClosDepArgs }.

Definition LRTClosFType CT (clos : LRTClosF CT) : LetRecType :=
  LRTDepArgsOut
    (lrtClosNumArgs CT clos)
    (projT2 CT (lrtClosClos CT clos))
    (lrtClosDepArgs CT clos).

Fixpoint LRTClosAndRet stk lvl : ClosType :=
  match lvl with
  | 0 => existT (fun T => T -> LetRecType) nat (nthLRT stk)
  | S lvl' =>
      existT
        (fun T => T -> LetRecType)
        (LRTClosF (LRTClosAndRet stk lvl'))
        (LRTClosFType (LRTClosAndRet stk lvl'))
  end.

Definition LRTClosLvl stk lrt lvl : Type@{entree_u} :=
  ClosOfType (LRTClosAndRet stk lvl) lrt.

Definition LRTClosLvlIncr stk lrt lvl (clos:LRTClosLvl stk lrt lvl)
  : LRTClosLvl stk lrt (S lvl) :=
  existT
    _
    (Build_LRTClosF (LRTClosAndRet stk lvl) (projT1 clos) 0 tt tt)
    (projT2 clos).

Definition LRTClosLvlLift stk lrt lvl1 lvl2 (l:lvl1 <= lvl2)
  : LRTClosLvl stk lrt lvl1 -> LRTClosLvl stk lrt lvl2 :=
  levelLift (LRTClosLvl stk lrt) (LRTClosLvlIncr stk lrt) lvl1 lvl2 l.

Definition LRTArgLvl stk argTp lvl :=
  LRTArgF (fun lrt => LRTClosLvl stk lrt lvl) argTp.

Fixpoint LRTArgLvlIncr stk argTp lvl :
  LRTArgLvl stk argTp lvl -> LRTArgLvl stk argTp (S lvl) :=
  match argTp return LRTArgLvl stk argTp lvl -> LRTArgLvl stk argTp (S lvl) with
  | LRT_SpecM R => LRTClosLvlIncr stk (LRT_SpecM R) lvl
  | LRT_FunDep A B => LRTClosLvlIncr stk (LRT_FunDep A B) lvl
  | LRT_FunClos A B => LRTClosLvlIncr stk (LRT_FunClos A B) lvl
  | LRT_Unit => fun u => u
  | LRT_BinOp F A B =>
      fmap2 _ _ _ _ (LRTArgLvlIncr stk A lvl) (LRTArgLvlIncr stk B lvl)
  | LRT_Sigma A B =>
      fun p => existT _ (projT1 p) (LRTArgLvlIncr stk (B (projT1 p)) lvl (projT2 p))
  end.

Definition LRTArgLvlLift stk argTp lvl1 lvl2 (l: lvl1 <= lvl2)
  : LRTArgLvl stk argTp lvl1 -> LRTArgLvl stk argTp lvl2 :=
  levelLift (LRTArgLvl stk argTp) (LRTArgLvlIncr stk argTp) lvl1 lvl2 l.

Definition LRTClosArgsLvl stk n lrt lvl dargs :=
  LRTClosArgsF (fun lrt => LRTClosLvl stk lrt lvl) n lrt dargs.

Fixpoint LRTClosArgsLvlIncr stk n lrt lvl :
  forall dargs, LRTClosArgsLvl stk n lrt lvl dargs ->
                LRTClosArgsLvl stk n lrt (S lvl) dargs :=
  match n return forall dargs, LRTClosArgsLvl stk n lrt lvl dargs ->
                               LRTClosArgsLvl stk n lrt (S lvl) dargs with
  | 0 => fun _ u => u
  | S n' =>
      match lrt return forall dargs, LRTClosArgsLvl stk (S n') lrt lvl dargs ->
                                     LRTClosArgsLvl stk (S n') lrt (S lvl) dargs with
      | LRT_SpecM R => fun bot => match bot with end
      | LRT_FunDep A B =>
          fun dargs cargs =>
            LRTClosArgsLvlIncr stk n' (B (projT1 dargs)) lvl (projT2 dargs) cargs
      | LRT_FunClos A B =>
          fun dargs cargs => (LRTArgLvlIncr stk A lvl (fst cargs),
                               LRTClosArgsLvlIncr stk n' B lvl dargs (snd cargs))
      | LRT_Unit => fun bot => match bot with end
      | LRT_BinOp F A B => fun bot => match bot with end
      | LRT_Sigma A B => fun bot => match bot with end
      end
  end.

Definition LRTClosArgsLvlLift stk n lrt lvl1 lvl2 (l: lvl1 <= lvl2) dargs
  : LRTClosArgsLvl stk n lrt lvl1 dargs -> LRTClosArgsLvl stk n lrt lvl2 dargs :=
  levelLift (fun lvl => LRTClosArgsLvl stk n lrt lvl dargs)
    (fun lvl => LRTClosArgsLvlIncr stk n lrt lvl dargs) lvl1 lvl2 l.


Definition LRTClos stk lrt : Type@{entree_u} :=
  { lvl & LRTClosLvl stk lrt lvl }.

Definition LRTArg stk argTp : Type@{entree_u} := LRTArgF (LRTClos stk) argTp.

Fixpoint LRTArgMax stk argTp
  : LRTArg stk argTp -> { lvl & LRTArgLvl stk argTp lvl } :=
  match argTp return LRTArg stk argTp -> { lvl & LRTArgLvl stk argTp lvl } with
  | LRT_SpecM R => fun clos => clos
  | LRT_FunDep A B => fun clos => clos
  | LRT_FunClos A B => fun clos => clos
  | LRT_Unit => fun u => existT _ 0 u
  | LRT_BinOp F A B =>
      fun x =>
        fmapMax2 (LRTArgLvl stk A) (LRTArgLvl stk B)
          (LRTArgLvlIncr stk A) (LRTArgLvlIncr stk B)
          (fmap2 _ _ _ _ (LRTArgMax stk A) (LRTArgMax stk B) x)
  | LRT_Sigma A B =>
      fun p =>
        existT _ (projT1 (LRTArgMax stk (B (projT1 p)) (projT2 p)))
          (existT _ (projT1 p) (projT2 (LRTArgMax stk (B (projT1 p)) (projT2 p))))
  end.

Definition LRTClosArgs stk n lrt dargs : Type@{entree_u} :=
  LRTClosArgsF (LRTClos stk) n lrt dargs.

Fixpoint LRTClosArgsMax stk n lrt :
  forall dargs, LRTClosArgs stk n lrt dargs ->
                { lvl & LRTClosArgsLvl stk n lrt lvl dargs } :=
  match n return forall dargs, LRTClosArgs stk n lrt dargs ->
                               { lvl & LRTClosArgsLvl stk n lrt lvl dargs } with
  | 0 => fun _ u => existT _ 0 u
  | S n' =>
      match lrt
            return forall dargs, LRTClosArgs stk (S n') lrt dargs ->
                                 { lvl & LRTClosArgsLvl stk (S n') lrt lvl dargs }
      with
      | LRT_SpecM R => fun bot => match bot with end
      | LRT_FunDep A B =>
          fun dargs cargs =>
            LRTClosArgsMax stk n' (B (projT1 dargs)) (projT2 dargs) cargs
      | LRT_FunClos A B =>
          fun dargs cargs =>
            levelCombine
              (LRTArgLvl stk A)
              (fun lvl => LRTClosArgsLvl stk n' B lvl dargs)
              (fun lvl => LRTClosArgsLvl stk (S n') (LRT_FunClos A B) lvl dargs)
              (LRTArgLvlIncr stk A)
              (fun lvl => LRTClosArgsLvlIncr stk n' B lvl dargs)
              (fun n a b => (a, b))
              (LRTArgMax stk A (fst cargs))
              (LRTClosArgsMax stk n' B dargs (snd cargs))
      | LRT_Unit => fun bot => match bot with end
      | LRT_BinOp F A B => fun bot => match bot with end
      | LRT_Sigma A B => fun bot => match bot with end
      end
  end.

Definition LRTArgs stk n lrt : Type@{entree_u} :=
  LRTArgsF (LRTClos stk) n lrt.

Definition LRTArgsOut stk n lrt : LRTArgs stk n lrt -> LetRecType :=
  LRTArgsFOut (LRTClos stk) n lrt.

Definition applyLRTClosF (CT:ClosType) lrt (clos: ClosOfType CT lrt) n :
  forall dargs, LRTClosArgsF (ClosOfType CT) n lrt dargs ->
                { clos' : LRTClosF CT &
                            LRTClosFType CT clos' = LRTDepArgsOut n lrt dargs } :=
  eq_rect (projT2 CT (projT1 clos))
    (fun lrt' => forall dargs,
         LRTClosArgsF (ClosOfType CT) n lrt' dargs ->
         { clos' : LRTClosF CT &
                     LRTClosFType CT clos' = LRTDepArgsOut n lrt' dargs })
    (fun dargs cargs =>
       existT _ (Build_LRTClosF CT (projT1 clos) n dargs cargs) (eq_refl _))
    lrt (projT2 clos).

Program Definition applyLRTClosArgsLvl stk lrt n lvl (clos: LRTClosLvl stk lrt lvl)
  (dargs: LRTDepArgs n lrt) (cargs: LRTClosArgsLvl stk n lrt lvl dargs)
  : LRTClosLvl stk (LRTDepArgsOut n lrt dargs) (S lvl) :=
  applyLRTClosF (LRTClosAndRet stk lvl) lrt clos n dargs cargs.

Definition applyLRTClosArgs stk lrt n (clos: LRTClos stk lrt)
  (dargs: LRTDepArgs n lrt) (cargs: LRTClosArgs stk n lrt dargs)
  : LRTClos stk (LRTDepArgsOut n lrt dargs) :=
  levelIncr (LRTClosLvl stk (LRTDepArgsOut n lrt dargs))
    (levelCombine
       (LRTClosLvl stk lrt)
       (fun lvl => LRTClosArgsLvl stk n lrt lvl dargs)
       (fun lvl => LRTClosLvl stk (LRTDepArgsOut n lrt dargs) (S lvl))
       (LRTClosLvlIncr stk lrt)
       (fun lvl => LRTClosArgsLvlIncr stk n lrt lvl dargs)
       (fun lvl clos' cargs' => applyLRTClosArgsLvl stk lrt n lvl clos' dargs cargs')
       clos
       (LRTClosArgsMax stk n lrt dargs cargs)).


(* A dependent tuple type of all the inputs of a LetRecType, i.e., return the
   type { x:A & { y:B & ... { z:C & unit } ...}} from a LetRecType that
   represents forall a b c..., SpecM ... (R a b c ...). A LetRectype that is not
   a function type just becomes the void type. *)
Fixpoint LRTInput stack lrt : Type@{entree_u} :=
  match lrt with
  | LRT_SpecM _ => unit
  | LRT_FunDep A rest => {a : A & LRTInput stack (rest a) }
  | LRT_FunClos A rest => LRTArg stack A * LRTInput stack rest
  | _ => void
  end.

(* The output type (R a b c ...) of a LetRecType that represents the function
   type forall a b c..., SpecM ... (R a b c ...) given a dependent tuple of
   arguments to a function of that type *)
Fixpoint LRTOutput stack lrt : EncodingType (LRTInput stack lrt) :=
  match lrt with
  | LRT_SpecM R => fun _ => LRTArg stack R
  | LRT_FunDep A rest => fun args =>
                           let '(existT _ a args') := args in
                           LRTOutput stack (rest a) args'
  | LRT_FunClos A rest => fun args => LRTOutput stack rest (snd args)
  | _ => fun args => match args with end
  end.

(* Build the type forall a b c ..., F (a, (b, (c, ...))) for an arbitrary type
   function F over an LRTInput. A LetRecType that is not a function type turns
   into a function from v:void to F v *)
Fixpoint lrtPi stack lrt : (LRTInput stack lrt -> Type) -> Type :=
  match lrt return (LRTInput stack lrt -> Type) -> Type with
  | LRT_SpecM _ => fun F => F tt
  | LRT_FunDep A lrtF =>
      fun F => forall a, lrtPi stack (lrtF a) (fun args => F (existT _ a args))
  | LRT_FunClos A lrt' =>
      fun F => forall a, lrtPi stack lrt' (fun args => F (a, args))
  | _ => fun F => forall v:void, F v
  end.

(* Build an lrtPi function from a unary function on an LRTInput *)
Fixpoint lrtLambda stack lrt
  : forall (F : LRTInput stack lrt -> Type),
    (forall args, F args) -> lrtPi stack lrt F :=
  match lrt return
        forall (F : LRTInput stack lrt -> Type),
          (forall args, F args) -> lrtPi stack lrt F
  with
  | LRT_SpecM _ => fun _ f => f tt
  | LRT_FunDep A lrtF =>
    fun F f a => lrtLambda stack (lrtF a)
                   (fun args => F (existT _ a args))
                   (fun args => f (existT _ a args))
  | LRT_FunClos A lrt' =>
      fun F f a => lrtLambda stack lrt'
                     (fun args => F (a, args))
                     (fun args => f (a, args))
  | _ => fun _ _ v => match v with end
  end.

(* Apply an lrtPi function *)
Fixpoint lrtApply stack lrt
  : forall F, lrtPi stack lrt F -> forall args, F args :=
  match lrt return forall F, lrtPi stack lrt F -> forall args, F args with
  | LRT_SpecM _ =>
    fun F f u => match u return F u with | tt => f end
  | LRT_FunDep A lrtF =>
    fun F f args =>
      match args return F args with
      | existT _ arg args' =>
        lrtApply stack (lrtF arg) (fun args' => F (existT _ arg args')) (f arg) args'
      end
  | LRT_FunClos A lrt' =>
    fun F f args =>
      match args return F args with
      | (arg, args') =>
        lrtApply stack lrt' (fun args' => F (arg, args')) (f arg) args'
      end
  | _ =>
      fun _ _ v => match v with end
  end.

(* A recursive call to one of the functions in a FunStack, specified by a
natural number n that picks a specific index in the FunStack along with a set of
arguments for that recursive call, relative to a given stack *)
Inductive StackCall stack : Type@{entree_u} :=
| StackCallOfArgs n (args : LRTInput stack (nthLRT stack n)).

(* The return type for a StackCall recursive call, using a specific M *)
Definition StackCallRet stack (args: StackCall stack) : Type@{entree_u} :=
  match args with
  | StackCallOfArgs _ n args => LRTOutput stack (nthLRT stack n) args
  end.

Global Instance EncodingType_StackCall stack : EncodingType (StackCall stack) :=
  StackCallRet stack.

(* The error event type *)
Inductive ErrorE : Set :=
| mkErrorE : string -> ErrorE.

Global Instance EncodingType_ErrorE : EncodingType ErrorE := fun _ => void.

(* Create an event type for either an event in E or a recursive call in a stack
   Γ of recursive functions in scope *)
Definition FunStackE (E : EvType@{entree_u}) (stack : FunStack) : Type@{entree_u} :=
  StackCall stack + (ErrorE + E).

(* The return type for a FunStackE effect in a SpecM computation *)
Definition FunStackERet E stack (e:FunStackE E stack) : Type@{entree_u} :=
  encodes e.

Global Instance EncodingType_FunStackE E stack : EncodingType (FunStackE E stack) :=
  FunStackERet E stack.

Global Instance ReSum_FunStackE_E (E : EvType) (Γ : FunStack) : ReSum E (FunStackE E Γ) :=
  fun e => inr (inr e).

Global Instance ReSumRet_FunStackE_E (E : EvType) Γ :
  ReSumRet E (FunStackE E Γ) :=
  fun _ r => r.

Global Instance ReSum_FunStackE_Error (E : EvType) (Γ : FunStack) : ReSum ErrorE (FunStackE E Γ) :=
  fun e => inr (inl e).

Global Instance ReSumRet_FunStackE_Error (E : EvType) Γ :
  ReSumRet ErrorE (FunStackE E Γ) :=
  fun _ r => r.


(* Embed a call in the top level of the FunStack into a FunStackE *)
Global Instance ReSum_StackCall_FunStackE (E : EvType) (stack : FunStack) :
  ReSum (StackCall stack) (FunStackE E stack) :=
  fun args => inl args.

(* Map the return value for embedding a call in the top level to a FunStackE *)
Global Instance ReSumRet_StackCall_FunStackE E stack :
  ReSumRet (StackCall stack) (FunStackE E stack) :=
  fun _ r => r.

Global Instance EncodingType_LRTInput stack lrt :
  EncodingType (LRTInput stack lrt) := LRTOutput stack lrt.

(* ReSum instances for embedding the nth LRTInput into a StackCall *)
Global Instance ReSum_LRTInput_FunStackE E stack n :
  ReSum (LRTInput stack (nthLRT stack n)) (FunStackE E stack) :=
  fun args => resum (StackCallOfArgs stack n args).

Global Instance ReSumRet_LRTInput_FunStackE E stack n :
  ReSumRet (LRTInput stack (nthLRT stack n)) (FunStackE E stack) :=
  fun _ r => r.

Global Instance ReSum_Error_E_FunStack (E : EvType) (stack : FunStack) :
  ReSum (SpecEvent (ErrorE + E)) (SpecEvent (FunStackE E stack)) :=
  fun e => match e with
           | Spec_vis e => Spec_vis (resum e)
           | Spec_forall T => Spec_forall T
           | Spec_exists T => Spec_exists T
           end.

Global Instance ReSumRet_Error_E_FunStack (E : EvType) (stack : FunStack) :
  ReSumRet (SpecEvent (ErrorE + E)) (SpecEvent (FunStackE E stack)) :=
  fun e =>
    match e with
    | Spec_vis e => fun x => resum_ret e x
    | Spec_forall T => fun x => x
    | Spec_exists T => fun x => x
    end.


(** Defining the SpecM monad **)

(* The SpecM monad is an entree spec over FunStackE events *)
Definition SpecM (E:EvType) stack A : Type :=
  entree_spec (FunStackE E stack) A.

(* The observation / unfolding of a SpecM computation tree *)
Definition SpecM' (E:EvType) stack A : Type :=
  entree_spec' (FunStackE E stack) A.

(* The monadic operations on SpecM *)
Definition RetS {E} {Γ A} (a : A) : SpecM E Γ A := ret a.
Definition BindS {E} {Γ A B} (m : SpecM E Γ A) (k : A -> SpecM E Γ B) :=
  bind m k.
Definition IterS {E} {Γ A B} (body : A -> SpecM E Γ (A + B)) :
  A -> SpecM E Γ B := EnTree.iter body.
Definition AssumeS {E} {Γ} (P : Prop) : SpecM E Γ unit :=
  assume_spec P.
Definition AssertS {E} {Γ} (P : Prop) : SpecM E Γ unit :=
  assert_spec P.
Definition ForallS {E} {Γ} (A : Type) `{QuantType A} : SpecM E Γ A :=
  forall_spec A.
Definition ExistsS {E} {Γ} (A : Type) `{QuantType A} : SpecM E Γ A :=
  exists_spec A.
Definition TriggerS {E:EvType} {Γ} (e : E) : SpecM E Γ (encodes e) := trigger e.
Definition ErrorS {E} {Γ} A (str : string) : SpecM E Γ A :=
  bind (trigger (mkErrorE str)) (fun (x:void) => match x with end).

Global Instance SpecM_Monad {E} Γ : Monad (SpecM E Γ) :=
  {|
    ret := fun A a => RetS a;
    bind := fun A B m k => BindS m k;
  |}.

(* Helper for applyDepApp *)
Definition castCallFun E stack lrt1 lrt2 (e : lrt1 = lrt2)
  (f: forall args:LRTInput stack lrt1, SpecM E stack (LRTOutput _ _ args))
  : (forall args:LRTInput stack lrt2, SpecM E stack (LRTOutput _ _ args)) :=
  eq_rect lrt1
    (fun lrt => forall args:LRTInput stack lrt, SpecM E stack (LRTOutput _ _ args))
    f lrt2 e.

(* Apply an LRTDepApp to its remaining arguments *)
Fixpoint applyDepApp E stack lrt_in lrt_out :
  (forall args:LRTInput stack lrt_in, SpecM E stack (LRTOutput _ _ args)) ->
  LRTDepApp lrt_in lrt_out ->
  forall args:LRTInput stack lrt_out, SpecM E stack (LRTOutput stack lrt_out args) :=
  match lrt_in return
        (forall args:LRTInput stack lrt_in, SpecM E stack (LRTOutput _ _ args)) ->
        LRTDepApp lrt_in lrt_out ->
        forall args:LRTInput stack lrt_out,
          SpecM E stack (LRTOutput stack lrt_out args)
  with
  | LRT_FunDep A lrtF =>
      fun f da args =>
        match da with
        | inl e => (castCallFun E stack _ lrt_out e f) args
        | inr da' =>
            applyDepApp E stack (lrtF (projT1 da')) lrt_out
                        (fun args' => f (existT _ (projT1 da') args'))
                        (projT2 da') args
        end
  | _ =>
      fun f e args => (castCallFun E stack _ lrt_out e f) args
  end.

(* Apply an LRTArg of monadic type *)
Definition CallLRTArg E stack lrt :
  LRTArg stack lrt ->
  lrtPi stack lrt (fun args => SpecM E stack (LRTOutput stack lrt args)) :=
  match lrt return LRTArg stack lrt ->
                   lrtPi stack lrt (fun args =>
                                      SpecM E stack (LRTOutput stack lrt args))
  with
  | LRT_SpecM R =>
      fun arg =>
        lrtLambda stack (LRT_SpecM R) _
          (fun args =>
             applyDepApp E stack _ _
               (trigger (H2:=@SpecEventReSumRet _ _ _ _ _ _))
               (projT2 arg) args)
  | LRT_FunDep A B =>
      fun arg =>
        lrtLambda stack (LRT_FunDep A B) _
          (fun args =>
             applyDepApp E stack _ _
               (trigger (H2:=@SpecEventReSumRet _ _ _ _ _ _))
               (projT2 arg) args)
  | LRT_FunClos A B =>
      fun arg =>
        lrtLambda stack (LRT_FunClos A B) _
          (fun args =>
             applyDepApp E stack _ _
               (trigger (H2:=@SpecEventReSumRet _ _ _ _ _ _))
               (projT2 arg) args)
  | LRT_Unit =>
      fun arg =>
        lrtLambda stack LRT_Unit _ (fun v => match v with end)
  | LRT_BinOp F A B =>
      fun arg =>
        lrtLambda stack (LRT_BinOp F A B) _ (fun v => match v with end)
  | LRT_Sigma A B =>
      fun arg =>
        lrtLambda stack (LRT_Sigma A B) _ (fun v => match v with end)
  end.


(** Defining MultiFixS **)

(* A monadic function whose type is described by the encoding lrt *)
Definition SpecFun E stack lrt : Type@{entree_u} :=
  lrtPi stack lrt (fun args => SpecM E stack (LRTOutput _ lrt args)).

(* A trivially inhabited "default" SpecFun of type default_lrt *)
Definition defaultSpecFun E stack : SpecFun E stack default_lrt :=
  fun (v:void) => match v with end.

(* A dependent pair of an LRT and a SpecFun with that LRT *)
Definition SpecFunSig E stack : Type@{entree_u+1} :=
  { lrt:LetRecType & SpecFun E stack lrt }.

(* The dependent pair of the default SpecFun and its LRT *)
Definition defaultSpecFunSig E stack : SpecFunSig E stack :=
  existT _ default_lrt (defaultSpecFun E stack).

(* A right-nested tuple of a list of function definitions for all the
LetRecTypes in the defs list, that can make calls into the calls list *)
Definition StackTuple E calls defs : Type@{entree_u} :=
  mapTuple (SpecFun E calls) defs.

(* The StackTuple of 0 functions *)
Definition emptyStackTuple E calls : StackTuple E calls pnil := tt.

(* Get the nth function in a StackTuple *)
Definition nthStackTupleFun E calls defs n (funs : StackTuple E calls defs) :
  SpecFun E calls (nthLRT defs n) :=
  nthProjDefault (SpecFun E calls) default_lrt
    (defaultSpecFun E calls) _ n funs.

(* Apply a StackTuple to a StackCall to get a StackCallRet *)
Definition applyStackTuple E stack (funs : StackTuple E stack stack)
           (call : StackCall stack) : SpecM E stack (StackCallRet stack call) :=
  match call return SpecM E stack (StackCallRet stack call) with
  | StackCallOfArgs _ n args =>
    lrtApply stack (nthLRT stack n) _ (nthStackTupleFun _ stack stack n funs) args
  end.

(* Create a multi-way letrec that binds 0 or more co-recursive functions *)
Definition LetRecS E R stack (funs : StackTuple E stack stack) (body : SpecM E stack R)
  : SpecM E pnil R :=
  resumEntree (interp_mrec_spec (applyStackTuple E stack funs) body).


(** Stack Inclusions **)

(* A stack inclusion is a mapping from the indices of one stack to those of
another that preserves LetRecTypes. Note that this is not technically a relation
because the mapping itself matters. *)
Definition stackIncl (stk1 stk2 : FunStack) : Type :=
  { f : nat -> nat |
    forall n, n < plength stk1 ->
              nthLRT stk1 n = nthLRT stk2 (f n) /\ f n < plength stk2 }.

(* Apply a stackIncl, mapping anything outside of the domain to outside of the
codomain *)
Definition applyIncl {stk1 stk2} (incl : stackIncl stk1 stk2) n :=
  match Compare_dec.lt_dec n (plength stk1) with
  | left _ => proj1_sig incl n
  | right _ => plength stk2
  end.

(* applyIncl preserves nthLRT *)
Lemma applyInclEq {stk1 stk2} incl n :
  nthLRT stk2 (@applyIncl stk1 stk2 incl n) = nthLRT stk1 n.
Proof.
  unfold applyIncl. destruct (Compare_dec.lt_dec n (plength stk1)).
  - symmetry. apply (proj2_sig incl n). assumption.
  - unfold nthLRT. repeat rewrite nth_default'_default.
    + reflexivity.
    + destruct (Compare_dec.le_lt_dec (plength stk1) n); [ assumption | ].
      elimtype False; apply n0; assumption.
    + reflexivity.
Qed.

(* The trivial stack inclusion from the empty stack *)
Program Definition nilStackIncl stk : stackIncl pnil stk :=
  fun n => n.
Next Obligation.
  inversion H.
Defined.

(* The trivially reflexive stack inclusion *)
Program Definition reflStackIncl stk : stackIncl stk stk :=
  fun n => n.

(* A trivially reflexive stack inclusion that uses an equality on stacks *)
Program Definition eqReflStackIncl stk1 stk2 (e:stk1 = stk2) : stackIncl stk1 stk2 :=
  fun n => n.

(* The trivially reflexive stack inclusion, that appends nil on the left *)
Program Definition pappNilStackIncl stk : stackIncl (papp stk pnil) stk :=
  eqReflStackIncl _ _ (papp_nil _).

(* Apply the associativity of pmap_assoc in a stack inclusion *)
Program Definition pappAssocStackIncl stk1 stk2 stk3 :
  stackIncl (papp (papp stk1 stk2) stk3) (papp stk1 (papp stk2 stk3)) :=
  eqReflStackIncl _ _ (papp_assoc _ _ _).

(* Invert the associativity of pmap_assoc in a stack inclusion *)
Program Definition pappUnassocStackIncl stk1 stk2 stk3 :
  stackIncl (papp stk1 (papp stk2 stk3)) (papp (papp stk1 stk2) stk3) :=
  eqReflStackIncl _ _ (eq_sym (papp_assoc _ _ _)).

(* Compose two stack inclusions *)
Program Definition compStackIncl {stk1 stk2 stk3}
  (incl1 : stackIncl stk1 stk2) (incl2 : stackIncl stk2 stk3)
  : stackIncl stk1 stk3 :=
  fun n => incl2 (incl1 n).
Next Obligation.
Proof.
  destruct (proj2_sig incl1 n H) as [ eq1 lt1 ].
  destruct (proj2_sig incl2 _ lt1) as [ eq2 lt2 ].
  split.
  - rewrite eq1. rewrite eq2. reflexivity.
  - assumption.
Defined.

(* Prefix a stackIncl with a single LetRecType that stays constant *)
Program Definition consStackIncl lrt stk1 stk2 (incl : stackIncl stk1 stk2) :
  stackIncl (pcons lrt stk1) (pcons lrt stk2) :=
  fun n =>
    match n with
    | 0 => 0
    | S n' => S (incl n')
    end.
Next Obligation.
Proof.
  split.
  - destruct n; [ reflexivity | ].
    assert (n < plength stk1) as lt1; [ apply le_S_n; assumption | ].
    unfold nthLRT. simpl. apply (proj1 (proj2_sig incl n lt1)).
  - destruct n.
    + apply le_n_S. apply le_0_n.
    + apply Lt.lt_n_S.
      assert (n < plength stk1) as lt1; [ apply le_S_n; assumption | ].
      apply (proj2 (proj2_sig incl n lt1)).
Defined.

(* Prefix a stackIncl with a list of LetRecTypes that stay constant *)
Fixpoint prefixStackIncl pre stk1 stk2 (incl: stackIncl stk1 stk2)
  : stackIncl (papp pre stk1) (papp pre stk2) :=
  match pre return stackIncl (papp pre stk1) (papp pre stk2) with
  | pnil => incl
  | pcons lrt pre' =>
      consStackIncl lrt _ _ (prefixStackIncl pre' stk1 stk2 incl)
  end.

(* "Weaken" a stack by appending another stack on the left *)
Program Definition weakenLeftStackIncl stk1 stk2 :
  stackIncl stk2 (papp stk1 stk2) :=
  fun n => plength stk1 + n.
Next Obligation.
  split.
  - symmetry; apply nth_default'_app_right.
  - rewrite plength_papp. apply Plus.plus_lt_compat_l. assumption.
Defined.

(* "Weaken" a stack by appending another stack on the right *)
Program Definition weakenRightStackIncl stk1 stk2 :
  stackIncl stk1 (papp stk1 stk2) :=
  fun n => n.
Next Obligation.
  split.
  - symmetry; apply nth_default'_app_left; assumption.
  - rewrite plength_papp.
    eapply Lt.lt_le_trans; [ eassumption | apply Plus.le_plus_l ].
Defined.

(* Prefix a stackIncl with a single LetRecType on the left that maps into a
prefix of LetRecTypes on the right *)
Program Definition consPrefixStackIncl n (pre : FunStack) (lt : n < plength pre)
  stk1 stk2 (incl : stackIncl stk1 stk2) :
  stackIncl (pcons (nthLRT pre n) stk1) (papp pre stk2) :=
  fun m =>
    match m with
    | 0 => n
    | S n' => plength pre + incl n'
    end.
Next Obligation.
  destruct n0; split.
  - unfold nthLRT. rewrite nth_default'_app_left; [ | assumption ]. reflexivity.
  - eapply Lt.lt_le_trans; [ eassumption | ]. apply plength_app_r.
  - unfold nthLRT. rewrite nth_default'_app_right.
    apply (proj1 (proj2_sig incl n0 (le_S_n _ _ H))).
  - rewrite plength_papp. apply Plus.plus_lt_compat_l.
    apply (proj2 (proj2_sig incl n0 (le_S_n _ _ H))).
Defined.


(** Defining recursive calls in a stack-polymorphic way **)

(* An input for a call in a stack can only be to a call number that is in range *)
Lemma LRTInput_in_bounds stk stk' n (args : LRTInput stk' (nthLRT stk n)) :
  n < plength stk.
Proof.
  destruct (Compare_dec.le_lt_dec (plength stk) n); [ | assumption ].
  unfold nthLRT in args; rewrite nth_default'_default in args;
    [ destruct (projT1 args) | assumption ].
Qed.

Definition castLRTInput stk lrt lrt' (e : lrt = lrt')
  (args : LRTInput stk lrt) : LRTInput stk lrt' :=
  eq_rect lrt (LRTInput stk) args lrt' e.

Program Definition uncastLRTOutput stk lrt lrt' (e : lrt = lrt')
  (args : LRTInput stk lrt)
  (ret : LRTOutput stk lrt' (castLRTInput _ lrt lrt' e args)) :
  LRTOutput stk lrt args := _.

(* A StackCall in a polymorphic context (in the sense of PolySpecFun, below),
where the call is into a function in stk1 but where stk1 has been extended to
some arbitrary stk2 *)
Inductive PolyStackCall stk1 stk2 : Type@{entree_u} :=
| PolyStackCallOfArgs n (args : LRTInput stk2 (nthLRT stk1 n)).

(* The return type for a PolyStackCall recursive call *)
Definition PolyStackCallRet stk1 stk2
  (call: PolyStackCall stk1 stk2) : Type@{entree_u} :=
  match call with
  | PolyStackCallOfArgs _ _ n args => LRTOutput stk2 (nthLRT stk1 n) args
  end.

(* Convert a PolyStackCall to the StackCall it is meant to be mapped to *)
Definition mapPolyStackCall stk1 stk2 (incl : stackIncl stk1 stk2)
  (call : PolyStackCall stk1 stk2) : StackCall stk2 :=
  match call with
  | PolyStackCallOfArgs _ _ n args =>
      StackCallOfArgs stk2 (applyIncl incl n)
        (castLRTInput stk2 _ _ (eq_sym (applyInclEq incl n)) args)
  end.

(* Convert a StackCallRet back to a PolyStackCallRet *)
Definition unmapPolyStackCallRet stk1 stk2 (incl : stackIncl stk1 stk2)
  (call : PolyStackCall stk1 stk2) :
  StackCallRet _ (mapPolyStackCall _ _ incl call) ->
  PolyStackCallRet stk1 stk2 call :=
  match call return StackCallRet _ (mapPolyStackCall _ _ incl call) ->
                    PolyStackCallRet stk1 stk2 call with
  | PolyStackCallOfArgs _ _ n args =>
      uncastLRTOutput _ _ _ (eq_sym (applyInclEq incl n)) args
  end.

(* Tell the typeclass system to look for stackIncl assumptions *)
Global Hint Extern 1 (stackIncl _ _) => assumption : typeclass_instances.

Global Instance EncodingType_PolyStackCall stk1 stk2
  : EncodingType (PolyStackCall stk1 stk2) := PolyStackCallRet stk1 stk2.

Global Program Instance ReSum_PolyStackCall stk1 stk2 (incl : stackIncl stk1 stk2) :
  ReSum (PolyStackCall stk1 stk2) (StackCall stk2) :=
  mapPolyStackCall stk1 stk2 incl.

Global Program Instance ReSumRet_PolyStackCall stk1 stk2
  (incl : stackIncl stk1 stk2) :
  ReSumRet (PolyStackCall stk1 stk2) (StackCall stk2) :=
  unmapPolyStackCallRet stk1 stk2 incl.

Global Program Instance ReSum_PolyStackCall_FunStackE E stk1 stk2
  (incl : stackIncl stk1 stk2) :
  ReSum (PolyStackCall stk1 stk2) (FunStackE E stk2) :=
  fun args => inl (mapPolyStackCall _ _ incl args).

Global Program Instance ReSumRet_PolyStackCall_FunStackE E stk1 stk2
  (incl : stackIncl stk1 stk2) :
  ReSumRet (PolyStackCall stk1 stk2) (FunStackE E stk2) :=
  fun args ret => unmapPolyStackCallRet _ _ incl args ret.

Definition CallS E stk1 stk2 (incl : stackIncl stk1 stk2)
  (call : PolyStackCall stk1 stk2) : SpecM E stk2 (encodes call) :=
  trigger call.

Definition mkPolyStackCall stk1 stk2 n
  : lrtPi stk2 (nthLRT stk1 n) (fun _ => PolyStackCall stk1 stk2) :=
  lrtLambda stk2 (nthLRT stk1 n)
    (fun _ => PolyStackCall stk1 stk2)
    (fun args => PolyStackCallOfArgs stk1 stk2 n args).


(** Stack-polymorphic function tuples **)

(* A monadic function that is polymorphic in its function stack *)
Definition PolySpecFun E stack lrt :=
  forall stack', stackIncl stack stack' -> SpecFun E stack' lrt.

(* Apply a stackIncl to a PolySpecFun *)
Definition inclPolySpecFun E stk stk' lrt (incl : stackIncl stk stk')
  (f : PolySpecFun E stk lrt) : PolySpecFun E stk' lrt :=
  fun stk'' incl' => f stk'' (compStackIncl incl incl').

(* A StackTuple that is polymorphic in its function stack, which defines
functions for all the defs that can call all the calls *)
Definition PolyStackTuple E calls defs :=
  forall calls', stackIncl calls calls' -> StackTuple E calls' defs.

(* Append two PolyStackTuples *)
Definition appPolyStackTuple E calls defs1 defs2
  (pft1 : PolyStackTuple E calls defs1)
  (pft2 : PolyStackTuple E calls defs2)
  : PolyStackTuple E calls (papp defs1 defs2) :=
  fun stack' incl =>
    appMapTuple _ defs1 defs2 (pft1 stack' incl) (pft2 stack' incl).

(* Apply a stackIncl to the calls list of a PolyStackTuple *)
Definition inclPolyStackTuple E calls1 calls2 defs
  (incl : stackIncl calls1 calls2)
  (pft : PolyStackTuple E calls1 defs)
  : PolyStackTuple E calls2 defs :=
  fun stack' incl' => pft stack' (compStackIncl incl incl').

(* An extension of a tuple along a stackIncl is a tuple that has all the same
elements at the new positions mapped to by the stackIncl *)
Definition isTupleExt E stk stk' (incl : stackIncl stk stk')
                       (tup1 : mapTuple (SpecFun E stk') stk)
                       (tup2 : StackTuple E stk' stk') : Prop :=
  forall n,
    n < plength stk ->
    nthProjDefaultSig (SpecFun E stk') (defaultSpecFunSig E stk') stk n tup1
    = nthProjDefaultSig (SpecFun E stk') (defaultSpecFunSig E stk') stk'
        (proj1_sig incl n) tup2.


(* An instance of a PolyStackTuple is a StackTuple for a possibly extended stack
that includes all the all the SpecFuns in the original StackTuple *)
Definition isTupleInst E stk stk' (incl : stackIncl stk stk')
                       (ptup : PolyStackTuple E stk stk)
                       (tup : StackTuple E stk' stk') : Prop :=
  isTupleExt E stk stk' incl (ptup stk' incl) tup.

Lemma isTupleInstAppL E stk1 stk2 stk' (incl : stackIncl (papp stk1 stk2) stk')
                      (ptup1 : PolyStackTuple E stk1 stk1)
                      (ptup2 : PolyStackTuple E (papp stk1 stk2) stk2)
                      (tup : StackTuple E stk' stk') :
  isTupleInst E (papp stk1 stk2) stk' incl
              (appPolyStackTuple
                 _ _ _ _
                 (inclPolyStackTuple _ _ _ _
                    (weakenRightStackIncl _ _)
                    ptup1)
                 ptup2)
              tup ->
  isTupleInst E stk1 stk' (compStackIncl (weakenRightStackIncl _ _) incl)
              ptup1 tup.
Proof.
  unfold isTupleInst, appPolyStackTuple, inclPolyStackTuple. simpl.
  intros H n n_lt. etransitivity; [ | apply H ].
  - symmetry; apply nthProjDefaultSig_app_l. assumption.
  - eapply Lt.lt_le_trans; [ eassumption | apply plength_app_r ].
Qed.

Lemma isTupleInstAppR E stk1 stk2 stk' (incl : stackIncl (papp stk1 stk2) stk')
                      (ptup1 : PolyStackTuple E (papp stk1 stk2) stk1)
                      (ptup2 : PolyStackTuple E stk2 stk2)
                      (tup : StackTuple E stk' stk') :
  isTupleInst E (papp stk1 stk2) stk' incl
              (appPolyStackTuple
                 _ _ _ _
                 ptup1
                 (inclPolyStackTuple _ _ _ _
                    (weakenLeftStackIncl _ _)
                    ptup2))
              tup ->
  isTupleInst E stk2 stk' (compStackIncl (weakenLeftStackIncl _ _) incl)
              ptup2 tup.
Proof.
  unfold isTupleInst, appPolyStackTuple, inclPolyStackTuple. simpl.
  intros H n n_lt.
  etransitivity; [ | apply H ].
  - rewrite nthProjDefaultSig_app_r; [ | apply Plus.le_plus_l ].
    simpl. rewrite Minus.minus_plus. reflexivity.
  - rewrite plength_papp. apply Plus.plus_lt_compat_l. assumption.
Qed.


(** Specification Definitions **)

(* A "spec definition" represents a definition of a SpecM monadic function via
LetRecS over a tuple of recursive function bodies *)
Record SpecDef E :=
  { defStack : FunStack;
    defFuns : PolyStackTuple E defStack defStack;
    defLRT : LetRecType;
    defBody : PolySpecFun E defStack defLRT }.

(* Complete a SpecDef to a SpecM computation *)
Definition completeSpecDef E (d : SpecDef E)
  (args : LRTInput (defStack E d) (defLRT E d)) :
  SpecM E pnil (LRTOutput _ _ args) :=
  LetRecS E _ (defStack _ d)
    (defFuns _ d (defStack _ d) (reflStackIncl _))
    (lrtApply _ _ _ (defBody _ d (defStack _ d) (reflStackIncl _)) args).

(* Build the concatenated FunStack for a list of imported spec defs *)
Definition impsStack E (imps : plist (SpecDef E)) : FunStack :=
  pconcat (pmap (defStack _) imps).

(* Buuild the list of LetRecTypes implemented by a list of imported spec defs *)
Definition impsLRTs E (imps : plist (SpecDef E)) : FunStack :=
  pmap (defLRT _) imps.

(* Build the list of recursive functions for a list of imported spec defs *)
Fixpoint impsFuns E (imps : plist (SpecDef E)) :
  PolyStackTuple E (impsStack E imps) (impsStack E imps) :=
  match imps return PolyStackTuple E (impsStack E imps) (impsStack E imps) with
  | pnil => fun _ _ => tt
  | pcons d imps' =>
      appPolyStackTuple _ _ _ _
        (inclPolyStackTuple _ _ _ _
           (weakenRightStackIncl _ _)
           (defFuns _ d))
        (inclPolyStackTuple _ _ _ _
           (weakenLeftStackIncl _ _)
           (impsFuns E imps'))
  end.

(* The combined function stack for defineSpec *)
Definition defineSpecStack E stk (imps : plist (SpecDef E)) :=
  papp stk (impsStack E imps).

(* Define a spec from: a list of imported spec definitions; a tuple of
recursively-defined functions; and a body that can call into either *)
Definition defineSpec E stk lrt (imps : plist (SpecDef E))
  (recs : PolyStackTuple E (defineSpecStack E stk imps) stk)
  (body : PolySpecFun E (defineSpecStack E stk imps) lrt) : SpecDef E :=
  {|
    defStack := defineSpecStack E stk imps;
    defFuns :=
      appPolyStackTuple _ _ _ _
        recs (inclPolyStackTuple _ _ _ _
                (weakenLeftStackIncl _ _) (impsFuns E imps));
    defLRT := lrt;
    defBody := body
  |}.

(*
(* Get the body of the nth import in a list of imports *)
Fixpoint nthImportBody E imps n :
  PolySpecFun E (impsStack E imps) (nthLRT (impsLRTs E imps) n) :=
  match imps return PolySpecFun E (impsStack E imps) (nthLRT (impsLRTs E imps) n)
  with
  | pnil => fun _ _ bot => match bot with end
  | pcons imp imps' =>
      match n return PolySpecFun E (impsStack E (pcons imp imps'))
                       (nthLRT (impsLRTs E (pcons imp imps')) n) with
      | 0 =>
          inclPolySpecFun _ _ _ _ (weakenRightStackIncl _ _) (defBody E imp)
      | S n' =>
          inclPolySpecFun _ _ _ _ (weakenLeftStackIncl _ _)
            (nthImportBody E imps' n')
      end
  end.
*)

(* A trivial spec definition *)
Definition defaultSpecDef E : SpecDef E :=
  {|
    defStack := pnil;
    defFuns := fun _ _ => tt;
    defLRT := default_lrt;
    defBody := fun _ _ bot => match bot with end;
  |}.

(* Get the nth spec definition from a list, defaulting to the trivial one *)
Definition nthSpecDef {E} (defs : plist (SpecDef E)) n :=
  nth_default' (defaultSpecDef E) defs n.

(* Build a stackIncl from the FunStack of an spec def to that of a list of defs *)
Fixpoint nthSpecIncl E imps n :
  stackIncl (defStack E (nthSpecDef imps n)) (impsStack E imps) :=
  match imps return stackIncl (defStack E (nthSpecDef imps n)) (impsStack E imps) with
  | pnil => nilStackIncl _
  | pcons imp imps' =>
      match n return stackIncl (defStack E (nthSpecDef (pcons imp imps') n))
                       (impsStack E (pcons imp imps')) with
      | 0 => weakenRightStackIncl _ _
      | S n' => compStackIncl (nthSpecIncl E imps' n') (weakenLeftStackIncl _ _)
      end
  end.

(* Build a stackIncl from an imported def to a defineSpec *)
Definition importIncl E stk imps n :
  stackIncl (defStack E (nthSpecDef imps n)) (defineSpecStack E stk imps) :=
  compStackIncl (nthSpecIncl E imps n) (weakenLeftStackIncl _ _).


(* FIXME: just keeping LRTValue in case it is useful in the future...
(* A value of an LRTArgType *)
Fixpoint LRTValue E (stack:FunStack) (argTp : LRTArgType) : Type@{entree_u} :=
  match argTp with
  | ArgType_Const A => A
  | ArgType_Prod A B => LRTValue E stack A * LRTValue E stack B
  | ArgType_Sigma A B => { x:A & LRTValue E stack (B x) }
  | ArgType_Fun lrt => LRTValueFun E stack lrt
  end
with
LRTValueFun E (stack:FunStack) (lrt : LetRecType) : Type@{entree_u} :=
  match lrt with
  | LRT_SpecM R => SpecM E stack (LRTValue E stack R)
  | LRT_FunDep A lrtF => forall a, LRTValueFun E stack (lrtF a)
  | LRT_FunClos A lrt' => LRTArg stack A -> LRTValueFun E stack lrt'
  end.

(* Convert an LRTArg to an LRTValue *)
Fixpoint LRTArg2Value E stack argTp : LRTArg stack argTp -> LRTValue E stack argTp :=
  match argTp return LRTArg stack argTp -> LRTValue E stack argTp with
  | ArgType_Const _ => fun x => x
  | ArgType_Prod A B => fun tup => (LRTArg2Value E stack A (fst tup),
                                     LRTArg2Value E stack B (snd tup))
  | ArgType_Sigma A B =>
      fun sig => existT _ (projT1 sig) (LRTArg2Value E stack (B (projT1 sig)) (projT2 sig))
  | ArgType_Fun lrt =>
      fun sig =>
        LRTArgFun2ValueFun E stack lrt
          (fun args =>
             CallS
               E stack
               (StackCallOfArgs _ (projT1 sig)
                  (applyDepApp stack _ _ (projT2 sig) args)))
  end
with
LRTArgFun2ValueFun E stack lrt : (forall args:LRTInput stack lrt,
                                     SpecM E stack (LRTOutput stack lrt args)) ->
                                 LRTValueFun E stack lrt :=
  match lrt return (forall args,
                    SpecM E stack (LRTOutput stack lrt args)) ->
                   LRTValueFun E stack lrt with
  | LRT_SpecM R =>
      fun f => bind (f tt) (fun x => ret (LRTArg2Value E stack R x))
  | LRT_FunDep A lrt' =>
      fun f a =>
        LRTArgFun2ValueFun E stack (lrt' a) (fun args => f (existT _ a args))
  | LRT_FunClos A lrt' =>
      fun f a =>
        LRTArgFun2ValueFun E stack lrt' (fun args => f (a, args))
  end.
*)

(** Notations in terms of the SpecM combinators **)
Module SpecMNotations.

Notation "t1 >>= k2" := (BindS t1 k2)
                        (at level 58, left associativity) : entree_scope.
Notation "x <- t1 ;; t2" := (BindS t1 (fun x => t2) )
                        (at level 61, t1 at next level, right associativity) : entree_scope.
Notation "t1 ;; t2" := (BindS t1 (fun _ => t2))
                       (at level 61, right associativity) : entree_scope.
Notation "' p <- t1 ;; t2" :=
  (BindS t1 (fun x_ => match x_ with p => t2 end) )
  (at level 61, t1 at next level, p pattern, right associativity) : entree_scope.

End SpecMNotations.


(* Interpreting SpecM computations in the state monad *)

Section interpWithState.
Import ExtLib.Structures.Functor.

Definition StateT S M A := S -> M (S * A)%type.
Global Instance Monad_StateT M s `{Monad M} : Monad (StateT s M) :=
  {|
    ret := fun A x s => ret (s, x);
    bind := fun A B m k s => bind (m s) (fun a_s =>
                                           let (s',a) := a_s in
                                           k a s')
  |}.

Global Instance MonadIter_StateT M St `{Monad M} `{MI:MonadIter M} : MonadIter (StateT St M) :=
  fun R I body i s =>
    iter (MonadIter:=MI) (R:=St * R)
         (fun s'_i':St * I =>
            let (s',i') := s'_i' in
            bind (body i s) (fun s''_ir =>
                               match s''_ir with
                               | (s'', inl i') => ret (inl (s'', i'))
                               | (s'', inr r) => ret (inr (s'', r))
                               end)) (s,i).

Definition interpWithState {E1 E2} `{EncodingType E1} `{EncodingType E2} {St}
           (h : forall e:E1, StateT St (entree E2) (encodes e)) {A} :
  entree E1 A -> StateT St (entree E2) A :=
  iter (fun t =>
          match observe t with
          | RetF r => ret (inr r)
          | TauF t => ret (inl t)
          | VisF e k => fmap (fun x => inl (k x)) (h e)
          end).

End interpWithState.

(* Corecursively looks for performances of exceptional effects. If an
   exceptional performance is caught, then `catch` is performed instead. *)
Program CoFixpoint try_catch {E:EvType} {Γ} {A} {B}
    (is_exceptional : FunStackE E Γ -> option A)
    (catch : A -> SpecM E Γ B) :
    SpecM E Γ B -> SpecM E Γ B :=
  fun t => match t with
  | go _ _ (RetF r) => ret r
  | go _ _ (TauF t') => Tau (try_catch is_exceptional catch t')
  | go _ _ (VisF se k) =>
      match se with
      | Spec_vis fs =>
          match is_exceptional fs with 
          | Some a => catch a
          | None => Vis (Spec_vis fs) (fun x => try_catch is_exceptional catch (k _))
          end
      | Spec_forall T => Vis (Spec_forall T) (fun x => try_catch is_exceptional catch (k _))
      | Spec_exists T => Vis (Spec_exists T) (fun x => try_catch is_exceptional catch (k _))
      end
  end.
