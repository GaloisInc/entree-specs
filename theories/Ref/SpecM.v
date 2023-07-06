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
      F { n:nat & A n} { n:nat & B n} ->
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


(* The pair functor preserves colimits *)
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

(* NOTE: lrt_u is really just entree_u + 1, but Coq doesn't like that in some
places where we need to write it, so we just define it as a new universe *)
Universe lrt_u.
Constraint entree_u < lrt_u.

(* An encoded argument type for a recursive function and its arguments *)
Inductive LetRecType : Type@{lrt_u} :=
(* These three constructors represent functions of 0 or more arguments *)
| LRT_SpecM (R : LetRecType) : LetRecType
| LRT_FunDep (A : Type@{entree_u}) (rest : A -> LetRecType) : LetRecType
| LRT_FunClos (A : LetRecType) (rest : LetRecType) : LetRecType
(* These constructors represent the argument types used in functions *)
| LRT_Type (A : Type@{entree_u}) : LetRecType
| LRT_BinOp F `{ColimFunctor2 F} (A B : LetRecType) : LetRecType
| LRT_Sigma (A : Type@{entree_u}) (B : A -> LetRecType) : LetRecType
.

(* A FunStack is a list of LetRecTypes representing all of the functions bound
   by multiFixS that are currently in scope *)
Definition FunStack : Type@{lrt_u} := plist LetRecType.

(* A trivially inhabited "default" LetRecType *)
Definition default_lrt : LetRecType :=
  LRT_FunDep void (fun _ => LRT_SpecM (LRT_Type void)).

(* Get the nth element of a FunStack list, or void -> void if n is too big *)
Definition nthLRT (stk : FunStack) n : LetRecType :=
  nth_default' default_lrt stk n.

Definition nthClos (Closs : plist (LetRecType -> Type@{entree_u})) n
  : LetRecType -> Type@{entree_u} :=
  nth_default' (A:=LetRecType -> Type@{entree_u}) (fun _ => void) Closs n.

(* An argument to a recursive function call, which is a decoding of a LetRecType
to its corresponding Coq type except that functions are interpreted using the
supplied type functor *)
Fixpoint LRTArgF (Clos : LetRecType -> Type@{entree_u}) (argTp : LetRecType)
  : Type@{entree_u} :=
  match argTp with
  | LRT_SpecM R => Clos (LRT_SpecM R)
  | LRT_FunDep A B => Clos (LRT_FunDep A B)
  | LRT_FunClos A B => Clos (LRT_FunClos A B)
  | LRT_Type A => A
  | LRT_BinOp F A B => F (LRTArgF Clos A) (LRTArgF Clos B)
  | LRT_Sigma A B => { x:A & LRTArgF Clos (B x) }
  end.


(**
 ** Sequences of N arguments
 **)

(* The head input type of a monadic function type described by a LetRecType *)
Definition LRTHead (Arg: LetRecType -> Type@{entree_u}) lrt : Type@{entree_u} :=
  match lrt with
  | LRT_SpecM R => void
  | LRT_FunDep A B => A
  | LRT_FunClos A B => Arg A
  | LRT_Type A => void
  | LRT_BinOp F A B => void
  | LRT_Sigma A B => void
  end.

(* The dependent part of the LRTHead type *)
Definition LRTDepHead lrt : Type@{entree_u} :=
  match lrt with
  | LRT_SpecM R => void
  | LRT_FunDep A B => A
  | LRT_FunClos A B => unit
  | LRT_Type A => void
  | LRT_BinOp F A B => void
  | LRT_Sigma A B => void
  end.

(* The closure part of the LRTHead type *)
Definition LRTClosHead (Arg: LetRecType -> Type@{entree_u}) lrt : Type@{entree_u} :=
  match lrt with
  | LRT_SpecM R => void
  | LRT_FunDep A B => unit
  | LRT_FunClos A B => Arg A
  | LRT_Type A => void
  | LRT_BinOp F A B => void
  | LRT_Sigma A B => void
  end.

(* Project the dependent part of an LRTHead *)
Definition projLRTHeadD Arg lrt : LRTHead Arg lrt -> LRTDepHead lrt :=
  match lrt return LRTHead Arg lrt -> LRTDepHead lrt with
  | LRT_SpecM R => fun bot => match bot with end
  | LRT_FunDep A B => fun a => a
  | LRT_FunClos A B => fun arg => tt
  | LRT_Type A => fun bot => match bot with end
  | LRT_BinOp F A B => fun bot => match bot with end
  | LRT_Sigma A B => fun bot => match bot with end
  end.

(* Project the closure part of an LRTHead *)
Definition projLRTHeadC Arg lrt : LRTHead Arg lrt -> LRTClosHead Arg lrt :=
  match lrt return LRTHead Arg lrt -> LRTClosHead Arg lrt with
  | LRT_SpecM R => fun bot => match bot with end
  | LRT_FunDep A B => fun a => tt
  | LRT_FunClos A B => fun arg => arg
  | LRT_Type A => fun bot => match bot with end
  | LRT_BinOp F A B => fun bot => match bot with end
  | LRT_Sigma A B => fun bot => match bot with end
  end.

(* Given the dependent head argument of lrt, compute its tail LetRecType *)
Definition LRTTail lrt : LRTDepHead lrt -> LetRecType :=
  match lrt return LRTDepHead lrt -> LetRecType with
  | LRT_SpecM R => fun bot => match bot with end
  | LRT_FunDep A B => fun a => B a
  | LRT_FunClos A B => fun _ => B
  | LRT_Type A => fun bot => match bot with end
  | LRT_BinOp F A B => fun bot => match bot with end
  | LRT_Sigma A B => fun bot => match bot with end
  end.

Fixpoint LRTDepArgsAndRet n lrt : { T:Type@{entree_u} & T -> LetRecType } :=
  match n with
  | 0 => existT (fun T => T -> LetRecType) unit (fun _ => lrt)
  | S n' =>
      existT (fun T => T -> LetRecType)
        { args: projT1 (LRTDepArgsAndRet n' lrt) &
                  LRTDepHead (projT2 (LRTDepArgsAndRet n' lrt) args) }
             (fun args =>
                LRTTail (projT2 (LRTDepArgsAndRet n' lrt) (projT1 args)) (projT2 args))
  end.

Definition LRTDepArgs n lrt : Type@{entree_u} := projT1 (LRTDepArgsAndRet n lrt).

Definition LRTDepArgsOut n lrt (args: LRTDepArgs n lrt) : LetRecType :=
  projT2 (LRTDepArgsAndRet n lrt) args.

Definition LRTDepArgsNil lrt : LRTDepArgs 0 lrt := tt.

Definition LRTDepArgsConsR n lrt (dargs: LRTDepArgs n lrt)
  (darg: LRTDepHead (LRTDepArgsOut n lrt dargs)) : LRTDepArgs (S n) lrt :=
  existT _ dargs darg.

Definition LRTDepArgsConsROutEq n lrt dargs darg :
  LRTDepArgsOut (S n) lrt (LRTDepArgsConsR n lrt dargs darg) =
    LRTTail (LRTDepArgsOut n lrt dargs) darg :=
  eq_refl _. (* Checks that this holds by definitional equality *)

Fixpoint LRTClosArgsF (Arg: LetRecType -> Type@{entree_u}) n lrt
  : LRTDepArgs n lrt -> Type@{entree_u} :=
  match n return LRTDepArgs n lrt -> Type@{entree_u} with
  | 0 => fun _ => unit
  | S n' =>
      fun dargs =>
        prod (LRTClosArgsF Arg n' lrt (projT1 dargs))
          (LRTClosHead Arg (LRTDepArgsOut n' lrt (projT1 dargs)))
  end.

Definition LRTClosArgsFNil Arg lrt : LRTClosArgsF Arg 0 lrt (LRTDepArgsNil lrt) := tt.

Definition LRTClosArgsFConsR Arg n lrt dargs (cargs: LRTClosArgsF Arg n lrt dargs)
  (darg: LRTDepHead (LRTDepArgsOut n lrt dargs))
  (carg: LRTClosHead Arg (LRTDepArgsOut n lrt dargs)) :
  LRTClosArgsF Arg (S n) lrt (LRTDepArgsConsR n lrt dargs darg) :=
  (cargs, carg).

Definition LRTArgsF Arg n lrt : Type@{entree_u} :=
  { dep_args:LRTDepArgs n lrt & LRTClosArgsF Arg n lrt dep_args }.

Definition LRTArgsFOut Arg n lrt : LRTArgsF Arg n lrt -> LetRecType :=
  fun args => LRTDepArgsOut n lrt (projT1 args).

Definition LRTArgsFNil Arg lrt : LRTArgsF Arg 0 lrt := existT _ tt tt.

Definition LRTArgsFConsR Arg n lrt (args: LRTArgsF Arg n lrt)
  (darg: LRTDepHead (LRTDepArgsOut n lrt (projT1 args)))
  (carg: LRTClosHead Arg (LRTDepArgsOut n lrt (projT1 args))) :
  LRTArgsF Arg (S n) lrt :=
  existT _ (LRTDepArgsConsR n lrt (projT1 args) darg)
    (LRTClosArgsFConsR Arg n lrt (projT1 args) (projT2 args) darg carg).

Definition LRTArgsFConsROutEq Arg n lrt args darg carg :
  LRTArgsFOut Arg (S n) lrt (LRTArgsFConsR Arg n lrt args darg carg) =
    LRTTail (LRTArgsFOut Arg n lrt args) darg :=
  eq_refl _. (* Checks that this holds by definitional equality *)


(**
 ** Defining closures
 **)

Definition ClosElemF (Closs : plist (LetRecType -> Type@{entree_u})) lrt
  : Type@{entree_u} :=
  { n & nthClos Closs n lrt }.

Definition ClosElemFConsClos Clos Closs lrt (ce: ClosElemF Closs lrt)
  : ClosElemF (pcons Clos Closs) lrt :=
  existT _ (S (projT1 ce)) (projT2 ce).

Record LRTClosF stk (Closs : plist (LetRecType -> Type@{entree_u})) lrt
  : Type@{entree_u} :=
  { lrtClosNum : nat;
    lrtClosNumArgs : nat;
    lrtClosDepArgs : LRTDepArgs lrtClosNumArgs (nthLRT stk lrtClosNum);
    lrtClosClosArgs : LRTClosArgsF (LRTArgF (ClosElemF Closs)) lrtClosNumArgs
                        (nthLRT stk lrtClosNum) lrtClosDepArgs;
    lrtClosLRTEq : LRTDepArgsOut lrtClosNumArgs _ lrtClosDepArgs = lrt }.

Definition LRTClosFOut {stk Closs lrt} (clos: LRTClosF stk Closs lrt) : LetRecType :=
  LRTDepArgsOut (lrtClosNumArgs _ _ _ clos) _ (lrtClosDepArgs _ _ _ clos).

Definition applyLRTClosFRaw stk Closs lrt (clos: LRTClosF stk Closs lrt)
  (darg: LRTDepHead (LRTClosFOut clos))
  (carg: LRTClosHead (LRTArgF (ClosElemF Closs)) (LRTClosFOut clos))
  : LRTClosF stk Closs (LRTTail (LRTClosFOut clos) darg) :=
  {|
    lrtClosNum := lrtClosNum _ _ _ clos;
    lrtClosNumArgs := S (lrtClosNumArgs _ _ _ clos);
    lrtClosDepArgs := LRTDepArgsConsR _ _ (lrtClosDepArgs _ _ _ clos) darg;
    lrtClosClosArgs := LRTClosArgsFConsR _ _ _ _ (lrtClosClosArgs _ _ _ clos) darg carg;
    lrtClosLRTEq := eq_refl _;
  |}.

Program Definition applyLRTClosF stk Closs lrt (clos: LRTClosF stk Closs lrt) :
  forall darg: LRTDepHead lrt, LRTClosHead (LRTArgF (ClosElemF Closs)) lrt ->
                               LRTClosF stk Closs (LRTTail lrt darg) :=
  eq_rect
    (LRTClosFOut clos)
    (fun lrt' => forall darg, LRTClosHead (LRTArgF (ClosElemF Closs)) lrt' ->
                              LRTClosF stk Closs (LRTTail lrt' darg))
    (applyLRTClosFRaw stk Closs lrt clos)
    lrt (lrtClosLRTEq _ _ _ clos).


(**
 ** Lifting functions for closures and arguments
 **)

Fixpoint LRTArgFConsClos Clos Closs argTp
  : LRTArgF (ClosElemF Closs) argTp ->
    LRTArgF (ClosElemF (pcons Clos Closs)) argTp :=
  match argTp return LRTArgF (ClosElemF Closs) argTp ->
                     LRTArgF (ClosElemF (pcons Clos Closs)) argTp with
  | LRT_SpecM R => ClosElemFConsClos Clos Closs _
  | LRT_FunDep A B => ClosElemFConsClos Clos Closs _
  | LRT_FunClos A B => ClosElemFConsClos Clos Closs _
  | LRT_Type A => fun a => a
  | LRT_BinOp F A B =>
      fmap2 _ _ _ _ (LRTArgFConsClos Clos Closs A) (LRTArgFConsClos Clos Closs B)
  | LRT_Sigma A B =>
      fun p => existT _ (projT1 p)
                 (LRTArgFConsClos Clos Closs (B (projT1 p)) (projT2 p))
  end.

Definition LRTClosHeadConsClos Clos Closs lrt
  : LRTClosHead (LRTArgF (ClosElemF Closs)) lrt ->
    LRTClosHead (LRTArgF (ClosElemF (pcons Clos Closs))) lrt :=
  match lrt return LRTClosHead (LRTArgF (ClosElemF Closs)) lrt ->
                   LRTClosHead (LRTArgF (ClosElemF (pcons Clos Closs))) lrt with
  | LRT_SpecM R => fun bot => match bot with end
  | LRT_FunDep A B => fun u => u
  | LRT_FunClos A B => fun arg => LRTArgFConsClos Clos Closs A arg
  | LRT_Type A => fun bot => match bot with end
  | LRT_BinOp F A B => fun bot => match bot with end
  | LRT_Sigma A B => fun bot => match bot with end
  end.

Fixpoint LRTClosArgsFConsClos Clos Closs n lrt :
  forall dargs, LRTClosArgsF (LRTArgF (ClosElemF Closs)) n lrt dargs ->
                LRTClosArgsF (LRTArgF (ClosElemF (pcons Clos Closs))) n lrt dargs :=
  match n return
        forall dargs,
          LRTClosArgsF (LRTArgF (ClosElemF Closs)) n lrt dargs ->
          LRTClosArgsF (LRTArgF (ClosElemF (pcons Clos Closs))) n lrt dargs
  with
  | 0 => fun _ u => u
  | S n' =>
      fun dargs cargs =>
        (LRTClosArgsFConsClos Clos Closs n' lrt (projT1 dargs) (fst cargs),
          LRTClosHeadConsClos Clos Closs _ (snd cargs))
  end.

Definition LRTClosFConsClos stk Clos Closs lrt
  (clos : LRTClosF stk Closs lrt) : LRTClosF stk (pcons Clos Closs) lrt :=
  {|
    lrtClosNum := lrtClosNum _ _ _ clos;
    lrtClosNumArgs := lrtClosNumArgs _ _ _ clos;
    lrtClosDepArgs := lrtClosDepArgs _ _ _ clos;
    lrtClosClosArgs :=
      LRTClosArgsFConsClos Clos Closs _ _ _ (lrtClosClosArgs _ _ _ clos);
    lrtClosLRTEq := lrtClosLRTEq _ _ _ clos;
 |}.


(**
 ** Tie the knot by defining closures by level
 **)

Fixpoint LRTClosTypes stk lvl : plist (LetRecType -> Type@{entree_u}) :=
  match lvl with
  | 0 => pnil
  | S lvl' =>
      pcons (LRTClosF stk (LRTClosTypes stk lvl')) (LRTClosTypes stk lvl')
  end.

Definition ClosElemLvl stk lvl lrt : Type@{entree_u} :=
  ClosElemF (LRTClosTypes stk lvl) lrt.

Definition ClosElemLvlInc stk lvl lrt (clos: ClosElemLvl stk lvl lrt)
  : ClosElemLvl stk (S lvl) lrt :=
  ClosElemFConsClos _ _ lrt clos.

Definition LRTArgLvl stk argTp lvl : Type@{entree_u} :=
  LRTArgF (ClosElemLvl stk lvl) argTp.

Definition LRTArgLvlInc stk argTp lvl (arg: LRTArgLvl stk argTp lvl)
  : LRTArgLvl stk argTp (S lvl) :=
  LRTArgFConsClos _ _ argTp arg.

Definition LRTArgHeadLvl stk lrt lvl : Type@{entree_u} :=
  LRTClosHead (fun argTp => LRTArgLvl stk argTp lvl) lrt.

Definition LRTArgHeadLvlInc stk lrt lvl (arg: LRTArgHeadLvl stk lrt lvl) :
  LRTArgHeadLvl stk lrt (S lvl) :=
  LRTClosHeadConsClos _ _ lrt arg.

Definition LRTClosArgsLvl stk n lrt lvl dargs :=
  LRTClosArgsF (fun argTp => LRTArgLvl stk argTp lvl) n lrt dargs.

Definition LRTClosArgsLvlInc stk n lrt lvl dargs
  (cargs: LRTClosArgsLvl stk n lrt lvl dargs)
  : LRTClosArgsLvl stk n lrt (S lvl) dargs :=
  LRTClosArgsFConsClos _ _ n lrt dargs cargs.

Definition LRTClosLvl stk lrt lvl :=
  LRTClosF stk (LRTClosTypes stk lvl) lrt.

Definition LRTClosLvlInc stk lrt lvl (clos: LRTClosLvl stk lrt lvl)
  : LRTClosLvl stk lrt (S lvl) :=
  LRTClosFConsClos stk _ _ lrt clos.

Definition applyLRTClosLvl stk lrt lvl (clos: LRTClosLvl stk lrt lvl)
  (darg: LRTDepHead lrt) (carg: LRTArgHeadLvl stk lrt lvl)
  : LRTClosLvl stk (LRTTail lrt darg) lvl :=
  applyLRTClosF stk _ lrt clos darg carg.


(**
 ** Defining closures and arguments at arbitrary levels, and mapping them to and
 ** from their corresponding leveled types
 **)

Definition LRTClos stk lrt : Type@{entree_u} :=
  { lvl & LRTClosLvl stk lrt lvl }.

Definition LRTClosToClosElem stk lrt (clos: LRTClos stk lrt)
  : { lvl & ClosElemLvl stk lvl lrt } :=
  existT _ (S (projT1 clos)) (existT _ 0 (projT2 clos)).

Fixpoint LRTClosFromClosElemH stk lrt lvl lft :
  nthClos (LRTClosTypes stk lvl) lft lrt -> LRTClosLvl stk lrt (lvl - S lft) :=
  match lvl return nthClos (LRTClosTypes stk lvl) lft lrt ->
                   LRTClosLvl stk lrt (lvl - S lft) with
  | 0 => fun bot => match bot with end
  | S lvl' =>
      match lft return nthClos (LRTClosTypes stk (S lvl')) lft lrt ->
                       LRTClosLvl stk lrt (lvl' - lft) with
      | 0 =>
          match lvl' return nthClos (LRTClosTypes stk (S lvl')) 0 lrt ->
                            LRTClosLvl stk lrt (lvl' - 0) with
          | 0 => fun clos => clos
          | S lvl'' => fun clos => clos
          end
      | S lft' => fun clos => LRTClosFromClosElemH stk lrt lvl' lft' clos
      end
  end.

Definition LRTClosFromClosElem stk lrt lvl
  (clos: ClosElemLvl stk lvl lrt) : LRTClos stk lrt :=
  existT _ _ (LRTClosFromClosElemH stk lrt lvl (projT1 clos) (projT2 clos)).

Definition LRTClosFromClosElemInc stk lrt lvl clos :
  LRTClosFromClosElem stk lrt (S lvl) (ClosElemLvlInc stk lvl lrt clos) =
  LRTClosFromClosElem stk lrt lvl clos :=
  eq_refl _. (* Check that this equality holds by definitional equality *)

Lemma LRTClosToFromClosElem stk lrt clos :
  LRTClosFromClosElem stk lrt
    (projT1 (LRTClosToClosElem stk lrt clos))
    (projT2 (LRTClosToClosElem stk lrt clos)) = clos.
Proof.
  destruct clos as [lvl clos]. revert clos; induction lvl; intros; reflexivity.
Qed.

Definition LRTArg stk argTp : Type@{entree_u} := LRTArgF (LRTClos stk) argTp.

Fixpoint LRTArgMax stk argTp
  : LRTArg stk argTp -> { lvl & LRTArgLvl stk argTp lvl } :=
  match argTp return LRTArg stk argTp -> { lvl & LRTArgLvl stk argTp lvl } with
  | LRT_SpecM R => fun clos => LRTClosToClosElem stk _ clos
  | LRT_FunDep A B => fun clos => LRTClosToClosElem stk _ clos
  | LRT_FunClos A B => fun clos => LRTClosToClosElem stk _ clos
  | LRT_Type A => fun a => existT _ 0 a
  | LRT_BinOp F A B =>
      fun x =>
        fmapMax2 (LRTArgLvl stk A) (LRTArgLvl stk B)
          (LRTArgLvlInc stk A) (LRTArgLvlInc stk B)
          (fmap2 _ _ _ _ (LRTArgMax stk A) (LRTArgMax stk B) x)
  | LRT_Sigma A B =>
      fun p =>
        existT _ (projT1 (LRTArgMax stk (B (projT1 p)) (projT2 p)))
          (existT _ (projT1 p) (projT2 (LRTArgMax stk (B (projT1 p)) (projT2 p))))
  end.


Fixpoint LRTArgMaxInv stk argTp lvl :
  LRTArgLvl stk argTp lvl -> LRTArg stk argTp :=
  match argTp return LRTArgLvl stk argTp lvl -> LRTArg stk argTp with
  | LRT_SpecM R => fun clos => LRTClosFromClosElem stk _ _ clos
  | LRT_FunDep A B => fun clos => LRTClosFromClosElem stk _ _ clos
  | LRT_FunClos A B => fun clos => LRTClosFromClosElem stk _ _ clos
  | LRT_Type A => fun a => a
  | LRT_BinOp F A B =>
      fmap2
        (LRTArgLvl stk A lvl) (LRTArg stk A) (LRTArgLvl stk B lvl) (LRTArg stk B)
        (LRTArgMaxInv stk A lvl) (LRTArgMaxInv stk B lvl)
  | LRT_Sigma A B =>
      fun p =>
        existT _ (projT1 p) (LRTArgMaxInv stk (B (projT1 p)) lvl (projT2 p))
  end.

Lemma LRTArgMaxInvInc stk argTp lvl (arg : LRTArgLvl stk argTp lvl) :
  LRTArgMaxInv stk argTp lvl arg
  = LRTArgMaxInv stk argTp (S lvl) (LRTArgLvlInc stk argTp lvl arg).
Proof.
  revert arg; induction argTp; intros; simpl; try reflexivity.
  - unfold LRTArgLvlInc; simpl.
    rewrite fmap2Comp.
    apply (fmap2Proper (F:=F)); [ | | reflexivity ];
      repeat intro; subst x; [ apply IHargTp1 | apply IHargTp2 ].
  - f_equal; apply H.
Qed.

Lemma LRTArgMaxInvEq stk argTp arg :
  LRTArgMaxInv stk argTp (projT1 (LRTArgMax stk argTp arg))
    (projT2 (LRTArgMax stk argTp arg))
  = arg.
Proof.
  revert arg; induction argTp; intros; simpl.
  - apply LRTClosToFromClosElem.
  - apply LRTClosToFromClosElem.
  - apply LRTClosToFromClosElem.
  - reflexivity.
  - etransitivity; [ apply (fmapMax2Eq (F:=F)) | ].
    + apply LRTArgMaxInvInc.
    + apply LRTArgMaxInvInc.
    + rewrite fmap2Comp.
      etransitivity; [ | apply (fmap2Id (F:=F)) ].
      apply (fmap2Proper (F:=F)); [ | | reflexivity ];
        repeat intro; subst x; [ apply IHargTp1 | apply IHargTp2 ].
  - destruct arg. simpl. rewrite H. reflexivity.
Qed.


Definition LRTArgHead stk lrt := LRTClosHead (LRTArg stk) lrt.

Definition LRTArgHeadMax stk lrt :
  LRTArgHead stk lrt -> { lvl & LRTArgHeadLvl stk lrt lvl } :=
  match lrt return LRTArgHead stk lrt -> { lvl & LRTArgHeadLvl stk lrt lvl } with
  | LRT_SpecM R => fun bot => match bot with end
  | LRT_FunDep A B => fun u => existT _ 0 u
  | LRT_FunClos A B => fun arg => LRTArgMax stk _ arg
  | LRT_Type A => fun bot => match bot with end
  | LRT_BinOp F A B => fun bot => match bot with end
  | LRT_Sigma A B => fun bot => match bot with end
  end.

Definition LRTArgHeadMaxInv stk lrt lvl :
  LRTArgHeadLvl stk lrt lvl -> LRTArgHead stk lrt :=
  match lrt return LRTArgHeadLvl stk lrt lvl -> LRTArgHead stk lrt with
  | LRT_SpecM R => fun bot => match bot with end
  | LRT_FunDep A B => fun u => u
  | LRT_FunClos A B => fun arg => LRTArgMaxInv stk A lvl arg
  | LRT_Type A => fun bot => match bot with end
  | LRT_BinOp F A B => fun bot => match bot with end
  | LRT_Sigma A B => fun bot => match bot with end
  end.

Lemma LRTArgHeadMaxInvInc stk lrt lvl (arg : LRTArgHeadLvl stk lrt lvl) :
  LRTArgHeadMaxInv stk lrt lvl arg
  = LRTArgHeadMaxInv stk lrt (S lvl) (LRTArgHeadLvlInc stk lrt lvl arg).
Proof.
  destruct lrt; try reflexivity; try destruct arg.
  apply LRTArgMaxInvInc.
Qed.

Lemma LRTArgHeadMaxInvEq stk lrt arg :
  LRTArgHeadMaxInv stk lrt (projT1 (LRTArgHeadMax stk lrt arg))
    (projT2 (LRTArgHeadMax stk lrt arg))
  = arg.
Proof.
  revert arg; destruct lrt; intros; simpl; try reflexivity; try destruct arg.
  apply LRTArgMaxInvEq.
Qed.


Definition LRTClosArgs stk n lrt dargs : Type@{entree_u} :=
  LRTClosArgsF (LRTArgF (LRTClos stk)) n lrt dargs.

Fixpoint LRTClosArgsMax stk n lrt :
  forall dargs, LRTClosArgs stk n lrt dargs ->
                { lvl & LRTClosArgsLvl stk n lrt lvl dargs } :=
  match n return forall dargs, LRTClosArgs stk n lrt dargs ->
                               { lvl & LRTClosArgsLvl stk n lrt lvl dargs } with
  | 0 => fun _ u => existT _ 0 u
  | S n' =>
      fun dargs cargs =>
        levelCombine
          (fun lvl => LRTClosArgsLvl stk n' lrt lvl (projT1 dargs))
          (fun lvl => LRTArgHeadLvl stk _ lvl)
          (fun lvl => LRTClosArgsLvl stk (S n') lrt lvl dargs)
          (fun lvl => LRTClosArgsLvlInc stk n' _ lvl (projT1 dargs))
          (fun lvl => LRTArgHeadLvlInc stk _ lvl)
          (fun n a b => (a, b))
          (LRTClosArgsMax stk n' lrt (projT1 dargs) (fst cargs))
          (LRTArgHeadMax stk _ (snd cargs))
  end.

Fixpoint LRTClosArgsMaxInv stk n lrt lvl :
  forall dargs, LRTClosArgsLvl stk n lrt lvl dargs ->
                LRTClosArgs stk n lrt dargs :=
  match n return forall dargs, LRTClosArgsLvl stk n lrt lvl dargs ->
                               LRTClosArgs stk n lrt dargs with
  | 0 => fun _ u => u
  | S n' =>
      fun dargs cargs =>
        (LRTClosArgsMaxInv stk n' lrt lvl (projT1 dargs) (fst cargs),
          LRTArgHeadMaxInv stk _ lvl (snd cargs))
  end.

Lemma LRTClosArgsMaxInvInc stk n lrt lvl dargs cargs :
  LRTClosArgsMaxInv stk n lrt lvl dargs cargs
  = LRTClosArgsMaxInv stk n lrt (S lvl) dargs
      (LRTClosArgsLvlInc stk n lrt lvl dargs cargs).
Proof.
  revert lrt dargs cargs; induction n; intros.
  - reflexivity.
  - simpl. f_equal; [ apply IHn | apply LRTArgHeadMaxInvInc ].
Qed.

Lemma LRTClosArgsMaxInvEq stk n lrt dargs cargs :
  LRTClosArgsMaxInv stk n lrt
    (projT1 (LRTClosArgsMax stk n lrt dargs cargs))
    dargs
    (projT2 (LRTClosArgsMax stk n lrt dargs cargs)) =
    cargs.
Proof.
  revert lrt dargs cargs; induction n; intros.
  - reflexivity.
  - destruct cargs. simpl. f_equal.
    + rewrite (elimLevelMaxR _ _ _ _ _
                 (fun lvl cargs =>
                    LRTClosArgsMaxInv stk n _ lvl (projT1 dargs) cargs));
        [ apply IHn | intros; apply LRTClosArgsMaxInvInc ].
    + rewrite elimLevelMaxL;
        [ apply LRTArgHeadMaxInvEq | intros; apply LRTArgHeadMaxInvInc ].
Qed.


Definition applyLRTClos stk lrt (clos: LRTClos stk lrt)
  (darg: LRTDepHead lrt) (carg: LRTArgHead stk lrt)
  : LRTClos stk (LRTTail lrt darg) :=
  levelCombine
    (LRTClosLvl stk lrt)
    (LRTArgHeadLvl stk lrt)
    (LRTClosLvl stk (LRTTail lrt darg))
    (LRTClosLvlInc stk lrt)
    (LRTArgHeadLvlInc stk lrt)
    (fun lvl clos' carg' => applyLRTClosLvl stk lrt lvl clos' darg carg')
    clos
    (LRTArgHeadMax stk lrt carg).

Definition applyLRTClosDep stk A B (clos: LRTClos stk (LRT_FunDep A B)) (a:A)
  : LRTClos stk (B a) := applyLRTClos stk (LRT_FunDep A B) clos a tt.

Definition applyLRTClosClos stk A B (clos: LRTClos stk (LRT_FunClos A B))
  (arg: LRTArg stk A) : LRTClos stk B := applyLRTClos stk (LRT_FunClos A B) clos tt arg.

Fixpoint applyLRTClosNRet stk n lrt : Type@{entree_u} :=
  match n with
  | 0 => LRTClos stk lrt
  | S n' =>
      match lrt with
      | LRT_SpecM R => void -> void
      | LRT_FunDep A B => forall a:A, applyLRTClosNRet stk n' (B a)
      | LRT_FunClos A B => LRTArg stk A -> applyLRTClosNRet stk n' B
      | LRT_Type A => void -> void
      | LRT_BinOp F A B => void -> void
      | LRT_Sigma A B => void -> void
      end
  end.

Fixpoint applyLRTClosN stk n lrt : LRTClos stk lrt -> applyLRTClosNRet stk n lrt :=
  match n return LRTClos stk lrt -> applyLRTClosNRet stk n lrt with
  | 0 => fun clos => clos
  | S n' =>
      match lrt return LRTClos stk lrt -> applyLRTClosNRet stk (S n') lrt with
      | LRT_SpecM R => fun _ bot => bot
      | LRT_FunDep A B => fun clos a =>
                            applyLRTClosN stk n' (B a) (applyLRTClosDep stk A B clos a)
      | LRT_FunClos A B => fun clos arg =>
                             applyLRTClosN stk n' B (applyLRTClosClos stk A B clos arg)
      | LRT_Type A => fun _ bot => bot
      | LRT_BinOp F A B => fun _ bot => bot
      | LRT_Sigma A B => fun _ bot => bot
      end
  end.


(**
 ** Complete lists of input arguments to corecursive functions
 **)

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


Definition LRTInputCons stk lrt :
  forall darg:LRTDepHead lrt, LRTClosHead (LRTArgF (LRTClos stk)) lrt ->
                              LRTInput stk (LRTTail lrt darg) ->
                              LRTInput stk lrt :=
  match lrt return forall darg, LRTClosHead (LRTArgF (LRTClos stk)) lrt ->
                                LRTInput stk (LRTTail lrt darg) ->
                                LRTInput stk lrt with
  | LRT_SpecM R => fun bot => match bot with end
  | LRT_FunDep A B => fun a _ inps => existT _ a inps
  | LRT_FunClos A B => fun _ arg inps => (arg, inps)
  | LRT_Type A => fun bot => match bot with end
  | LRT_BinOp F A B => fun bot => match bot with end
  | LRT_Sigma A B => fun bot => match bot with end
  end.

Lemma LRTInputConsOut stk lrt darg carg inps :
  LRTOutput stk lrt (LRTInputCons stk lrt darg carg inps) =
    LRTOutput stk _ inps.
Proof.
  destruct lrt; try destruct darg; reflexivity.
Qed.

Fixpoint LRTArgsToInput stk n lrt :
  forall dargs, LRTClosArgs stk n lrt dargs ->
                LRTInput stk (LRTDepArgsOut n lrt dargs) -> LRTInput stk lrt :=
  match n return forall dargs, LRTClosArgs stk n lrt dargs ->
                               LRTInput stk (LRTDepArgsOut n lrt dargs) ->
                               LRTInput stk lrt
  with
  | 0 => fun _ _ inps => inps
  | S n' =>
      fun dargs cargs inps =>
        LRTArgsToInput stk n' _ (projT1 dargs) (fst cargs)
          (LRTInputCons stk _ (projT2 dargs) (snd cargs) inps)
  end.

Lemma LRTArgsToInputOut stk n lrt dargs cargs inps :
  LRTOutput stk lrt (LRTArgsToInput stk n lrt dargs cargs inps) =
    LRTOutput stk _ inps.
Proof.
  revert dargs cargs inps; induction n; [ reflexivity | ]; intros.
  etransitivity; [ apply IHn | apply LRTInputConsOut ].
Qed.


(**
 ** N-ary functions over LetRecTypes
 **)

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


(**
 ** Calls to an arbitrary corecursive function in the stack
 **)

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

Definition LRTClosToCall stk R (clos: LRTClos stk (LRT_SpecM R)) : StackCall stk :=
  StackCallOfArgs stk (lrtClosNum _ _ _ (projT2 clos))
    (LRTArgsToInput stk
       (lrtClosNumArgs _ _ _ (projT2 clos))
       (nthLRT stk (lrtClosNum _ _ _ (projT2 clos)))
       (lrtClosDepArgs _ _ _ (projT2 clos))
       (LRTClosArgsMaxInv _ _ _ _ _ (lrtClosClosArgs _ _ _ (projT2 clos)))
       (eq_rect (LRT_SpecM R) (LRTInput stk) tt _ (eq_sym (lrtClosLRTEq _ _ _ (projT2 clos))))).

Lemma castLRTOutput stk lrt1 lrt2 (inps: LRTInput stk lrt2) (e: lrt1 = lrt2) :
  LRTOutput stk lrt1 (eq_rect lrt2 (LRTInput stk) inps lrt1 (eq_sym e)) = LRTOutput stk lrt2 inps.
Proof.
  destruct e. reflexivity.
Qed.

Lemma LRTClosToCallRet stk R clos :
  StackCallRet stk (LRTClosToCall stk R clos) = LRTArg stk R.
Proof.
  simpl. rewrite LRTArgsToInputOut. apply castLRTOutput.
Qed.


(**
 ** EncodingType and ReSum instances for defining SpecM
 **)

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


(**
 ** The SpecM monad
 **)

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

Definition CallS {E stk R} (clos: LRTClos stk (LRT_SpecM R))
  : SpecM E stk (LRTArg stk R) :=
  eq_rect
    (StackCallRet stk (LRTClosToCall stk R clos))
    (SpecM E stk)
    (trigger (LRTClosToCall stk R clos))
    (LRTArg stk R)
    (LRTClosToCallRet stk R clos).


(**
 ** Defining MultiFixS
 **)

(* A monadic function whose type is described by the encoding lrt *)
Definition SpecFun E stack lrt : Type@{entree_u} :=
  lrtPi stack lrt (fun args => SpecM E stack (LRTOutput _ lrt args)).

(* A trivially inhabited "default" SpecFun of type default_lrt *)
Definition defaultSpecFun E stack : SpecFun E stack default_lrt :=
  fun (v:void) => match v with end.

(* A dependent pair of an LRT and a SpecFun with that LRT *)
Definition SpecFunSig E stack : Type@{lrt_u} :=
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


(**
 ** Stack Inclusions
 **)

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


(**
 ** Stack-polymorphic function tuples
 **)

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


(**
 ** Specification Definitions
 **)

(* A "spec definition" represents a definition of a SpecM monadic function via
LetRecS over a tuple of recursive function bodies *)
Record SpecDef E lrt : Type@{lrt_u} :=
  { defStack : FunStack;
    defFuns : PolyStackTuple E defStack defStack;
    defBody : PolySpecFun E defStack lrt }.

(* A trivial spec definition *)
(* FIXME: why does this need to be in Program? *)
Program Definition defaultSpecDef E : SpecDef E default_lrt :=
  {|
    defStack := pnil;
    defFuns := fun _ _ => tt;
    defBody := fun _ _ (x:void) => match x with end;
  |}.

(* Complete a SpecDef to a SpecM computation *)
Definition completeSpecDef E lrt (d : SpecDef E lrt)
  (args : LRTInput (defStack E lrt d) lrt) :
  SpecM E pnil (LRTOutput _ _ args) :=
  LetRecS E _ (defStack _ _ d)
    (defFuns _ _ d (defStack _ _ d) (reflStackIncl _))
    (lrtApply _ _ _ (defBody _ _ d (defStack _ _ d) (reflStackIncl _)) args).

(* A list of spec imports with the given LetRecTypes *)
Definition impsList E imps_lrts : Type@{lrt_u} := mapTuple (SpecDef E) imps_lrts.

(* Build the concatenated FunStack for a list of imported spec defs *)
Fixpoint impsStack E imps_lrts : impsList E imps_lrts -> FunStack :=
  match imps_lrts return impsList E imps_lrts -> FunStack with
  | pnil => fun _ => pnil
  | pcons imp_lrt imps_lrts' =>
      fun imps => papp (defStack _ _ (fst imps)) (impsStack E imps_lrts' (snd imps))
  end.

(* Build the list of recursive functions for a list of imported spec defs *)
Fixpoint impsFuns E imps_lrts :
  forall imps, PolyStackTuple E (impsStack E imps_lrts imps)
                 (impsStack E imps_lrts imps) :=
  match imps_lrts return forall imps, PolyStackTuple E (impsStack E imps_lrts imps)
                                        (impsStack E imps_lrts imps) with
  | pnil => fun _ _ _ => tt
  | pcons lrt imps_lrts' =>
      fun imps =>
        appPolyStackTuple _ _ _ _
          (inclPolyStackTuple _ _ _ _
             (weakenRightStackIncl _ _)
             (defFuns _ _ (fst imps)))
          (inclPolyStackTuple _ _ _ _
             (weakenLeftStackIncl _ _)
             (impsFuns E imps_lrts' (snd imps)))
  end.

(* The combined function stack for defineSpec *)
Definition defineSpecStack E stk imps_lrts (imps: impsList E imps_lrts) : FunStack :=
  papp stk (impsStack E imps_lrts imps).

(* Get the nth spec import from an import list *)
Definition nthImport E imps_lrts (imps: impsList E imps_lrts) n
  : SpecDef E (nthLRT imps_lrts n) :=
  nthProjDefault (SpecDef E) default_lrt (defaultSpecDef E) imps_lrts n imps.

(* Build a stackIncl from the stack of an import to an impsStack containing it *)
Fixpoint nthImpInclImpStack E imps_lrts n :
  forall imps, stackIncl (defStack E _ (nthImport E imps_lrts imps n))
                 (impsStack E imps_lrts imps) :=
  match imps_lrts return forall imps, stackIncl (defStack E _ (nthImport E imps_lrts imps n))
                                        (impsStack E imps_lrts imps) with
  | pnil => fun _ => nilStackIncl _
  | pcons lrt imps_lrts' =>
      match n return forall imps, stackIncl (defStack E _ (nthImport E _ imps n))
                                    (impsStack E (pcons lrt imps_lrts') imps) with
      | 0 => fun _ => weakenRightStackIncl _ _
      | S n' => fun imps =>
                  compStackIncl (nthImpInclImpStack E imps_lrts' n' (snd imps))
                    (weakenLeftStackIncl _ _)
      end
  end.

(* Build a stackIncl from the stack of an import to that of a spec that imports it *)
Definition nthImpIncl E stk imps_lrts imps n :
  stackIncl (defStack E _ (nthImport E imps_lrts imps n))
    (defineSpecStack E stk imps_lrts imps) :=
  compStackIncl (nthImpInclImpStack E imps_lrts n imps) (weakenLeftStackIncl _ _).

(* Define a spec from: a list of imported spec definitions; a tuple of
recursively-defined functions; and a body that can call into either *)
Definition defineSpec E stk imps_lrts lrt
  (imps : impsList E imps_lrts)
  (recs : PolyStackTuple E (defineSpecStack E stk imps_lrts imps) stk)
  (body : PolySpecFun E (defineSpecStack E stk imps_lrts imps) lrt) : SpecDef E lrt :=
  {|
    defStack := defineSpecStack E stk imps_lrts imps;
    defFuns :=
      appPolyStackTuple _ _ _ _
        recs (inclPolyStackTuple _ _ _ _
                (weakenLeftStackIncl _ _) (impsFuns E imps_lrts imps));
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

(* The stack inclusion from the "local" stack to the defStack of a SpecDef *)
Definition localIncl E stk imps_lrts imps
  : stackIncl stk (defineSpecStack E stk imps_lrts imps) :=
  weakenRightStackIncl _ _.

(* Build a closure using a stackIncl *)
Definition mkLRTClosIncl stk1 stk2 (incl : stackIncl stk1 stk2) n
  : LRTClos stk2 (nthLRT stk1 n) :=
  existT _ 0
         {|
           lrtClosNum := applyIncl incl n;
           lrtClosNumArgs := 0;
           lrtClosDepArgs := LRTDepArgsNil _;
           lrtClosClosArgs := LRTClosArgsFNil _ _;
           lrtClosLRTEq := applyInclEq incl n;
         |}.

(* Build a closure for a corecursive function that is local to the current def *)
Definition mkLocalLRTClos E stk imps_lrts imps stk'
  (incl: stackIncl (defineSpecStack E stk imps_lrts imps) stk') n
  : LRTClos stk' (nthLRT stk n) :=
  mkLRTClosIncl stk stk' (compStackIncl (localIncl E stk imps_lrts imps) incl) n.

(* Call the body of the nth import *)
Definition callNthImportS E stk imps_lrts imps stk'
  (incl: stackIncl (defineSpecStack E stk imps_lrts imps) stk') n
  : SpecFun E stk' (nthLRT imps_lrts n) :=
  defBody _ _ (nthImport E imps_lrts imps n) stk'
    (compStackIncl (nthImpIncl E stk imps_lrts imps n) incl).

(*
FIXME HERE:
- Define lrtProp and lrtSatisfies
- Prove that lrtSatisfies is preserved by application
*)


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


(**
 ** Notations in terms of the SpecM combinators
 **)

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


(**
 ** Interpreting SpecM computations in the state monad
 **)

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
