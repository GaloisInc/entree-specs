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
     Strings.String
     Lists.List
.

From Paco Require Import paco.

Local Open Scope entree_scope.
Local Open Scope list_scope.

Import Monads.


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


(** Finite binary functors **)

(* A finite binary functor is a functor that intuitively contains finitely many
elements of the types in its arguments *)
Class FinBinFunctor (F : Type@{entree_u} -> Type@{entree_u} -> Type@{entree_u}) :=
  { finBinFmap : forall A B C D, (A -> B) -> (C -> D) -> F A C -> F B D;
    finBinMax : forall (A B : nat -> Type@{entree_u}),
      (forall n, A n -> A (S n)) -> (forall n, B n -> B (S n)) ->
      F ({ n:nat & A n}) ({ n:nat & B n}) ->
      { n & F (A n) (B n) } }.

(* The constant functor is a finite binary functor *)
#[global]
Instance Const_FinBinFunctor T : FinBinFunctor (fun _ _ => T) :=
  {|
    finBinFmap := fun _ _ _ _ f g (t:T) => t;
    finBinMax := fun A B incA incB (t:T) => existT _ 0 t
  |}.

(* Finite binary functors compose *)
#[global]
Instance Compose_FinBinFunctor F G H
  `{FinBinFunctor F} `{FinBinFunctor G} `{FinBinFunctor H}
  : FinBinFunctor (fun A B => F (G A B) (H A B)) :=
  {|
    finBinFmap := fun A B C D f g (x:F (G A C) (H A C)) =>
                    finBinFmap (G A C) (G B D) (H A C) (H B D)
                               (finBinFmap A B C D f g)
                               (finBinFmap A B C D f g) x;
    finBinMax :=
      fun A B incA incB x =>
        finBinMax
          (F:=F)
          (fun n => G (A n) (B n)) (fun n => H (A n) (B n))
          (fun n =>
             finBinFmap (F:=G) (A n) (A (S n)) (B n) (B (S n)) (incA n) (incB n))
          (fun n =>
             finBinFmap (F:=H) (A n) (A (S n)) (B n) (B (S n)) (incA n) (incB n))
          (finBinFmap
             (F:=F)
             (G { n & A n} { n & B n}) { n & G (A n) (B n) }
             (H { n & A n} { n & B n}) { n & H (A n) (B n) }
             (finBinMax A B incA incB)
             (finBinMax A B incA incB)
             x)
  |}.

Fixpoint levelAdd (A : nat -> Type@{entree_u}) (incA : forall n, A n -> A (S n))
  n m (a : A n) : A (m + n) :=
  match m return A (m + n) with
  | 0 => a
  | S m' => incA (m' + n) (levelAdd A incA n m' a)
  end.

Program Definition levelLift A incA n m (l: n <= m) (a:A n) : A m :=
  eq_rect _ A (levelAdd A incA n (m - n) a) _ _.
Next Obligation.
  rewrite PeanoNat.Nat.add_comm. apply Minus.le_plus_minus_r. assumption.
Defined.

Definition levelCombine (A B C : nat -> Type@{entree_u}) incA incB
  (f : forall n, A n -> B n -> C n) (a : { n & A n}) (b : { n & B n})
  : { n & C n } :=
  existT C
    (max (projT1 a) (projT1 b))
    (f (max (projT1 a) (projT1 b))
       (levelLift A incA (projT1 a) (max (projT1 a) (projT1 b))
          (PeanoNat.Nat.le_max_l (projT1 a) (projT1 b)) (projT2 a))
       (levelLift B incB (projT1 b) (max (projT1 a) (projT1 b))
          (PeanoNat.Nat.le_max_r (projT1 a) (projT1 b)) (projT2 b))).

Definition levelIncr (A : nat -> Type@{entree_u}) (a : { n & A (S n) }) :
  { n & A n } :=
  existT A (S (projT1 a)) (projT2 a).


(** An inductive description of recursive function types and their arguments **)

(* An encoded argument type for a recursive function and its arguments *)
Inductive LetRecType : Type@{entree_u + 1} :=
(* These three constructors represent functions of 0 or more arguments *)
| LRT_SpecM (R : LetRecType) : LetRecType
| LRT_FunDep (A : Type@{entree_u}) (rest : A -> LetRecType) : LetRecType
| LRT_FunClos (A : LetRecType) (rest : LetRecType) : LetRecType
(* These constructors represent the argument types used in functions *)
| LRT_Unit : LetRecType
| LRT_BinOp F `{FinBinFunctor F} (A B : LetRecType) : LetRecType
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
      finBinFmap _ _ _ _ (LRTArgLvlIncr stk A lvl) (LRTArgLvlIncr stk B lvl)
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
        finBinMax (LRTArgLvl stk A) (LRTArgLvl stk B)
          (LRTArgLvlIncr stk A) (LRTArgLvlIncr stk B)
          (finBinFmap _ _ _ _ (LRTArgMax stk A) (LRTArgMax stk B) x)
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



(* Compute a dependent tuple type of all the inputs of a LetRecType, i.e.,
   return the type { x:A & { y:B & ... { z:C & unit } ...}} from a LetRecType
   that represents forall a b c..., SpecM ... (R a b c ...). A LetRectype that
   is not a function type just becomes the void type. *)
Fixpoint LRTInput stack lrt : Type@{entree_u} :=
  match lrt with
  | LRT_SpecM _ => unit
  | LRT_FunDep A rest => {a : A & LRTInput stack (rest a) }
  | LRT_FunClos A rest => LRTArg stack A * LRTInput stack rest
  | _ => void
  end.

(* Compute the output type (R a b c ...) from a LetRecType that represents
   forall a b c..., SpecM ... (R a b c ...) and a dependent tuple of arguments
   to a function of that type *)
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
