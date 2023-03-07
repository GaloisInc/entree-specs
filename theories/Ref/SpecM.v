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
     Strings.String
     Lists.List
.

From Paco Require Import paco.

Local Open Scope entree_scope.
Local Open Scope list_scope.

Import Monads.


(* Examples of higher-order functions we want to write (but without monadic types) *)
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


(** Helper definitions **)

Polymorphic Inductive plist@{u} (A : Type@{u}) :=
| pnil : plist A
| pcons : A -> plist A -> plist A.
Arguments pnil {A}.
Arguments pcons {A} _ _.

Polymorphic Fixpoint plength@{u} {A : Type@{u}} (xs : plist A) : nat :=
  match xs with
  | pnil => 0
  | pcons _ xs' => S (plength xs')
  end.


Polymorphic Fixpoint pmap@{u} {A B : Type@{u}} (f : A -> B) (xs : plist A) : plist B :=
  match xs with
  | pnil => pnil
  | pcons x xs' => pcons (f x) (pmap f xs')
  end.

Polymorphic Fixpoint papp@{u} {A : Type@{u}} (xs ys : plist A) : plist A :=
  match xs with
  | pnil => ys
  | pcons x xs' => pcons x (papp xs' ys)
  end.

(* FIXME: doesn't work!
Polymorphic Fixpoint pconcat@{u} {A : Type@{u}} (xss : plist (plist A)) : plist A :=
  match xss with
  | pnil => pnil
  | pcons xs xss' => papp xs (pconcat xss')
  end.
*)

Polymorphic Definition pconcat@{u} {A : Type@{u}} (xss : plist (plist A)) : plist A :=
  plist_rect@{u u} (plist A) (fun _ => plist A) pnil
    (fun xs _ yss => papp xs yss) xss.


(* A version of nth_default that does primary recursion on the list *)
Fixpoint nth_default' {A} (d : A) (l : plist A) n : A :=
  match l with
  | pnil => d
  | pcons x l' => match n with
                  | 0 => x
                  | S n' => nth_default' d l' n'
                  end
  end.

(* If an index n is less then the length of the first list of an append, then
the nth element of the append is the nth element of the first list *)
Lemma nth_default'_app_left {A} (d:A) l1 l2 n :
  n < plength l1 -> nth_default' d (papp l1 l2) n = nth_default' d l1 n.
Proof.
  revert n; induction l1; intros.
  - inversion H.
  - destruct n; [ reflexivity | ]. simpl.
    apply IHl1. simpl in H. apply Lt.lt_S_n. assumption.
Qed.

Lemma nth_default'_app_right {A} (d:A) l1 l2 n :
  nth_default' d (papp l1 l2) (plength l1 + n) = nth_default' d l2 n.
Proof.
  revert n; induction l1; intros.
  - reflexivity.
  - apply IHl1.
Qed.


(* Build the right-nested tuple type of a list of types formed by mapping a
function across a list *)
Fixpoint mapTuple@{u v} {T:Type@{v}} (f : T -> Type@{u}) (xs : plist T) : Type@{u} :=
  match xs with
  | pnil => unit
  | pcons x xs' => f x * mapTuple f xs'
  end.

(* Append two mapTuple tuples *)
Fixpoint appMapTuple@{u v} {T:Type@{v}} (f : T -> Type@{u}) (xs ys : plist T) :
  mapTuple f xs -> mapTuple f ys -> mapTuple f (papp xs ys) :=
  match xs return mapTuple f xs -> mapTuple f ys -> mapTuple f (papp xs ys) with
  | pnil => fun _ tup2 => tup2
  | pcons x xs' =>
      fun tup1 tup2 => (fst tup1, appMapTuple f xs' ys (snd tup1) tup2)
  end.

(* Project the nth element of a tupleOfTypes *)
Fixpoint nthProjDefault@{u v} {T:Type@{v}} (f : T -> Type@{u}) (dT:T) (d:f dT) xs
  : forall n, mapTuple f xs -> f (nth_default' dT xs n) :=
  match xs return forall n, mapTuple f xs -> f (nth_default' dT xs n) with
  | pnil => fun _ _ => d
  | pcons x xs' =>
      fun n =>
        match n return mapTuple f (pcons x xs') -> f (nth_default' dT (pcons x xs') n) with
        | 0 => fun tup => fst tup
        | S n' => fun tup => nthProjDefault f dT d xs' n' (snd tup)
        end
  end.

(* A specialized dependent pair of a type and decoding function for it *)
Polymorphic Record EncType@{u} : Type :=
  { EncType_type :> Type@{u};
    EncType_encodes : EncodingType EncType_type }.

Global Instance EncodingType_EncType (ET:EncType) : EncodingType ET :=
  EncType_encodes ET.


(** A new approach to LetRecType **)

(* An encoded argument type for a recursive function *)
Inductive LetRecType : Type@{entree_u + 1} :=
| LRT_Ret (R : LRTArgType) : LetRecType
| LRT_FunDep (A : Type@{entree_u}) (rest : A -> LetRecType) : LetRecType
| LRT_Fun (A : LRTArgType) (rest : LetRecType) : LetRecType
with LRTArgType : Type@{entree_u + 1} :=
| ArgType_Const (A : Type@{entree_u}) : LRTArgType
| ArgType_Prod (A B : LRTArgType) : LRTArgType
| ArgType_Sigma (A : Type@{entree_u}) (B : A -> LRTArgType) : LRTArgType
| ArgType_Fun (lrt : LetRecType) : LRTArgType
.

(* A FunStack is a list of LetRecTypes representing all of the functions bound
   by multiFixS that are currently in scope *)
Definition FunStack := plist LetRecType.

(* A trivially inhabited "default" LetRecType *)
Definition default_lrt : LetRecType :=
  LRT_FunDep void (fun _ => LRT_Ret (ArgType_Const void)).

(* Get the nth element of a FunStack list, or void -> void if n is too big *)
Definition nthLRT (frame : FunStack) n : LetRecType :=
  nth_default' default_lrt frame n.

(* A partial application of a function of a LetRecType lrt_in to some of its
FunDep arguments, resulting in LetRecType lrt_out *)
Fixpoint LRTDepApp (lrt_in lrt_out : LetRecType) : Type@{entree_u} :=
  (lrt_in = lrt_out) +
    match lrt_in with
    | LRT_FunDep A lrt_in' => { a:A & LRTDepApp (lrt_in' a) lrt_out  }
    | LRT_Ret _ => False
    | LRT_Fun _ _ => False
    end.

(* An argument to a recursive function call, which is a decodeing of the
LRTArgType to its corresponding Coq type except that functions are just natural
numbers that choose functions in the current function stack *)
Fixpoint LRTArg (stack : FunStack) (argTp : LRTArgType) : Type@{entree_u} :=
  match argTp with
  | ArgType_Const A => A
  | ArgType_Prod A B => LRTArg stack A * LRTArg stack B
  | ArgType_Sigma A B => { x:A & LRTArg stack (B x) }
  | ArgType_Fun lrt => { n:nat & LRTDepApp (nthLRT stack n) lrt }
  end.

(* Compute a dependent tuple type of all the inputs of a LetRecType, i.e.,
   return the type { x:A & { y:B & ... { z:C & unit } ...}} from a LetRecType
   that represents forall a b c..., SpecM ... (R a b c ...) *)
Fixpoint LRTInput stack lrt : Type@{entree_u} :=
  match lrt with
  | LRT_Ret _ => unit
  | LRT_FunDep A rest => {a : A & LRTInput stack (rest a) }
  | LRT_Fun A rest => LRTArg stack A * LRTInput stack rest
  end.

(* Compute the output type (R a b c ...) from a LetRecType that represents
   forall a b c..., SpecM ... (R a b c ...) and a dependent tuple of arguments
   to a function of that type *)
Fixpoint LRTOutput stack lrt : EncodingType (LRTInput stack lrt) :=
  match lrt with
  | LRT_Ret R => fun _ => LRTArg stack R
  | LRT_FunDep A rest => fun args =>
                           let '(existT _ a args') := args in
                           LRTOutput stack (rest a) args'
  | LRT_Fun A rest => fun args => LRTOutput stack rest (snd args)
  end.

(* Build the type forall a b c ..., F (a, (b, (c, ...))) for an arbitrary type
   function F over an LRTInput *)
Fixpoint lrtPi stack lrt : (LRTInput stack lrt -> Type) -> Type :=
  match lrt return (LRTInput stack lrt -> Type) -> Type with
  | LRT_Ret _ => fun F => F tt
  | LRT_FunDep A lrtF =>
      fun F => forall a, lrtPi stack (lrtF a) (fun args => F (existT _ a args))
  | LRT_Fun A lrt' =>
      fun F => forall a, lrtPi stack lrt' (fun args => F (a, args))
  end.

(* Build an lrtPi function from a unary function on an LRTInput *)
Fixpoint lrtLambda stack lrt
  : forall (F : LRTInput stack lrt -> Type),
    (forall args, F args) -> lrtPi stack lrt F :=
  match lrt return
        forall (F : LRTInput stack lrt -> Type),
          (forall args, F args) -> lrtPi stack lrt F
  with
  | LRT_Ret _ => fun _ f => f tt
  | LRT_FunDep A lrtF =>
    fun F f a => lrtLambda stack (lrtF a)
                   (fun args => F (existT _ a args))
                   (fun args => f (existT _ a args))
  | LRT_Fun A lrt' =>
      fun F f a => lrtLambda stack lrt'
                     (fun args => F (a, args))
                     (fun args => f (a, args))
  end.

(* Apply an lrtPi function *)
Fixpoint lrtApply stack lrt
  : forall F, lrtPi stack lrt F -> forall args, F args :=
  match lrt return forall F, lrtPi stack lrt F -> forall args, F args with
  | LRT_Ret _ =>
    fun F f u => match u return F u with | tt => f end
  | LRT_FunDep A lrtF =>
    fun F f args =>
      match args return F args with
      | existT _ arg args' =>
        lrtApply stack (lrtF arg) (fun args' => F (existT _ arg args')) (f arg) args'
      end
  | LRT_Fun A lrt' =>
    fun F f args =>
      match args return F args with
      | (arg, args') =>
        lrtApply stack lrt' (fun args' => F (arg, args')) (f arg) args'
      end
  end.

(* A recursive call to one of the functions in a FunStack, specified by a
natural number n that picks a specific index in the FunStack along with a set of
arguments for that recursive call, relative to a given stack *)
(* FIXME: rename FrameCall -> StackCall *)
Inductive FrameCall stack : Type@{entree_u} :=
| FrameCallOfArgs n (args : LRTInput stack (nthLRT stack n)).

(* The return type for a FrameCall recursive call, using a specific M *)
Definition FrameCallRet stack (args: FrameCall stack) : Type@{entree_u} :=
  match args with
  | FrameCallOfArgs _ n args => LRTOutput stack (nthLRT stack n) args
  end.

Global Instance EncodingType_FrameCall stack : EncodingType (FrameCall stack) :=
  FrameCallRet stack.

(* Make a recursive call from its individual arguments *)
Definition mkFrameCall stack n
  : lrtPi stack (nthLRT stack n) (fun args => FrameCall stack) :=
  lrtLambda stack (nthLRT stack n) (fun _ => FrameCall stack) (FrameCallOfArgs stack n).

(* The error event type *)
Inductive ErrorE : Set :=
| mkErrorE : string -> ErrorE.

Global Instance EncodingType_ErrorE : EncodingType ErrorE := fun _ => void.

(* Create an event type for either an event in E or a recursive call in a stack
   Γ of recursive functions in scope *)
Definition FunStackE (E : EncType@{entree_u}) (stack : FunStack) : Type@{entree_u} :=
  FrameCall stack + (ErrorE + E).

Global Instance EncodingType_FunStackE E stack : EncodingType (FunStackE E stack) :=
  _.

Global Instance ReSum_FunStackE_E (E : EncType) (Γ : FunStack) : ReSum E (FunStackE E Γ) :=
  fun e => inr (inr e).

Global Instance ReSumRet_FunStackE_E (E : EncType) Γ :
  ReSumRet E (FunStackE E Γ) :=
  fun _ r => r.

Global Instance ReSum_FunStackE_Error (E : EncType) (Γ : FunStack) : ReSum ErrorE (FunStackE E Γ) :=
  fun e => inr (inl e).

Global Instance ReSumRet_FunStackE_Error (E : EncType) Γ :
  ReSumRet ErrorE (FunStackE E Γ) :=
  fun _ r => r.


(* Embed a call in the top level of the FunStack into a FunStackE *)
Global Instance ReSum_FrameCall_FunStackE (E : EncType) (stack : FunStack) :
  ReSum (FrameCall stack) (FunStackE E stack) :=
  fun args => inl args.

(* Map the return value for embedding a call in the top level to a FunStackE *)
Global Instance ReSumRet_FrameCall_FunStackE E stack :
  ReSumRet (FrameCall stack) (FunStackE E stack) :=
  fun _ r => r.

Global Instance EncodingType_LRTInput stack lrt :
  EncodingType (LRTInput stack lrt) := LRTOutput stack lrt.

(* ReSum instances for embedding the nth LRTInput into a FrameCall *)
Global Instance Resum_FunStackE_LRTInput E stack n :
  ReSum (LRTInput stack (nthLRT stack n)) (FunStackE E stack) :=
  fun args => resum (FrameCallOfArgs stack n args).

Global Instance FrameCall_ReSumRet E stack n :
  ReSumRet (LRTInput stack (nthLRT stack n)) (FunStackE E stack) :=
  fun _ r => r.

Global Instance ReSum_Error_E_FunStack (E : EncType) (stack : FunStack) :
  ReSum (SpecEvent (ErrorE + E)) (SpecEvent (FunStackE E stack)) :=
  fun e => match e with
           | Spec_vis e => Spec_vis (resum e)
           | Spec_forall T => Spec_forall T
           | Spec_exists T => Spec_exists T
           end.

Global Instance ReSumRet_Error_E_FunStack (E : EncType) (stack : FunStack) :
  ReSumRet (SpecEvent (ErrorE + E)) (SpecEvent (FunStackE E stack)) :=
  fun e =>
    match e with
    | Spec_vis e => fun x => resum_ret e x
    | Spec_forall T => fun x => x
    | Spec_exists T => fun x => x
    end.


(** Defining the SpecM monad **)

Definition SpecM (E:EncType) stack A : Type :=
  entree_spec (FunStackE E stack) A.

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
Definition TriggerS {E:EncType} {Γ} (e : E) : SpecM E Γ (encodes e) := trigger e.
Definition ErrorS {E} {Γ} A (str : string) : SpecM E Γ A :=
  bind (trigger (mkErrorE str)) (fun (x:void) => match x with end).

Global Instance SpecM_Monad {E} Γ : Monad (SpecM E Γ) :=
  {|
    ret := fun A a => RetS a;
    bind := fun A B m k => BindS m k;
  |}.

(* Create a recursive call to a function in the top-most using args *)
Definition CallS E stack (args : FrameCall stack) :
  SpecM E stack (FrameCallRet stack args) :=
  trigger (H2:=@SpecEventReSumRet _ _ _ _ _ _) args.

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
  | LRT_Ret R =>
      fun f da args =>
        match da with
        | inl e => (castCallFun E stack (LRT_Ret R) lrt_out e f) args
        | inr bot => match bot with end
        end
  | LRT_FunDep A lrtF =>
      fun f da args =>
        match da with
        | inl e => (castCallFun E stack _ lrt_out e f) args
        | inr da' =>
            applyDepApp E stack (lrtF (projT1 da')) lrt_out
                        (fun args' => f (existT _ (projT1 da') args'))
                        (projT2 da') args
        end
  | LRT_Fun A lrt' =>
      fun f da args =>
        match da with
        | inl e => (castCallFun E stack _ lrt_out e f) args
        | inr bot => match bot with end
        end
  end.

(* Apply an LRTArg of monadic type *)
Definition CallLRTArg E stack lrt (arg:LRTArg stack (ArgType_Fun lrt)) :
  lrtPi stack lrt (fun args => SpecM E stack (LRTOutput stack lrt args)) :=
  lrtLambda stack lrt _
    (fun args =>
       applyDepApp E stack _ _
         (trigger (H2:=@SpecEventReSumRet _ _ _ _ _ _))
         (projT2 arg) args).


(** Defining MultiFixS **)

(* The type of a function body in a recursive function frame *)
Definition FrameFun E stack lrt : Type@{entree_u} :=
  lrtPi stack lrt (fun args => SpecM E stack (LRTOutput _ lrt args)).

(* A right-nested tuple of a list of functions in a recursive function frame *)
Definition FrameTuple E stack : Type@{entree_u} :=
  mapTuple (FrameFun E stack) stack.

(* Get the nth function in a FrameTuple *)
Definition nthFrameTupleFun E stack n (funs : FrameTuple E stack) :
  FrameFun E stack (nthLRT stack n) :=
  nthProjDefault (FrameFun E stack) default_lrt
    (fun (v:void) => match v with end) _ n funs.

(* Apply a FrameTuple to a FrameCall to get a FrameCallRet *)
Definition applyFrameTuple E stack (funs : FrameTuple E stack)
           (call : FrameCall stack) : SpecM E stack (FrameCallRet stack call) :=
  match call return SpecM E stack (FrameCallRet stack call) with
  | FrameCallOfArgs _ n args =>
    lrtApply stack (nthLRT stack n) _ (nthFrameTupleFun _ stack n funs) args
  end.

(* Create a multi-way fixed point of a sequence of functions *)
Definition MultiFixS E stack (bodies : FrameTuple E stack) (call : FrameCall stack)
  : SpecM E pnil (FrameCallRet stack call) :=
  resumEntree (mrec_spec (applyFrameTuple E stack bodies) call).


(** Specification Definitions **)

(* A stack inclusion is a mapping from the indices of one stack to those of
another that preserves LetRecTypes. Note that this is not technically a relation
because the mapping itself matters. *)
Definition stackIncl (stk1 stk2 : FunStack) : Type :=
  { f : nat -> nat | forall n, nthLRT stk1 n = nthLRT stk2 (f n) }.

(* The trivially reflexive stack inclusion *)
Program Definition reflStackIncl stk : stackIncl stk stk :=
  fun n => n.

(* Compose two stack inclusions *)
Program Definition compStackIncl {stk1 stk2 stk3}
  (incl1 : stackIncl stk1 stk2) (incl2 : stackIncl stk2 stk3)
  : stackIncl stk1 stk3 :=
  fun n => incl2 (incl1 n).
Next Obligation.
Proof.
  rewrite (proj2_sig incl1). rewrite (proj2_sig incl2). reflexivity.
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
  destruct n0.
  - unfold nthLRT. rewrite nth_default'_app_left; [ | assumption ]. reflexivity.
  - unfold nthLRT. rewrite nth_default'_app_right.
    apply (proj2_sig incl).
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
  destruct n; [ reflexivity | ].
  unfold nthLRT. simpl. rewrite (proj2_sig incl). reflexivity.
Defined.

(* Prefix a stackIncl with a list of LetRecTypes that stay constant *)
Fixpoint prefixStackIncl pre stk1 stk2 (incl: stackIncl stk1 stk2)
  : stackIncl (papp pre stk1) (papp pre stk2) :=
  match pre return stackIncl (papp pre stk1) (papp pre stk2) with
  | pnil => incl
  | pcons lrt pre' =>
      consStackIncl lrt _ _ (prefixStackIncl pre' stk1 stk2 incl)
  end.


(* A FrameTuple that is polymorphic in its function stack, which defines
functions for all the defs that can call all the calls *)
Definition PolyFrameTuple E calls defs :=
  forall stack', stackIncl calls stack' -> mapTuple (FrameFun E stack') defs.

(* Append two PolyFrameTuples *)
Definition appPolyFrameTuple E calls defs1 defs2
  (pft1 : PolyFrameTuple E calls defs1)
  (pft2 : PolyFrameTuple E calls defs2)
  : PolyFrameTuple E calls (papp defs1 defs2) :=
  fun stack' incl =>
    appMapTuple _ defs1 defs2 (pft1 stack' incl) (pft2 stack' incl).

(* Apply a stackIncl to the calls list of a PolyFrameTuple *)
Definition inclPolyFrameTuple E calls1 calls2 defs
  (incl : stackIncl calls1 calls2)
  (pft : PolyFrameTuple E calls1 defs)
  : PolyFrameTuple E calls2 defs :=
  fun stack' incl' => pft stack' (compStackIncl incl incl').

(* A SpecDef represents a definition of a SpecM monadic function via MultiFixsS
as a FrameTuple plus an index into that FrameTuple *)
Record SpecDef E :=
  { SpecDef_stack : FunStack;
    SpecDef_bodies : PolyFrameTuple E SpecDef_stack SpecDef_stack;
    SpecDef_call : nat;
    SpecDef_callValid : SpecDef_call < plength SpecDef_stack }.

(* The output type of the main definition of a SpecDef *)
Definition SpecDefOut E (d : SpecDef E) : LetRecType :=
  nthLRT (SpecDef_stack _ d) (SpecDef_call _ d).


Program Fixpoint inclSpecDefCalls (ds : plist (SpecDef E)) :
  stackIncl (pmap (SpecDefOut E) ds) (pconcat (pmap (SpecDef_stack E) ds)) :=
  match ds return stackIncl (pmap (SpecDefOut E) ds)
                    (pconcat (pmap (SpecDef_stack E) ds)) with
  | pnil => reflStackIncl pnil
  | pcons d ds' =>


(* Complete a SpecDef to a SpecM computation *)
Definition completeSpecDef E (d : SpecDef E)
  (args : LRTInput (SpecDef_stack E d) (SpecDefOut E d)) :
  SpecM E pnil (LRTOutput _ _ args) :=
  MultiFixS E (SpecDef_stack _ d)
    (SpecDef_bodies _ d (SpecDef_stack _ d) (reflStackIncl _))
    (FrameCallOfArgs _ _ args).

(*
(* Call the nth recursive function in a SpecM computation *)
Definition callNth E stack n :
  lrtPi stack (nthLRT stack n) (fun args => SpecM E stack (LRTOutput _ _ args)) :=
  lrtLambda
    stack (nthLRT stack n)
    (fun args => SpecM E stack (LRTOutput _ _ args))
    (fun args => trigger args).

Definition callNthCast E stack n lrt (e : nthLRT stack n = lrt) :
  lrtPi stack lrt (fun args => SpecM E stack (LRTOutput _ _ args)) :=
  eq_rect (nthLRT stack n)
    (fun lrt' => lrtPi stack lrt' (fun args => SpecM E stack (LRTOutput _ _ args)))
    (callNth E stack n)
    lrt e.
*)

(* Build a SpecDef from a tuple of defs that can call into each other and into
any of a list of sub-definitions *)
Definition defineSpec E (subDefs : plist (SpecDef E)) (lrts : plist LetRecType)
  (defs : PolyFrameTuple E (papp lrts (pmap (SpecDefOut E) subDefs)) lrts)
  (n : nat) : SpecDef E :=
  {|
    SpecDef_stack := papp lrts (pconcat (pmap (SpecDef_stack E) subDefs));
    SpecDef_bodies :=
      fun stack' incl =>
    SpecDef_call := n; |}.


FIXME HERE: maybe we don't need LRTValue and friends?

(* A value of an LRTArgType *)
(* FIXME: figure out how to define MultiFixS using this LRTValueFun type... *)
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
  | LRT_Ret R => SpecM E stack (LRTValue E stack R)
  | LRT_FunDep A lrtF => forall a, LRTValueFun E stack (lrtF a)
  | LRT_Fun A lrt' => LRTArg stack A -> LRTValueFun E stack lrt'
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
               (FrameCallOfArgs _ (projT1 sig)
                  (applyDepApp stack _ _ (projT2 sig) args)))
  end
with
LRTArgFun2ValueFun E stack lrt : (forall args:LRTInput stack lrt,
                                     SpecM E stack (LRTOutput stack lrt args)) ->
                                 LRTValueFun E stack lrt :=
  match lrt return (forall args,
                    SpecM E stack (LRTOutput stack lrt args)) ->
                   LRTValueFun E stack lrt with
  | LRT_Ret R =>
      fun f => bind (f tt) (fun x => ret (LRTArg2Value E stack R x))
  | LRT_FunDep A lrt' =>
      fun f a =>
        LRTArgFun2ValueFun E stack (lrt' a) (fun args => f (existT _ a args))
  | LRT_Fun A lrt' =>
      fun f a =>
        LRTArgFun2ValueFun E stack lrt' (fun args => f (a, args))
  end.

FIXME: old stuff below

(* An element of an LRTArgType, which is either a decoding of the LRTArgType to
an actual Coq type or a recursive call of the given type in the frame *)
Fixpoint LRTArgTypeElem (M : Type@{entree_u} -> Type@{entree_u})
  (argTp : LRTArgType) : Type@{entree_u} :=
  match argTp with
  | ArgType_Const A => A
  | ArgType_Prod A B => LRTArgTypeElem M A * LRTArgTypeElem M B
  | ArgType_Sigma A B => { x:A & LRTArgTypeElem M (B x) }
  | ArgType_Arrow A B => LRTArgTypeElem M A -> LRTArgTypeElem M B
  | ArgType_Pi A B => forall x:A, LRTArgTypeElem M (B x)
  | ArgType_M A => M (LRTArgTypeElem M A)
  end.

(* The type of a recursive function *)
Inductive LetRecType : Type@{entree_u + 1} :=
| LRT_Ret (R : LRTArgType) : LetRecType
| LRT_FunDep (A : Type@{entree_u}) (rest : A -> LetRecType) : LetRecType
| LRT_Fun (A : LRTArgType) (rest : LetRecType) : LetRecType
.

(* Compute a dependent tuple type of all the inputs of a LetRecType, i.e.,
   return the type { x:A & { y:B & ... { z:C & unit } ...}} from a LetRecType
   that represents forall a b c..., SpecM ... (R a b c ...). The supplied type
   function M gives the interpretation of the ArgType_M type constructor. *)
Fixpoint LRTInput (M : Type@{entree_u} -> Type@{entree_u}) lrt : Type@{entree_u} :=
  match lrt with
  | LRT_Ret _ => unit
  | LRT_FunDep A rest => {a : A & LRTInput M (rest a) }
  | LRT_Fun A rest => LRTArgTypeElem M A * LRTInput M rest
  end.

(* Compute the output type (R a b c ...) from a LetRecType that represents
   forall a b c..., SpecM ... (R a b c ...) and a dependent tuple of arguments
   to a function of that type, using M for the ArgType_M type constructor *)
Fixpoint LRTOutput M lrt : EncodingType (LRTInput M lrt) :=
  match lrt with
  | LRT_Ret R => fun _ => LRTArgTypeElem M R
  | LRT_FunDep A rest => fun args =>
                           let '(existT _ a args') := args in
                           LRTOutput M (rest a) args'
  | LRT_Fun A rest => fun args => LRTOutput M rest (snd args)
  end.

(* Build the type forall a b c ..., F (a, (b, (c, ...))) for an arbitrary type
   function F over an LRTInput *)
Fixpoint lrtPi M lrt : (LRTInput M lrt -> Type) -> Type :=
  match lrt return (LRTInput M lrt -> Type) -> Type with
  | LRT_Ret _ => fun F => F tt
  | LRT_FunDep A lrtF =>
      fun F => forall a, lrtPi M (lrtF a) (fun args => F (existT _ a args))
  | LRT_Fun A lrt' =>
      fun F => forall a, lrtPi M lrt' (fun args => F (a, args))
  end.

(* Build an lrtPi function from a unary function on an LRTInput *)
Fixpoint lrtLambda M lrt
  : forall (F : LRTInput M lrt -> Type), (forall args, F args) -> lrtPi M lrt F :=
  match lrt return forall (F : LRTInput M lrt -> Type), (forall args, F args) ->
                                                        lrtPi M lrt F
  with
  | LRT_Ret _ => fun _ f => f tt
  | LRT_FunDep A lrtF =>
    fun F f a => lrtLambda M (lrtF a)
                   (fun args => F (existT _ a args))
                   (fun args => f (existT _ a args))
  | LRT_Fun A lrt' =>
      fun F f a => lrtLambda M lrt'
                     (fun args => F (a, args))
                     (fun args => f (a, args))
  end.

(* Apply an lrtPi function *)
Fixpoint lrtApply M lrt
  : forall F, lrtPi M lrt F -> forall args, F args :=
  match lrt return forall F, lrtPi M lrt F -> forall args, F args with
  | LRT_Ret _ =>
    fun F f u => match u return F u with | tt => f end
  | LRT_FunDep A lrtF =>
    fun F f args =>
      match args return F args with
      | existT _ arg args' =>
        lrtApply M (lrtF arg) (fun args' => F (existT _ arg args')) (f arg) args'
      end
  | LRT_Fun A lrt' =>
    fun F f args =>
      match args return F args with
      | (arg, args') =>
        lrtApply M lrt' (fun args' => F (arg, args')) (f arg) args'
      end
  end.

(* NOTE: it is straightforward to prove a beta rule for lrtApply lrtLambda, but
   that isn't really needed below *)


(** Frames, FrameCalls, and FunStackE **)

(* A recursive function frame is specified by a list of LetRecTypes *)
Definition RecFrame := list LetRecType.

(* Get the nth element of a RecFrame list, or void -> void if n is too big *)
Definition nthLRT (frame : RecFrame) n : LetRecType :=
  nth_default' (LRT_Fun (ArgType_Const void) (LRT_Ret (ArgType_Const void))) frame n.

(* A recursive call to one of the functions in a RecFrame, specified by a
natural number n that picks a specific index in the RecFrame along with a set of
arguments for that recursive call, using the given type function M as the
interpretation of the ArgType_M constructor *)
Inductive FrameCallH M frame : Type@{entree_u} :=
| FrameCallOfArgs n (args : LRTInput M (nthLRT frame n)).

(* The return type for a FrameCallH recursive call, using a specific M *)
Definition FrameCallHRet M frame (args: FrameCallH M frame) : Type@{entree_u} :=
  match args with
  | FrameCallOfArgs _ _ n args => LRTOutput M (nthLRT frame n) args
  end.

(* The type of a FrameCallH recursive call along with a FrameCallHRet function
that computes the return type of one of those recursive calls, but where the
arguments to the recursive call are at a specified "level". A level 0 frame call
is one whose higher-order arguments can only contain calls to monadic functions
of return type M0, while a level S lvl' call can contain higher-order arguments
with frame calls at level lvl' or below. *)
Fixpoint FrameCallLvlInOut (M0 : Type@{entree_u} -> Type@{entree_u}) frame lvl
  : EncType@{entree_u} :=
  match lvl with
  | 0 => Build_EncType (FrameCallH M0 frame) (FrameCallHRet M0 frame)
  | S lvl' =>
      let M := fun R =>
                 (M0 R +
                    { args:FrameCallLvlInOut M0 frame lvl'
                    | encodes args = R })%type in
      Build_EncType (FrameCallH M frame) (FrameCallHRet M frame)
  end.

(* A frame call at an arbitrary level, where M0 defines level 0 *)
Definition FrameCall (M0 : Type@{entree_u} -> Type@{entree_u}) frame :=
  { lvl & FrameCallLvlInOut M0 frame lvl }.

(* Compute the return type of a FrameCall *)
Definition FrameCallRet (M0 : Type@{entree_u} -> Type@{entree_u}) frame
                        (call : FrameCall M0 frame) : Type@{entree_u} :=
  encodes (projT2 call).

Global Instance EncodingType_FrameCall M0 frame : EncodingType (FrameCall M0 frame) :=
  FrameCallRet M0 frame.


(* A FunStack is a list of RecFrame representing all of the functions bound
    by multiFixS that are currently in scope *)
Definition FunStack := list RecFrame.

(* The error event type *)
Inductive ErrorE : Set :=
| mkErrorE : string -> ErrorE.

Global Instance EncodingType_ErrorE : EncodingType ErrorE := fun _ => void.

(* Create an event type for either an event in E or a recursive call in a stack
   Γ of recursive functions in scope *)
Fixpoint FunStackE (E : Type) `{EncodingType E} (stack : FunStack) : EncType@{entree_u} :=
  match stack with
  | nil => Build_EncType (ErrorE + E) _
  | frame :: stack' =>
      let M := fun R => entree_spec (FunStackE E stack') R in
      Build_EncType (FrameCall M frame + FunStackE E stack') _
  end.

(* Embed an underlying event into the FunStackE event type *)
Fixpoint FunStackE_embed_ev (E : Type) `{EncodingType E} Γ (e : ErrorE + E) : FunStackE E Γ :=
  match Γ return FunStackE E Γ with
  | nil => e
  | (_ :: Γ') => inr (FunStackE_embed_ev E Γ' e)
  end.

(* Map the output of a FunStackE event for an E to the output type of E *)
Fixpoint FunStackE_embed_ev_unmap (E : Type) `{EncodingType E} Γ e
  : encodes (FunStackE_embed_ev E Γ e) -> encodes e :=
  match Γ return encodes (FunStackE_embed_ev E Γ e) -> encodes e with
  | nil => fun o => o
  | (_ :: Γ') => FunStackE_embed_ev_unmap E Γ' e
  end.

Global Instance ReSum_FunStackE_E (E : Type) `{EncodingType E} (Γ : FunStack) : ReSum E (FunStackE E Γ) :=
  fun e => FunStackE_embed_ev E Γ (inr e).

Global Instance ReSumRet_FunStackE_E (E : Type) `{EncodingType E} Γ :
  ReSumRet E (FunStackE E Γ) :=
  fun e => FunStackE_embed_ev_unmap E Γ (inr e).

Global Instance ReSum_FunStackE_Error (E : Type) `{EncodingType E} (Γ : FunStack) : ReSum ErrorE (FunStackE E Γ) :=
  fun e => FunStackE_embed_ev E Γ (inl e).

Global Instance ReSumRet_FunStackE_Error (E : Type) `{EncodingType E} Γ :
  ReSumRet ErrorE (FunStackE E Γ) :=
  fun e => FunStackE_embed_ev_unmap E Γ (inl e).

Global Instance ReSum_cons_FunStack E `{EncodingType E} (stack : FunStack) frame :
  ReSum (SpecEvent (FunStackE E stack)) (SpecEvent (FunStackE E (frame :: stack))) :=
  fun e => match e with
           | Spec_vis e => Spec_vis (resum e)
           | Spec_forall T => Spec_forall T
           | Spec_exists T => Spec_exists T
           end.

Global Instance ReSumRet_nil_FunStack E `{EncodingType E} stack frame :
  ReSumRet (SpecEvent (FunStackE E stack)) (SpecEvent (FunStackE E (frame :: stack))) :=
  fun e =>
    match e return encodes (ReSum_cons_FunStack E stack frame e) -> encodes e with
    | Spec_vis e => fun x => resum_ret e x
    | Spec_forall T => fun x => x
    | Spec_exists T => fun x => x
    end.


(** The SpecM monad and associated operations **)

(* The SpecM monad is the entree_spec monad with FunStackE as the event type *)
Definition SpecM (E:EncType) stack A : Type@{entree_u} :=
  entree_spec (FunStackE E stack) A.

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
Definition TriggerS {E:EncType} {Γ} (e : E) : SpecM E Γ (encodes e) := trigger e.
Definition ErrorS {E} {Γ} A (str : string) : SpecM E Γ A :=
  bind (trigger (mkErrorE str)) (fun (x:void) => match x with end).

Global Instance SpecM_Monad {E} Γ : Monad (SpecM E Γ) :=
  {|
    ret := fun A a => RetS a;
    bind := fun A B m k => BindS m k;
  |}.

(* Cons a frame onto the stack of a SpecM computation *)
Definition consStackS E stack frame A (t:SpecM E stack A) : SpecM E (frame :: stack) A :=
  resumEntree t.


(** Making recursive calls **)

(* A FrameCall that calls into the topmost frame *)
Definition TopFrameCall (E:EncType) stack frame :=
  FrameCall (SpecM E stack) frame.

(* The return type of a TopFrameCall *)
Definition TopFrameCallRet (E:EncType) stack frame
  : TopFrameCall E stack frame -> Type :=
  FrameCallRet (SpecM E stack) frame.

(* Create a recursive call to a function in the top-most frame using args *)
Definition CallS E stack frame (args : TopFrameCall E stack frame) :
  SpecM E (frame :: stack) (TopFrameCallRet E stack frame args) :=
  trigger args.

FIXME HERE: how to define mkTopFrameCall to take in arguments which can have recursive calls to the same top frame?

(* Make a TopFrameCall from its individual arguments *)
Definition mkTopFrameCall E stack frame n
  : lrtPi (SpecM E stack) (nthLRT frame n) (fun args => TopFrameCall E stack frame) :=
  lrtLambda (SpecM E stack) (nthLRT frame n) (fun _ => TopFrameCall E stack frame) (FrameCallOfArgs _ frame n).


FIXME: update the below

(* Add a function type to the frame of a FrameCall *)
Definition consFrameCall {lrt frame} (call : FrameCall frame)
  : FrameCall (cons lrt frame) :=
  match call in FrameCall _ return FrameCall (cons lrt frame) with
  | FrameCallOfArgs _ n args => FrameCallOfArgs (cons lrt frame) (S n) args
  end.

(* The index of a FrameCall is always less than the length of the frame *)
Lemma FrameCallIndexLt frame call : @FrameCallIndex frame call < length frame.
Proof.
  destruct call.
  revert frame args; induction n; intros; destruct frame;
    try (destruct args; destruct x).
  - simpl. apply Lt.neq_0_lt. trivial.
  - simpl. apply Lt.lt_n_S. apply (IHn _ args).
Qed.

(* The return type for calling a recursive function in a RecFrame *)
Definition FrameCallRet frame (args: FrameCall frame) : Type@{entree_u} :=
  match args with
  | FrameCallOfArgs _ n args => LRTOutput (nthLRT frame n) args
  end.

Global Instance FrameCallRetEncoding lrt : EncodingType (FrameCall lrt) :=
  FrameCallRet lrt.

(* Make a recursive call from its individual arguments *)
Definition mkFrameCall (frame : RecFrame) n
  : lrtPi (nthLRT frame n) (fun args => FrameCall frame) :=
  lrtLambda (nthLRT frame n) (fun _ => FrameCall frame) (FrameCallOfArgs frame n).

(* ReSum instances for embedding the nth LRTInput into a FrameCall *)
Global Instance FrameCall_ReSum frame n :
  ReSum (LRTInput (nthLRT frame n)) (FrameCall frame) := FrameCallOfArgs frame n.
Global Instance FrameCall_ReSumRet frame n :
  ReSumRet (LRTInput (nthLRT frame n)) (FrameCall frame) :=
  fun _ r => r.

(* A FunStack is a list of RecFrame representing all of the functions bound
    by multiFixS that are currently in scope *)
Definition FunStack := list RecFrame.

(* The error event type *)
Inductive ErrorE : Set :=
| mkErrorE : string -> ErrorE.

Global Instance EncodingType_ErrorE : EncodingType ErrorE := fun _ => void.

(* Create an event type for either an event in E or a recursive call in a stack
   Γ of recursive functions in scope *)
Fixpoint FunStackE (E : Type) (Γ : FunStack) : Type@{entree_u} :=
  match Γ with
  | nil => ErrorE + E
  | frame :: Γ' => FrameCall frame + FunStackE E Γ'
  end.

(* Compute the output type for a FunStackE event *)
Fixpoint FunStackE_encodes (E : Type) `{EncodingType E} (Γ : FunStack) :
  FunStackE E Γ -> Type@{entree_u} :=
  match Γ return FunStackE E Γ -> Type with
  | nil => fun e => encodes e
  | frame :: Γ' => fun e => match e with
                            | inl args => FrameCallRet frame args
                            | inr args => FunStackE_encodes E Γ' args
                            end
  end.

Global Instance FunStackE_encodes' (E : Type) `{EncodingType E} (Γ : FunStack) : EncodingType (FunStackE E Γ) :=
  FunStackE_encodes E Γ.

(* Embed an underlying event into the FunStackE event type *)
Fixpoint FunStackE_embed_ev (E : Type) Γ (e : ErrorE + E) : FunStackE E Γ :=
  match Γ return FunStackE E Γ with
  | nil => e
  | (_ :: Γ') => inr (FunStackE_embed_ev E Γ' e)
  end.

(* Map the output of a FunStackE event for an E to the output type of E *)
Fixpoint FunStackE_embed_ev_unmap (E : Type) `{EncodingType E} Γ e
  : encodes (FunStackE_embed_ev E Γ e) -> encodes e :=
  match Γ return encodes (FunStackE_embed_ev E Γ e) -> encodes e with
  | nil => fun o => o
  | (_ :: Γ') => FunStackE_embed_ev_unmap E Γ' e
  end.

Global Instance ReSum_FunStackE_E (E : Type) (Γ : FunStack) : ReSum E (FunStackE E Γ) :=
  fun e => FunStackE_embed_ev E Γ (inr e).

Global Instance ReSumRet_FunStackE_E (E : Type) `{EncodingType E} Γ :
  ReSumRet E (FunStackE E Γ) :=
  fun e => FunStackE_embed_ev_unmap E Γ (inr e).

Global Instance ReSum_FunStackE_Error (E : Type) (Γ : FunStack) : ReSum ErrorE (FunStackE E Γ) :=
  fun e => FunStackE_embed_ev E Γ (inl e).

Global Instance ReSumRet_FunStackE_Error (E : Type) `{EncodingType E} Γ :
  ReSumRet ErrorE (FunStackE E Γ) :=
  fun e => FunStackE_embed_ev_unmap E Γ (inl e).

(* Get the nth RecFrame frame in a FunStack, returning the empty frame if n
   is too big *)
Definition nthFrame (Γ : FunStack) fnum : RecFrame :=
  nth_default' nil Γ fnum.

(* Embed a FrameCall for the fnum-th frame of a FunStack into FunStackE *)
(*
Fixpoint mkFunStackE E Γ fnum : FrameCall (nthFrame Γ fnum) -> FunStackE E Γ :=
  match Γ return FrameCall (nthFrame Γ fnum) -> FunStackE E Γ with
  | nil => fun x => match x with end
  | frame :: Γ' =>
    match fnum return FrameCall (nthFrame (frame :: Γ') fnum) ->
                      FunStackE E (frame :: Γ') with
    | 0 => fun args => inl args
    | S fnum' => fun args => inr (mkFunStackE E Γ' fnum' args)
    end
  end.

(* Embed an LRTInput for the nth function in the fnum-th frame of a FunStack
   into FunStackE *)
Definition mkFunStackE' E Γ fnum n
           (args:LRTInput (nthLRT (nthFrame Γ fnum) n)) : FunStackE E Γ :=
  mkFunStackE E Γ fnum (embedFrameCall _ n args).
*)

(* Embed a call in the top level of the FunStack into a FunStackE *)
Global Instance ReSum_LRTInput_FunStackE (E : Type) (Γ : FunStack) frame n :
  ReSum (LRTInput (nthLRT frame n)) (FunStackE E (frame :: Γ)) :=
  fun args => inl (FrameCallOfArgs frame n args).

(* Map the return value for embedding a call in the top level to a FunStackE *)
Global Instance ReSumRet_LRTInput_FunStackE (E : Type) `{EncodingType E} Γ frame n
  : ReSumRet (LRTInput (nthLRT frame n)) (FunStackE E (frame :: Γ)) :=
  fun args o => o.

(* Embed a call in the top level of the FunStack into a FunStackE *)
Global Instance ReSum_FrameCall_FunStackE (E : Type) (Γ : FunStack) frame :
  ReSum (FrameCall frame) (FunStackE E (frame :: Γ)) :=
  fun args => inl args.

(* Map the return value for embedding a call in the top level to a FunStackE *)
Global Instance ReSumRet_FrameCall_FunStackE (E : Type) `{EncodingType E} Γ frame :
  ReSumRet (FrameCall frame) (FunStackE E (frame :: Γ)) :=
  fun args o => o.


(* An EvType is an event type E plus a return type for each event in E *)
Record EvType : Type :=
  { evTypeType :> Type@{entree_u};
    evRetType : evTypeType -> Type@{entree_u} }.

Global Instance EncodingType_EvType (E:EvType) : EncodingType E :=
  fun e => evRetType E e.

Global Instance ReSum_FunStack_EvType (E : EvType) Γ : ReSum E (FunStackE E Γ) :=
  ReSum_FunStackE_E _ _.
Global Instance ReSumRet_FunStack_EvType (E : EvType) Γ : ReSumRet E (FunStackE E Γ) :=
  ReSumRet_FunStackE_E _ _.

(* The SpecM monad is the entree_spec monad with FunStackE as the event type *)
Definition SpecM (E:EvType) Γ A : Type@{entree_u} :=
  entree_spec (FunStackE E Γ) A.

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

Global Instance ReSum_nil_FunStack E (Γ : FunStack) :
  ReSum (SpecEvent (FunStackE E nil)) (SpecEvent (FunStackE E Γ)) :=
  fun e => match e with
           | Spec_vis (inl el) => Spec_vis (resum el)
           | Spec_vis (inr er) => Spec_vis (resum er)
           | Spec_forall T => Spec_forall T
           | Spec_exists T => Spec_exists T
           end.

Global Instance ReSumRet_nil_FunStack (E:EvType) (Γ : FunStack) :
  ReSumRet (SpecEvent (FunStackE E nil)) (SpecEvent (FunStackE E Γ)) :=
  fun e =>
    match e return encodes (ReSum_nil_FunStack E Γ e) -> encodes e with
    | Spec_vis (inl el) => fun x => resum_ret el x
    | Spec_vis (inr er) => fun x => resum_ret er x
    | Spec_forall T => fun x => x
    | Spec_exists T => fun x => x
    end.


(* Lift a SpecM in the empty FunStack to an arbitrary FunStack *)
Definition liftStackS {E} {Γ} A (t:SpecM E nil A) : SpecM E Γ A :=
  resumEntree t.

(* Compute the type forall a b c ... . SpecM ... (R a b c ...) from an lrt *)
(*
Fixpoint LRTType E `{EncodingType E} Γ (lrt : LetRecType) : Type@{entree_u} :=
  match lrt with
  | LRT_Ret R => SpecM E Γ R
  | LRT_Fun A rest => forall (a : A), LRTType E Γ (rest a)
  end.
*)
Definition LRTType E Γ lrt : Type@{entree_u} :=
  lrtPi lrt (fun args => SpecM E Γ (LRTOutput lrt args)).

(* Create a recursive call to a function in the top-most using args *)
Definition CallS E Γ frame (args : FrameCall frame) :
  SpecM E (frame :: Γ) (FrameCallRet frame args) :=
  trigger (H2:=@SpecEventReSumRet _ _ _ _ _ _) args.

(* Build the right-nested tuple type of a list of functions in a RecFrame *)
Fixpoint FrameTuple E Γ (frame : RecFrame) : Type@{entree_u} :=
  match frame with
  | nil => unit
  | lrt :: frame' => LRTType E Γ lrt * FrameTuple E Γ frame'
  end.

(* Get the nth function in a FrameTuple *)
Fixpoint nthFrameTupleFun E Γ frame : forall n, FrameTuple E Γ frame ->
                                                LRTType E Γ (nthLRT frame n) :=
  match frame return forall n, FrameTuple E Γ frame ->
                               LRTType E Γ (nthLRT frame n) with
  | nil => fun _ _ v => match v with end
  | lrt :: frame' =>
    fun n => match n return FrameTuple E Γ (lrt :: frame') ->
                            LRTType E Γ (nthLRT (lrt :: frame') n) with
             | 0 => fun tup => fst tup
             | S n' => fun tup => nthFrameTupleFun E Γ frame' n' (snd tup)
             end
  end.

(* Apply a FrameTuple to a FrameCall to get a FrameCallRet *)
Definition applyFrameTuple E Γ frame (funs : FrameTuple E Γ frame)
           (call : FrameCall frame) : SpecM E Γ (FrameCallRet frame call) :=
  match call return SpecM E Γ (FrameCallRet frame call) with
  | FrameCallOfArgs _ n args =>
    lrtApply (nthLRT frame n) _ (nthFrameTupleFun _ _ frame n funs) args
  end.

(* Create a multi-way fixed point of a sequence of functions *)
Definition MultiFixS E Γ frame
           (bodies : FrameTuple E (frame :: Γ) frame)
           (call : FrameCall frame) : SpecM E Γ (FrameCallRet frame call) :=
  mrec_spec (applyFrameTuple E (frame :: Γ) frame bodies) call.



FIXME: old stuff below

(** Stack functors and using them in MultiFixS **)

(* A StackType is a type that depends on a FunStack *)
Definition StackType := FunStack -> Type@{entree_u}.

(* A stack functor is a type which depends on the current FunStack that supports
pushing and popping the FunStack as long as we have an interpretation of each
frame that is pushed or popped *)
Class IsStackFunc E (T : StackType) :=
  { pushSF : forall Γ frame,
      FrameTuple E (frame :: Γ) frame ->
      T Γ -> T (frame :: Γ);
    popSF : forall Γ frame,
      FrameTuple E (frame :: Γ) frame ->
      T (frame :: Γ) -> T Γ; }.

Definition constST T : StackType := fun _ => T.

#[global] Instance IsStackFunc_const E T : IsStackFunc E (constST T) :=
  { pushSF := fun _ _ _ x => x; popSF := fun _ _ _ x => x }.

Definition prodST (T1 T2 : StackType) : StackType :=
  (fun stk => prod (T1 stk) (T2 stk)).

#[global] Instance IsStackFunc_pair E T1 T2
  {isSF1 : IsStackFunc E T1} {isSF2 : IsStackFunc E T2} :
  IsStackFunc E (prodST T1 T2) :=
  { pushSF := fun stk frame interp tup => (pushSF stk frame interp (fst tup),
                                            pushSF stk frame interp (snd tup));
    popSF := fun stk frame interp tup => (popSF stk frame interp (fst tup),
                                           popSF stk frame interp (snd tup)); }.

Definition arrowST (T U : StackType) : StackType :=
  fun stk => T stk -> U stk.

#[global] Instance IsStackFunc_fun E T1 T2 
  {isSF1 : IsStackFunc E T1} {isSF2 : IsStackFunc E T2} :
  IsStackFunc E (arrowST T1 T2) :=
  { pushSF := fun stk frame interp f x =>
                pushSF stk frame interp (f (popSF stk frame interp x));
    popSF := fun stk frame interp f x =>
               popSF stk frame interp (f (pushSF stk frame interp x)); }.

(* A variant of LetRecType where arguments and the return type can depend on the
current stack, though arguments that do are not allowed to be type indices *)
Inductive LetRecTypeSF E : Type@{entree_u + 1} :=
| LRTSF_Ret R `{IsStackFunc E R} : LetRecTypeSF E
| LRTSF_Fun (A : Type@{entree_u}) (rest : A -> LetRecTypeSF E) : LetRecTypeSF E
| LRTSF_FunSF (A : StackType) `{IsStackFunc E A} (rest : LetRecTypeSF E) : LetRecTypeSF E.

(* Convert a LetRecTypeSF to a LetRecType by applying all its stack functors *)
Fixpoint applyLetRecTypeSF E stack (lrtSF : LetRecTypeSF E) : LetRecType :=
  match lrtSF with
  | LRTSF_Ret _ R => LRT_Ret (R stack)
  | LRTSF_Fun _ A rest => LRT_Fun A (fun x => applyLetRecTypeSF E stack (rest x))
  | LRTSF_FunSF _ A rest => LRT_Fun (A stack) (fun _ => applyLetRecTypeSF E stack rest)
  end.

(* A RecFrame of stack functor LetRecTypes *)
Definition RecFrameSF E := list (LetRecTypeSF E).

(* Convert a RecFrameSF to a RecFrame by applying all its LetRecTypeSFs *)
Fixpoint applyRecFrameSF E stack (frame : RecFrameSF E) : RecFrame :=
  match frame with
  | nil => nil
  | lrtSF :: frame' =>
      applyLetRecTypeSF E stack lrtSF :: applyRecFrameSF E stack frame'
  end.

(* Create a multi-way fixed point of a sequence of functions *)
Definition MultiFixS_SF E Γ frame
           (bodies : FrameTuple E (frame :: Γ) frame)
           (call : FrameCall frame) : SpecM E Γ (FrameCallRet frame call) :=
  mrec_spec (applyFrameTuple E (frame :: Γ) frame bodies) call.




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
