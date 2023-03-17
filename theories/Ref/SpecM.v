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

Lemma papp_nil {A} (xs : plist A) : papp xs pnil = xs.
Proof.
  induction xs; [ reflexivity | ].
  simpl. rewrite IHxs. reflexivity.
Qed.

Lemma papp_assoc {A} (xs ys zs : plist A)
  : papp (papp xs ys) zs = papp xs (papp ys zs).
Proof.
  revert ys zs; induction xs; intros; [ reflexivity | ].
  simpl. rewrite IHxs. reflexivity.
Qed.

Lemma plength_papp {A} (xs ys : plist A)
  : plength (papp xs ys) = plength xs + plength ys.
Proof.
  induction xs; [ reflexivity | ].
  simpl. rewrite IHxs. reflexivity.
Qed.

Lemma plength_app_r {A} (xs ys : plist A) : plength xs <= plength (papp xs ys).
Proof.
  induction xs; [ apply le_0_n | ].
  apply le_n_S. assumption.
Qed.

Polymorphic Definition pcons_r@{u} {A : Type@{u}} (xs : plist A) (x:A) : plist A :=
  papp xs (pcons x pnil).

Lemma pcons_r_app {A} xs (x:A) ys : papp (pcons_r xs x) ys = papp xs (pcons x ys).
Proof.
  unfold pcons_r. rewrite papp_assoc. reflexivity.
Qed.

Polymorphic Fixpoint papp_r@{u} {A : Type@{u}} (xs ys : plist A) : plist A :=
  match ys with
  | pnil => xs
  | pcons y ys' => papp_r (pcons_r xs y) ys'
  end.

Lemma papp_r_papp {A} (xs ys : plist A) : papp_r xs ys = papp xs ys.
Proof.
  revert xs; induction ys; intros.
  - symmetry. apply papp_nil.
  - simpl. rewrite IHys. apply pcons_r_app.
Qed.

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

(* If an index n is at least as long as a list, nth_default' returns the default *)
Lemma nth_default'_default {A} (d:A) l n : plength l <= n -> nth_default' d l n = d.
Proof.
  revert n; induction l; intros; [ reflexivity | ].
  simpl. destruct n.
  - inversion H.
  - apply IHl. apply le_S_n. assumption.
Qed.

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

(* Project the nth element of a mapTuple *)
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


(** An inductive description of recursive function types and their arguments **)

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
Global Instance ReSum_LRTInput_FunStackE E stack n :
  ReSum (LRTInput stack (nthLRT stack n)) (FunStackE E stack) :=
  fun args => resum (FrameCallOfArgs stack n args).

Global Instance ReSumRet_LRTInput_FunStackE E stack n :
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

(* A FrameCall with its return type *)
Definition FrameCallWithRet stack (R : Type@{entree_u}) : Type@{entree_u} :=
  { call:FrameCall stack | FrameCallRet stack call = R }.

(* Create a recursive call to a function in the top-most using args *)
Definition CallS E stack R (args : FrameCallWithRet stack R) :
  SpecM E stack R :=
  eq_rect
    _ (fun R' => SpecM E stack R')
    (trigger (H2:=@SpecEventReSumRet _ _ _ _ _ _) (proj1_sig args))
    R (proj2_sig args).

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


(** Stack Inclusions **)

(* A stack inclusion is a mapping from the indices of one stack to those of
another that preserves LetRecTypes. Note that this is not technically a relation
because the mapping itself matters. *)
Definition stackIncl (stk1 stk2 : FunStack) : Type :=
  { f : nat -> nat |
    forall n, n < plength stk1 ->
              nthLRT stk1 n = nthLRT stk2 (f n) /\ f n < plength stk2 }.

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


(** Stack-polymorphic function tuples **)

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

(* An input for a call in a stack can only be to a call number that is in range *)
Lemma LRTInput_in_bounds stk stk' n (args : LRTInput stk' (nthLRT stk n)) :
  n < plength stk.
Proof.
  destruct (Compare_dec.le_lt_dec (plength stk) n); [ | assumption ].
  unfold nthLRT in args; rewrite nth_default'_default in args;
    [ destruct (projT1 args) | assumption ].
Qed.

Program Definition castLRTInput stk lrt lrt' (e : lrt = lrt')
  (args : LRTInput stk lrt) :
  { args': LRTInput stk lrt' | LRTOutput _ _ args' = LRTOutput _ _ args } := args.

(* Make a FrameCall in the context of a PolyFrameTuple *)
Program Definition mkFrameCall stk stk' (incl : stackIncl stk stk') n
  : lrtPi stk' (nthLRT stk n)
      (fun args => FrameCallWithRet stk' (LRTOutput stk' _ args)) :=
  lrtLambda stk' (nthLRT stk n) _
    (fun args =>
       exist _ (FrameCallOfArgs stk' (incl n) (castLRTInput stk' _ _ _ args)) _).
Next Obligation.
  apply (proj1 (proj2_sig incl n (LRTInput_in_bounds _ _ _ args))).
Defined.
Next Obligation.
  apply (proj2_sig (castLRTInput stk' _ _ _ args)).
Defined.


(** Specification Definitions **)

(* A "spec definition" represents a definition of a SpecM monadic function via
MultiFixsS over a tuple of recursive function bodies and a top-level call into
that tuple. A RelSpecDef is a spec definition relative to some stack of
already-defined recursive functions. *)
Record RelSpecDef E stk :=
  { relDefStack : FunStack;
    relDefBodies : PolyFrameTuple E (papp stk relDefStack) relDefStack;
    relDefCall : nat;
    relDefCallLt : relDefCall < plength relDefStack }.

(* The output type of the main definition of a RelSpecDef *)
Definition relDefOut E stk (d : RelSpecDef E stk) : LetRecType :=
  nthLRT (relDefStack _ _ d) (relDefCall _ _ d).

(* A spec definition that is not relative, i.e., has an empty stack *)
Definition SpecDef E := RelSpecDef E pnil.

(* Complete a SpecDef to a SpecM computation *)
Definition completeSpecDef E (d : SpecDef E)
  (args : LRTInput (relDefStack E _ d) (relDefOut E _ d)) :
  SpecM E pnil (LRTOutput _ _ args) :=
  MultiFixS E (relDefStack _ _ d)
    (relDefBodies _ _ d (relDefStack _ _ d) (reflStackIncl _))
    (FrameCallOfArgs _ _ args).

(* Build a stack inclusion for the imported spec in importSpecDef *)
Definition importInclImp E (imp : SpecDef E) stk stk_def :
  stackIncl (relDefStack _ _ imp) (papp stk (papp (relDefStack _ _ imp) stk_def)) :=
  compStackIncl
    (weakenRightStackIncl _ _)
    (weakenLeftStackIncl _ _).

(* Build a stack inclusion for the defined spec in importSpecDef *)
Definition importInclDef E (imp : SpecDef E) stk stk_def :
  stackIncl
    (papp (pcons_r stk (relDefOut _ _ imp)) stk_def)
    (papp stk (papp (relDefStack _ _ imp) stk_def)) :=
  compStackIncl
    (pappAssocStackIncl stk (pcons _ pnil) stk_def)
    (prefixStackIncl _ _ _
       (consPrefixStackIncl
          (relDefCall _ _ imp) _ (relDefCallLt _ _ imp)
          _ _ (reflStackIncl _))).

(* Import a SpecDef into another, by allowing the latter to call the former *)
Program Definition importSpecDef E (imp : SpecDef E) stk
  (d : RelSpecDef E (pcons_r stk (relDefOut E pnil imp))) :
  RelSpecDef E stk :=
  {|
    relDefStack := papp (relDefStack _ _ imp) (relDefStack _ _ d);
    relDefBodies :=
      appPolyFrameTuple
        E
        (papp stk (papp (relDefStack _ _ imp) (relDefStack _ _ d)))
        _ _
        (inclPolyFrameTuple
           _ _ _ _
           (importInclImp E imp stk (relDefStack _ _ d))
           (relDefBodies _ _ imp))
        (inclPolyFrameTuple
           _ _ _ _
           (importInclDef E imp stk (relDefStack _ _ d))
           (relDefBodies _ _ d));
    relDefCall := plength (relDefStack _ _ imp) + relDefCall _ _ d;
    relDefCallLt := _ |}.
Next Obligation.
  rewrite plength_papp.
  apply Plus.plus_lt_compat_l.
  apply relDefCallLt.
Defined.

(* Define a spec in a given FunStack that imports a list of spec definitions *)
Fixpoint defineRelSpec E stk (imps : plist (SpecDef E)) :
  RelSpecDef E (papp_r stk (pmap (relDefOut _ _) imps)) -> RelSpecDef E stk :=
  match imps return RelSpecDef E (papp_r stk (pmap (relDefOut _ _) imps)) ->
                    RelSpecDef E stk with
  | pnil => fun d => d
  | pcons imp imps' =>
      fun d =>
        importSpecDef E imp stk (defineRelSpec E _ imps' d)
  end.

(* Cast the stack of a spec definition *)
Program Definition castRelSpecDef E stk1 stk2 (e : stk1 = stk2)
  (d : RelSpecDef E stk1) : RelSpecDef E stk2 := d.

(* Define a spec in the empty FunStack that imports a list of spec definitions *)
Program Definition defineSpec E (imps : plist (SpecDef E))
                      (d : RelSpecDef E (pmap (relDefOut _ _) imps)) : SpecDef E :=
  defineRelSpec _ _ imps (castRelSpecDef _ _ _ _ d).
Next Obligation.
  rewrite papp_r_papp. reflexivity.
Defined.


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
Program CoFixpoint try_catch {E:EncType} {Γ} {A} {B}
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
