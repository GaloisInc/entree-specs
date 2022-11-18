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

(* An encoding of types of form forall a b c..., SpecM ... (R a b c ...). This
   encoding is realized by LRTType below. *)
Inductive LetRecType : Type@{entree_u + 1} :=
  | LRT_Ret (R : Type@{entree_u}) : LetRecType
  | LRT_Fun (A : Type@{entree_u}) (rest : A -> LetRecType) : LetRecType.

(* Compute a dependent tuple type of all the inputs of a LetRecType, i.e.,
   return the type { x:A & { y:B & ... { z:C & unit } ...}} from a LetRecType
   that represents forall a b c..., SpecM ... (R a b c ...) *)
(* might need to do a bunch of refactoring I think LRTInput' is right*)
Fixpoint LRTInput (lrt : LetRecType) : Type@{entree_u} :=
  match lrt with
  | LRT_Ret R => unit
  | LRT_Fun A rest => {a : A & LRTInput (rest a) }
  end.

(* Build the type forall a b c ..., F (a, (b, (c, ...))) for an arbitrary type
   function F over an LRTInput *)
Fixpoint lrtPi lrt : (LRTInput lrt -> Type) -> Type :=
  match lrt return (LRTInput lrt -> Type) -> Type with
  | LRT_Ret _ => fun F => F tt
  | LRT_Fun A lrtF =>
    fun F => forall a, lrtPi (lrtF a) (fun args => F (existT _ a args))
  end.

(* Build an lrtPi function from a unary function on an LRTInput *)
Fixpoint lrtLambda lrt
  : forall (F : LRTInput lrt -> Type), (forall args, F args) -> lrtPi lrt F :=
  match lrt return forall (F : LRTInput lrt -> Type), (forall args, F args) ->
                                                      lrtPi lrt F
  with
  | LRT_Ret _ => fun _ f => f tt
  | LRT_Fun A lrtF =>
    fun F f x => lrtLambda (lrtF x) (fun args => F (existT _ x args))
                           (fun args => f (existT _ x args))
  end.

(* Apply an lrtPi function *)
Fixpoint lrtApply lrt
  : forall F, lrtPi lrt F -> forall args, F args :=
  match lrt return forall F, lrtPi lrt F -> forall args, F args with
  | LRT_Ret _ =>
    fun F f u => match u return F u with | tt => f end
  | LRT_Fun A lrtF =>
    fun F f args =>
      match args return F args with
      | existT _ arg args' =>
        lrtApply (lrtF arg) (fun args' => F (existT _ arg args')) (f arg) args'
      end
  end.

(* NOTE: it is straight forward to prove a beta rule for lrtApply lrtLambda, but
   that isn't really needed below *)

(* Compute the output type (R a b c ...) from a LetRecType that represents
   forall a b c..., SpecM ... (R a b c ...) and a dependent tuple of arguments
   to a function of that type *)
Fixpoint LRTOutput lrt : EncodingType (LRTInput lrt) :=
  match lrt with
  | LRT_Ret R => fun _ : unit => R
  | LRT_Fun A rest => fun args =>
                        let '(existT _ a args') := args in
                        LRTOutput (rest a) args'
  end.

#[global] Instance LRTOutputEncoding lrt : EncodingType (LRTInput lrt) := LRTOutput lrt.

(* A recursive frame is a list of types for recursive functions all bound at the
   same time *)
Definition RecFrame := list LetRecType.

(* A version of nth_default that does primary recursion on the list *)
Fixpoint nth_default' {A} (d : A) (l : list A) n : A :=
  match l with
  | nil => d
  | x :: l' => match n with
               | 0 => x
               | S n' => nth_default' d l' n'
               end
  end.

(* Get the nth element of a RecFrame list, or void -> void if n is too big *)
Definition nthLRT (frame : RecFrame) n : LetRecType :=
  nth_default' (LRT_Fun void (fun _ => LRT_Ret void)) frame n.

(* A recursive call to one of the functions in a RecFrame *)
Inductive FrameCall frame : Type@{entree_u} :=
| FrameCallOfArgs n (args : LRTInput (nthLRT frame n)).

(* Get the index of a FrameCall *)
Definition FrameCallIndex {frame} (call : FrameCall frame) : nat :=
  match call with
  | FrameCallOfArgs _ n _ => n
  end.

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

#[global] Instance FrameCallRetEncoding lrt : EncodingType (FrameCall lrt) :=
  FrameCallRet lrt.

(* Make a recursive call from its individual arguments *)
Definition mkFrameCall (frame : RecFrame) n
  : lrtPi (nthLRT frame n) (fun args => FrameCall frame) :=
  lrtLambda (nthLRT frame n) (fun _ => FrameCall frame) (FrameCallOfArgs frame n).

(* ReSum instances for embedding the nth LRTInput into a FrameCall *)
#[global] Instance FrameCall_ReSum frame n :
  ReSum (LRTInput (nthLRT frame n)) (FrameCall frame) := FrameCallOfArgs frame n.
#[global] Instance FrameCall_ReSumRet frame n :
  ReSumRet (LRTInput (nthLRT frame n)) (FrameCall frame) :=
  fun _ r => r.

(* A FunStack is a list of RecFrame representing all of the functions bound
    by multiFixS that are currently in scope *)
Definition FunStack := list RecFrame.

(* The error event type *)
Inductive ErrorE : Set :=
| mkErrorE : string -> ErrorE.

#[global] Instance EncodingType_ErrorE : EncodingType ErrorE := fun _ => void.

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

#[global] Instance FunStackE_encodes' (E : Type) `{EncodingType E} (Γ : FunStack) : EncodingType (FunStackE E Γ) :=
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

#[global] Instance ReSum_FunStackE_E (E : Type) (Γ : FunStack) : ReSum E (FunStackE E Γ) :=
  fun e => FunStackE_embed_ev E Γ (inr e).

#[global] Instance ReSumRet_FunStackE_E (E : Type) `{EncodingType E} Γ :
  ReSumRet E (FunStackE E Γ) :=
  fun e => FunStackE_embed_ev_unmap E Γ (inr e).

#[global] Instance ReSum_FunStackE_Error (E : Type) (Γ : FunStack) : ReSum ErrorE (FunStackE E Γ) :=
  fun e => FunStackE_embed_ev E Γ (inl e).

#[global] Instance ReSumRet_FunStackE_Error (E : Type) `{EncodingType E} Γ :
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
#[global] Instance ReSum_LRTInput_FunStackE (E : Type) (Γ : FunStack) frame n :
  ReSum (LRTInput (nthLRT frame n)) (FunStackE E (frame :: Γ)) :=
  fun args => inl (FrameCallOfArgs frame n args).

(* Map the return value for embedding a call in the top level to a FunStackE *)
#[global] Instance ReSumRet_LRTInput_FunStackE (E : Type) `{EncodingType E} Γ frame n
  : ReSumRet (LRTInput (nthLRT frame n)) (FunStackE E (frame :: Γ)) :=
  fun args o => o.

(* Embed a call in the top level of the FunStack into a FunStackE *)
#[global] Instance ReSum_FrameCall_FunStackE (E : Type) (Γ : FunStack) frame :
  ReSum (FrameCall frame) (FunStackE E (frame :: Γ)) :=
  fun args => inl args.

(* Map the return value for embedding a call in the top level to a FunStackE *)
#[global] Instance ReSumRet_FrameCall_FunStackE (E : Type) `{EncodingType E} Γ frame :
  ReSumRet (FrameCall frame) (FunStackE E (frame :: Γ)) :=
  fun args o => o.


(* An EvType is an event type E plus a return type for each event in E *)
Record EvType : Type :=
  { evTypeType :> Type@{entree_u};
    evRetType : evTypeType -> Type@{entree_u} }.

Instance EncodingType_EvType (E:EvType) : EncodingType E :=
  fun e => evRetType E e.

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

#[global] Instance SpecM_Monad {E} Γ : Monad (SpecM E Γ) :=
  {|
    ret := fun A a => RetS a;
    bind := fun A B m k => BindS m k;
  |}.

#[global] Instance ReSum_nil_FunStack E (Γ : FunStack) :
  ReSum (SpecEvent (FunStackE E nil)) (SpecEvent (FunStackE E Γ)) :=
  fun e => match e with
           | Spec_vis (inl el) => Spec_vis (resum el)
           | Spec_vis (inr er) => Spec_vis (resum er)
           | Spec_forall T => Spec_forall T
           | Spec_exists T => Spec_exists T
           end.

#[global] Instance ReSumRet_nil_FunStack (E:EvType) (Γ : FunStack) :
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
Fixpoint FrameTuple E Γ (frame : RecFrame) : Type :=
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
#[global] Instance Monad_StateT M s `{Monad M} : Monad (StateT s M) :=
  {|
    ret := fun A x s => ret (s, x);
    bind := fun A B m k s => bind (m s) (fun a_s =>
                                           let (s',a) := a_s in
                                           k a s')
  |}.

#[global] Instance MonadIter_StateT M St `{Monad M} `{MI:MonadIter M} : MonadIter (StateT St M) :=
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
