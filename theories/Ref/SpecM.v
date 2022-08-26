From ITree Require Import
     Basics.Basics
     Basics.Tacs
     Basics.HeterogeneousRelations
     Basics.Monad
 .
From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Core.SubEvent
     Eq.Eqit
     Ref.Padded
     Ref.EnTreeSpecDefinition
     Ref.MRecSpec
.

From Coq Require Import Lists.List.

From Paco Require Import paco.

Local Open Scope entree_scope.
Local Open Scope list_scope.

Import Monads.

(*
  should we enfore that A has type universe < entree_u? 
  can that encode that we want?
  perhaps no, because the existing code has everything at sort 0, where
  we will want sort 1,
*)
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
Fixpoint LRTOutput lrt : EncodedType (LRTInput lrt) :=
  match lrt with
  | LRT_Ret R => fun _ : unit => R
  | LRT_Fun A rest => fun args =>
                        let '(existT _ a args') := args in
                        LRTOutput (rest a) args'
  end.

#[global] Instance LRTOutputEncoded lrt : EncodedType (LRTInput lrt) := LRTOutput lrt.

(* A list of LetRecTypes for a collection of mutually recursive functions bound
   by a single use of multiFixS *)
Definition LetRecTypes := list LetRecType.

(* The type of an LRTInput for one of the LetRecTypes in a LetRecTypes list *)
Fixpoint LRTsInput (lrts : LetRecTypes) : Type@{entree_u} :=
  match lrts with
  | nil => void
  | lrt :: lrts' => LRTInput lrt + (LRTsInput lrts')
  end.

(* Compute the output type for calling the recursive function in a LetRecTypes
   specified by a given LRTsInput using the arguments it contains as inputs *)
Fixpoint LRTsOutput (lrts : LetRecTypes) : LRTsInput lrts -> Type@{entree_u} :=
  match lrts return LRTsInput lrts -> Type with
  | nil => fun x => match x with end
  | lrt :: lrts' => fun x => match x with
                             | inl args => LRTOutput lrt args
                             | inr e => LRTsOutput lrts' e
                             end
  end.

#[global] Instance LRTsOutputEncoded lrt : EncodedType (LRTsInput lrt) := LRTsOutput lrt.

(* A version of nth_default that does primary recursion on the list *)
Fixpoint nth_default' {A} (d : A) (l : list A) n : A :=
  match l with
  | nil => d
  | x :: l' => match n with
               | 0 => x
               | S n' => nth_default' d l' n'
               end
  end.

(* Get the nth element of a LetRecTypes list, or void -> void if n is too big *)
Definition nthLRT (lrts : LetRecTypes) n : LetRecType :=
  nth_default' (LRT_Fun void (fun _ => LRT_Ret void)) lrts n.

(* Embed an LRTInput (nthLRT lrts n) into an LRTsInput lrts *)
Fixpoint mkLRTsInput n (lrts : LetRecTypes)
  : LRTInput (nthLRT lrts n) -> LRTsInput lrts :=
  match lrts return LRTInput (nthLRT lrts n) -> LRTsInput lrts with
  | nil => fun x => match projT1 x with end
  | lrt :: lrts' =>
    match n return LRTInput (nthLRT (lrt :: lrts') n) -> LRTsInput (lrt :: lrts') with
    | 0 => fun args => inl args
    | S n' => fun args => inr (mkLRTsInput n' lrts' args)
    end
  end.

(* Map an LRTsOutput lrts for the nth fun back to an LRTsOutput (nthLRT lrts n) *)
Fixpoint unmapLRTsOutput n lrts :
  forall args, LRTsOutput lrts (mkLRTsInput n lrts args) ->
               LRTOutput (nthLRT lrts n) args :=
  match lrts return forall args, LRTsOutput lrts (mkLRTsInput n lrts args) ->
                                 LRTOutput (nthLRT lrts n) args with
  | nil => fun x => match projT1 x with end
  | lrt :: lrts' =>
    match n return
          forall args, LRTsOutput (lrt :: lrts') (mkLRTsInput n (lrt :: lrts') args) ->
                       LRTOutput (nthLRT (lrt :: lrts') n) args with
    | 0 => fun args o => o
    | S n' => unmapLRTsOutput n' lrts'
    end
  end.

(* ReSum instances for embedding the nth LRTInput into an LRTsInput *)
#[global] Instance LRTsInput_ReSum n lrts :
  ReSum (LRTInput (nthLRT lrts n)) (LRTsInput lrts) := mkLRTsInput n lrts.
#[global] Instance LRTsInput_ReSumRet n lrts :
  ReSumRet (LRTInput (nthLRT lrts n)) (LRTsInput lrts) := unmapLRTsOutput n lrts.

(* A FunStack is a list of LetRecTypes representing all of the functions bound
    by multiFixS that are currently in scope *)
Definition FunStack := list LetRecTypes.

(* Create an event type for either an event in E or a recursive call in a stack
   Γ of recursive functions in scope *)
Fixpoint FunStackE (E : Type) (Γ : FunStack) : Type@{entree_u} :=
  match Γ with
  | nil => E
  | lrts :: Γ' => LRTsInput lrts + FunStackE E Γ'
  end.

(* Compute the output type for a FunStackE event *)
Fixpoint FunStackE_encodes (E : Type) `{EncodedType E} (Γ : FunStack) :
  FunStackE E Γ -> Type@{entree_u} :=
  match Γ return FunStackE E Γ -> Type with
  | nil => fun e => encodes e
  | lrts :: Γ' => fun e => match e with
                           | inl args => LRTsOutput lrts args
                           | inr args => FunStackE_encodes E Γ' args
                           end
  end.

#[global] Instance FunStackE_encodes' (E : Type) `{EncodedType E} (Γ : FunStack) : EncodedType (FunStackE E Γ) :=
  FunStackE_encodes E Γ.

(* Embed an E event into the FunStackE event type *)
Fixpoint FunStackE_resum (E : Type) (Γ : FunStack) (e : E) : FunStackE E Γ :=
  match Γ return FunStackE E Γ with
  | nil => e
  | (_ :: Γ') => inr (FunStackE_resum E Γ' e)
  end.

(* Map the output of a FunStackE event for an E to the output type of E *)
Fixpoint FunStackE_resum_ret (E : Type) `{EncodedType E} (Γ : FunStack)
         (e : E) : encodes (FunStackE_resum E Γ e) -> encodes e :=
  match Γ return encodes (FunStackE_resum E Γ e) -> encodes e with
  | nil => fun o => o
  | (_ :: Γ') => FunStackE_resum_ret E Γ' e
  end.

#[global] Instance FunStackE_resum' (E : Type) (Γ : FunStack) : ReSum E (FunStackE E Γ) :=
  FunStackE_resum E Γ.

#[global] Instance FunStackE_resum_ret' (E : Type) `{EncodedType E} Γ :
  ReSumRet E (FunStackE E Γ) :=
  FunStackE_resum_ret E Γ.

(* Get the nth LetRecTypes frame in a FunStack, returning the empty frame if n
   is too big *)
Definition nthFrame (Γ : FunStack) fnum : LetRecTypes :=
  nth_default' nil Γ fnum.

(* Embed an LRTsInput for the fnum-th frame of a FunStack into FunStackE *)
Fixpoint mkFunStackE E Γ fnum : LRTsInput (nthFrame Γ fnum) -> FunStackE E Γ :=
  match Γ return LRTsInput (nthFrame Γ fnum) -> FunStackE E Γ with
  | nil => fun x => match x with end
  | lrts :: Γ' =>
    match fnum return LRTsInput (nthFrame (lrts :: Γ') fnum) ->
                      FunStackE E (lrts :: Γ') with
    | 0 => fun args => inl args
    | S fnum' => fun args => inr (mkFunStackE E Γ' fnum' args)
    end
  end.

(* Embed an LRTInput for the nth function in the fnum-th frame of a FunStack
   into FunStackE *)
Definition mkFunStackE' E Γ fnum n
           (args:LRTInput (nthLRT (nthFrame Γ fnum) n)) : FunStackE E Γ :=
  mkFunStackE E Γ fnum (mkLRTsInput n _ args).

(* Embed a call in the top level of the FunStack into a FunStackE *)
#[global] Instance FunStackE_lrt_resum (E : Type) (Γ : FunStack) lrts n :
  ReSum (LRTInput (nthLRT lrts n)) (FunStackE E (lrts :: Γ)) :=
  fun args => inl (mkLRTsInput n lrts args).

(* Map the return value for embedding a call in the top level to a FunStackE *)
#[global] Instance FunStackE_lrt_resum_ret (E : Type) `{EncodedType E} Γ lrts n
  : ReSumRet (LRTInput (nthLRT lrts n)) (FunStackE E (lrts :: Γ)) :=
  fun args o => unmapLRTsOutput n lrts args o.


(* I am concerned that this might not reduce, hopefully equations won't fail me now *)

(*
Equations LRTsInput_proj (lrts : function_sigs) (args : LRTsInput lrts) : 
  {lrt : LetRecType & (function_var lrt lrts) * { args' : LRTInput lrt & (LRTOutput lrt args' -> LRTsOutput lrts args) }}%type :=
  LRTsInput_proj (lrt :: lrts) (inl args) := existT _ lrt (VarZ lrt lrts, existT _ args _);
  LRTsInput_proj (lrt :: lrts) (inr args) := let '(existT _ lrt' (x , (existT _ args' f))) := LRTsInput_proj lrts args in
                                            existT _ lrt' (VarS _ _ _ x, existT _ args' f ).
Next Obligation. simp LRTsOutput.
Defined.

(*TODO: investigate strange equations warning here*)
Equations LRTsOutput_projection (lrts : function_sigs) (lrt : LetRecType) 
          (args : LRTInput lrt) (x : function_var lrt lrts) : LRTsOutput lrts (LRTinjection lrt lrts x args) ->
                                                              LRTOutput lrt args :=
  LRTsOutput_projection lrts lrt args (VarZ lrt lrts) := fun ret => ret;
  LRTsOutput_projection lrts lrt args (VarS lrt lrt' lrts y) := LRTsOutput_projection lrts lrt args y.

(* doesn't even require any axioms *)

(* maybe using equations for LRTinjection is a mistake? will it reduce when *)
Definition call_spec {E : Type@{entree_u}} `{EncodedType E} {lrts : function_sigs} {Γ} {lrt : LetRecType} 
           (args : LRTInput lrt) (x : function_var lrt lrts) : entree_spec (FunStackE E (lrts :: Γ)) (LRTOutput lrt args) :=
Vis (Spec_vis (inl (LRTinjection lrt lrts x args)))
  (fun ret => Ret (LRTsOutput_projection lrts lrt args x ret)).
(*
Equations denote_SpecM (E : Type@{entree_u}) `{EncodedType E} (Γ : FunStack) (A : Type) (spec : SpecM E Γ A) :
  entree_spec (FunStackE E Γ) A :=
  denote_SpecM E Γ A (RetS a) := Ret a;
  denote_SpecM E Γ A (BindS m k) := EnTree.bind (denote_SpecM E _ _ m) (fun x => denote_SpecM E _ _ (k x));
  denote_SpecM E Γ A (AssumeS P) := assume_spec P;
  denote_SpecM E Γ A (AssertS P) := assert_spec P;
  denote_SpecM E Γ A (ForallS A) := forall_spec A;
  denote_SpecM E Γ A (ExistsS A) := exists_spec A;
  denote_SpecM E Γ A (TriggerS e) := trigger e;
  denote_SpecM E Γ A (CallS lrts lrt x args) := call_spec args x;
  denote_SpecM E Γ A _ := EnTree.spin.
Reset denote_SpecM.
*)
(* need to go from LRTsInput lrts to lrt * LTRInput lrt  *)
(* not right yet,*)
(*
Definition multifix_spec {E : Type@{entree_u}} `{EncodedType E} (lrts : function_sigs) {Γ : FunStack} 
           (bodies : forall lrt : LetRecType, function_var lrt lrts -> forall args : LRTInput lrt, SpecM E (lrts :: Γ) (LRTOutput lrt args))
           (lrt : LetRecType) (x : function_var lrt lrts) (args : LRTInput lrt) : SpecM E Γ (LRTOutput lrt args) :=
mrec_spec 
*)

(* TODO: investigate strange equations warning here *)
Equations LRTinjection_ret (lrt : LetRecType) lrts (x : function_var lrt lrts) (args : LRTInput lrt) : 
  LRTsOutput lrts (LRTinjection lrt lrts x args) -> LRTOutput lrt args :=
  LRTinjection_ret lrt (lrt :: lrts) (VarZ lrt lrts) args := fun ret => ret;
  LRTinjection_ret lrt (lrt' :: lrts) (VarS lrt lrt' lrts y) args := LRTinjection_ret lrt lrts y args.

(*
Definition LRTinjection_ret (lrt : LetRecType) lrts (x : function_var lrt lrts) (args : LRTInput lrt) : 
  LRTsOutput lrts (LRTinjection lrt lrts x args) -> LRTOutput lrt args.
induction x.
- simp LRTinjection. simp LRTsOutput.
- intros. apply IHx. simp LRTinjection in X.
Defined.
*)

*)

#[global] Instance Monad_entree_spec {E} `{EncodedType E} : Monad (entree_spec E) :=
  Monad_entree.

(* The SpecM monad is the entree_spec monad with FunStackE as the event type *)
Definition SpecM (E : Type@{entree_u}) `{EncodedType E} Γ A : Type@{entree_u} :=
  entree_spec (FunStackE E Γ) A.

Definition RetS {E} `{EncodedType E} {Γ A} (a : A) : SpecM E Γ A := ret a.
Definition BindS {E} `{EncodedType E} {Γ A B} (m : SpecM E Γ A) (k : A -> SpecM E Γ B) :=
  bind m k.
Definition IterS {E} `{EncodedType E} {Γ A B} (body : A -> SpecM E Γ (A + B)) :
  A -> SpecM E Γ B := EnTree.iter body.
Definition AssumeS {E} `{EncodedType E} {Γ} (P : Prop) : SpecM E Γ unit := assume_spec P.
Definition AssertS {E} `{EncodedType E} {Γ} (P : Prop) : SpecM E Γ unit := assert_spec P.
Definition ForallS {E} `{EncodedType E} {Γ} (A : Set) : SpecM E Γ A := forall_spec A.
Definition ExistsS {E} `{EncodedType E} {Γ} (A : Set) : SpecM E Γ A := exists_spec A.
Definition TriggerS {E} `{EncodedType E} {Γ} (e : E) : SpecM E Γ (encodes e) := trigger e.

(* Compute the type forall a b c ... . SpecM ... (R a b c ...) from an lrt *)
(*
Fixpoint LRTType E `{EncodedType E} Γ (lrt : LetRecType) : Type@{entree_u} :=
  match lrt with
  | LRT_Ret R => SpecM E Γ R
  | LRT_Fun A rest => forall (a : A), LRTType E Γ (rest a)
  end.
*)
Definition LRTType E `{EncodedType E} Γ lrt : Type@{entree_u} :=
  lrtPi lrt (fun args => SpecM E Γ (LRTOutput lrt args)).

(* Create a recursive call to a function in the top-most frame *)
Definition CallS E `{EncodedType E} Γ Frame n : LRTType E (Frame :: Γ) (nthLRT Frame n) :=
  lrtLambda
    (nthLRT Frame n)
    (fun args => SpecM E (Frame :: Γ) (LRTOutput _ args))
    (fun args => trigger args).

(* Build the right-nested tuple type of a list of functions of type LRTType *)
Fixpoint LRTsTuple E `{EncodedType E} Γ (lrts : LetRecTypes) : Type :=
  match lrts with
  | nil => unit
  | lrt :: lrts' => LRTType E Γ lrt * LRTsTuple E Γ lrts'
  end.

(* Convert an LRTsTuple to a function from an LRTsInput to an LRTsOutput *)
Fixpoint LRTsTupleFun E `{EncodedType E} Γ (lrts : LetRecTypes) :
  LRTsTuple E Γ lrts -> forall args, SpecM E Γ (LRTsOutput lrts args) :=
  match lrts return LRTsTuple E Γ lrts ->
                    forall args, SpecM E Γ (LRTsOutput lrts args) with
  | nil => fun _ x => match x with end
  | lrt :: lrts' =>
    fun fs args =>
      match args return SpecM E Γ (LRTsOutput (lrt :: lrts') args) with
      | inl argsL => lrtApply lrt _ (fst fs) argsL
      | inr argsR => LRTsTupleFun E Γ lrts' (snd fs) argsR
      end
  end.

#[global] Instance SpecM_Monad {E} `{EncodedType E} Γ : Monad (SpecM E Γ) :=
  {|
    ret := fun A a => RetS a;
    bind := fun A B m k => BindS m k;
  |}.

(* Create a multi-way fixed point of a sequence of functions *)
Definition MultiFixS E `{EncodedType E} Γ Frame
           (bodies : LRTsTuple E (Frame :: Γ) Frame) n :
  LRTType E Γ (nthLRT Frame n) :=
  lrtLambda
    (nthLRT Frame n)
    (fun args => SpecM E Γ (LRTOutput _ args))
    (fun args =>
       Functor.fmap
         (resum_ret args)
         (mrec_spec (LRTsTupleFun E (Frame :: Γ) Frame bodies)
                    (mkLRTsInput n Frame args))).
