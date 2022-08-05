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

From Equations Require Import Equations Signature.

Local Open Scope entree_scope.
Local Open Scope list_scope.


(*
  should we enfore that A has type universe < entree_u? 
  can that encode that we want?
  perhaps no, because the existing code has everything at sort 0, where
  we will want sort 1,

  types of form forall a b c..., SpecM ... (R a b c ...)
*)
Inductive LetRecType : Type@{entree_u + 1} :=
  | LRT_Ret (R : Type@{entree_u}) : LetRecType
  | LRT_Fun (A : Type@{entree_u}) (rest : A -> LetRecType) : LetRecType.

(*
Inductive LetRecTypeArg : LetRecType -> Type :=
  | LRT_RetArg R : unit -> LetRecTypeArg (LRT_Ret R)
  | LRT_FunArg A rest (a : A) (b : LetRecTypeArg (rest a) ) : LetRecTypeArg (LRT_Fun A rest).
*)
(* defines input type for a lrt event *)
Fixpoint LRTInput (lrt : LetRecType) : Type@{entree_u} :=
  match lrt with
  | LRT_Ret R => unit
  | LRT_Fun A rest => forall a : A, LRTInput (rest a) 
  end.


Fixpoint LRTOutput lrt : EncodedType (LRTInput lrt) :=
  match lrt with
  | LRT_Ret R => fun _ : unit => R
  | LRT_Fun A rest => fun args =>
                       forall a : A, LRTOutput (rest a) (args a) end.

#[global] Instance LRTOutputEncoded lrt : EncodedType (LRTInput lrt) := LRTOutput lrt.

Notation function_sigs := (list LetRecType).
Notation function_stack := (list function_sigs).
(*
Inductive call_var : mutual_sigs -> LetRecType -> Type :=
| VarZ : forall (Γ : mutual_sigs) (lrt : LetRecType), call_var (lrt :: Γ) lrt
| VarS : forall (Γ : mutual_sigs) (lrt1 lrt2 : LetRecType),
    call_var Γ lrt1 -> call_var (lrt2 :: Γ) lrt1.
*)
(*
Fixpoint call_var_arg Γ lrt (v : call_var Γ lrt) : Type@{entree_u} :=
  match v with
  | VarZ Γ' lrt' => LetRecTypeE lrt'
  | VarS Γ' lrt1 lrt2 c => call_var_arg _ _ c end.
*)
Fixpoint function_sig_index (lrts : function_sigs) (n : nat) : LetRecType :=
  match lrts with
  | nil => LRT_Ret void
  | lrt :: lrts' => 
      match n with
      | 0 => lrt
      | S m => function_sig_index lrts' m end 
  end.
(*
Fixpoint LRTSBodies (lrts : function_sigs) (body_type : LetRecType -> Type) :=
  match lrts 
*)

Fixpoint typed_list (l : list Type) : Type :=
  match l with
  | nil => unit
  | h :: t => h * (typed_list t) end.

(* a sort of typed debruijn variable borrowed from one of Steve's developments*)
Inductive function_var : LetRecType -> function_sigs -> Type :=
  | VarZ lrt lrts : function_var lrt (lrt :: lrts)
  | VarS lrt lrt' lrts : function_var lrt lrts -> function_var lrt (lrt' :: lrts).

Fixpoint function_var_index (n : nat) (lrts : function_sigs) : option LetRecType :=
  match lrts with
  | nil => None
  | lrt :: lrts' =>
      match n with
      | 0 => Some lrt
      | S m => function_var_index m lrts' end
      end.

(*need to figure *)

Inductive SpecM (E : Type) `{EncodedType E} : function_stack -> Type@{entree_u} -> Type := 
  | RetS Γ A (a : A) : SpecM E Γ A
  | BindS Γ A B : SpecM E Γ A -> (A -> SpecM E Γ B) -> SpecM E Γ B
  | IterS Γ A B : (A -> SpecM E Γ (A + B)) -> A -> SpecM E Γ B
  | TriggerS Γ (e : E) : SpecM E Γ (encodes e)
  | AssumeS Γ (P : Prop) : SpecM E Γ unit
  | AssertS Γ (P : Prop) : SpecM E Γ unit
  | ForallS Γ (A : Set) : SpecM E Γ A
  | ExistsS Γ (A : Set) : SpecM E Γ A 
  | CallS Γ lrts lrt (x : function_var lrt lrts) (args : LRTInput lrt) : 
    SpecM E (lrts :: Γ) (LRTOutput lrt args)
  | (* I am concerned this is a bit more expressive than necessary,
                 this bodies function can dispatch on the info of which index it is,
                 actual CFG's in the language won't do that,
                 although I suppose extra expressiveness is not necessarily a problem
                 as long as it does not make the new type too complicated
               *)
    MultiFixS Γ lrts 
              (bodies : forall lrt, function_var lrt lrts -> forall (args : LRTInput lrt),
                  SpecM E (lrts :: Γ) (LRTOutput lrt args))
    lrt (x : function_var lrt lrts) : 
    forall args : LRTInput lrt, SpecM E Γ (LRTOutput lrt args).

Fixpoint LRTsInput (lrts : function_sigs) : Type@{entree_u} :=
  match lrts with
  | nil => void
  | lrt :: lrts' =>
      LRTInput lrt + (LRTsInput lrts')
  end.

(* this was a key missing piece I should have seen earlier *)
Equations LRTinjection (lrt : LetRecType) (lrts : function_sigs) (x : function_var lrt lrts) (args : LRTInput lrt) : LRTsInput lrts  :=
  LRTinjection lrt (lrt :: lrts) (VarZ lrt lrts) args := inl args;
  LRTinjection lrt (lrt' :: lrts) (VarS lrt lrt' lrts y) args := inr (LRTinjection lrt lrts y args).


Equations LRTsOutput (lrts : function_sigs) (args : LRTsInput lrts) : Type@{entree_u} :=
  LRTsOutput nil args := match args : void with end;
  LRTsOutput (lrt :: lrts') (inl args') := LRTOutput lrt args';
  LRTsOutput (lrt :: lrts') (inr args') := LRTsOutput lrts' args'.


Fixpoint function_stackE (E : Type) (Γ : function_stack) : Type@{entree_u} :=
  match Γ with
  | nil => E
  | lrts :: Γ' => LRTsInput lrts + function_stackE E Γ' 
  end.

Equations function_stackE_encodes (E : Type) `{EncodedType E} (Γ : function_stack) (args : function_stackE E Γ) : Type@{entree_u}:=
  function_stackE_encodes E nil e := encodes e;
  function_stackE_encodes E (lrts :: Γ') (inl args') => LRTsOutput lrts args';
  function_stackE_encodes E (lrts :: Γ') (inr args') => function_stackE_encodes E Γ' args'.

#[global] Instance function_stackE_encodes' (E : Type) `{EncodedType E} (Γ : function_stack) : EncodedType (function_stackE E Γ) :=
  function_stackE_encodes E Γ.

Equations function_stackE_resum (E : Type) (Γ : function_stack) (e : E) : function_stackE E Γ :=
  function_stackE_resum E nil e := e;
  function_stackE_resum E (_ :: Γ') e := inr (function_stackE_resum E Γ' e).

#[global] Instance function_stackE_resum' (E : Type) (Γ : function_stack) : ReSum E (function_stackE E Γ) :=
  function_stackE_resum E Γ.
(* TODO: write this with equations *)
Definition function_stackE_resum_ret (E : Type) `{EncodedType E} (Γ : function_stack) : ReSumRet E (function_stackE E Γ).
red.  intros e x. induction Γ.
- cbv in x. exact x.
- exact (IHΓ x).
Defined.

#[global] Instance function_stackE_resum_ret' E `{EncodedType E} Γ : ReSumRet E (function_stackE E Γ) :=
  function_stackE_resum_ret E Γ.

Arguments RetS {_ _ _ _} _.
Arguments BindS {_ _ _ _ _} _ _.
Arguments IterS {_ _ _ _ _} _ _.
Arguments AssumeS {_ _ _}.
Arguments AssertS {_ _ _}.
Arguments ExistsS {_ _ _}.
Arguments ForallS {_ _ _}.
Arguments TriggerS {_ _ _} _.
Arguments CallS {_ _ _} _ _ _.
Arguments MultiFixS {_ _ _ _}.

(* write up the MultiFixS stuff, finish this translation this morning, look more at the haskell in afternoon*)

Definition calls_test (E : Type@{entree_u}) `{EncodedType E} (lrts : function_sigs) Γ (lrt : LetRecType) 
           (args : LRTInput lrt) (x : function_var lrt lrts) : entree_spec (function_stackE E (lrts :: Γ)) (LRTOutput lrt args).
simpl. constructor. eapply VisF. Unshelve.
(*so the problem is injection an LRTInput into an LRTsInput, should rely on function_var *)
2 : apply (Spec_vis (inl args)).
eapply (EnTree.trigger (Spec_vis (inl args))) .

Equations denote_SpecM (E : Type@{entree_u}) `{EncodedType E} (Γ : function_stack) (A : Type) (spec : SpecM E Γ A) :
  entree_spec (function_stackE E Γ) A :=
  denote_SpecM E Γ A (RetS a) := Ret a;
  denote_SpecM E Γ A (BindS m k) := EnTree.bind (denote_SpecM E _ _ m) (fun x => denote_SpecM E _ _ (k x));
  denote_SpecM E Γ A (AssumeS P) := assume_spec P;
  denote_SpecM E Γ A (AssertS P) := assert_spec P;
  denote_SpecM E Γ A (ForallS A) := forall_spec A;
  denote_SpecM E Γ A (ExistsS A) := exists_spec A;
  denote_SpecM E Γ A (TriggerS e) := trigger e;
  denote_SpecM E Γ A (CallS lrts lrt x args) := EnTree.trigger (Spec_vis (inl args) );
  denote_SpecM E Γ A _ := EnTree.spin.


Fixpoint denote_SpecM (E : Type@{entree_u}) `{EncodedType E} Γ A (spec : SpecM E Γ A) : 
  entree_spec (function_stackE E Γ) A :=
  match spec with
  | RetS a => Ret a
  | BindS m k => EnTree.bind (denote_SpecM E _ _ m) (fun x => denote_SpecM E _ _ (k x))
  | IterS body a => EnTree.iter (fun x => denote_SpecM E _ _ (body x)) a
  | AssumeS P => assume_spec P
  | AssertS P => assert_spec P
  | ForallS A => forall_spec A
  | ExistsS A => exists_spec A
  | TriggerS e => trigger e
  (* I think there is an issue with + vs LRTOutput *)
  | CallS lrts lrt x args => EnTree.trigger (Spec_vis (inl args) )
  | _ => EnTree.spin end.
(*

  | CallS a => (EnTree.trigger (Spec_vis (inl (CallDep _ _ a))))
  | MrecS A B bodies a => mrec_spec (fun c : call_depE _ _  => 
                         match c with CallDep _ _ a => denote_SpecM E _ _ (bodies a) end) 
                               (CallDep _ _ a)
  end.
*)
(* 
Equations function_stackE_resum_ret (E : Type) `{EncodedType E} (Γ : function_stack) (e : E) (x : encodes (resum e)) :
  function_stackE_encodes E Γ :=
  function_stackE_resum_ret E nil e x := x;
  function_stackE_resum_ret E (_ :: Γ') e x := function_stackE_resum_ret E Γ' e x. *)
(*write up the translation today *)

(*could be worth proving an isomorphism between function_var lrt lrts and 
  bound indices
 *)
(*
  | CallS Γ A B (a : A) : SpecM E (ct_intro A B :: Γ) (B a)
  | MrecS Γ A B (bodies : forall a, SpecM E (ct_intro A B :: Γ) (B a) ) (a : A):
    SpecM E Γ (B a) *)
.

(* not sure this is needed
Fixpoint nat_to_call_var Γ n : option call_var :=
  match Γ with
  | nil => None
  | lrt :: Γ' =>
      match n with
      | 0 => Some (VarZ Γ' lrt
*)
(* call stack should become a list list lrt 
   maybe a sort of typed list where each signature has an index
*)

Instance LetRecTypeEEncodes lrt : EncodedType (LetRecTypeE lrt) := LRTEncodes lrt.


Variant callE (lrt : LetRecType) : Type@{entree_u} := Call (a : encodes lrt).
(* check with eddy to make sure this is right, does this do mutual right? *)
#[global] Instance callE_encdoes lrt : EncodedType (callE lrt) :=
  fun _ => encodes lrt.

Variant call_depE (A : Type) (B : A -> Type) : Type@{entree_u} := CallDep (a : A).
#[global] Instance call_depE_encodes A B : EncodedType (call_depE A B) :=
  fun c => match c with CallDep _ _ a => B a end.

(* should be different for my uses *)
Fixpoint denote_LetRecType (M : Type -> Type) (lrt : LetRecType) : Type@{entree_u} :=
  match lrt with
  | LRT_Ret R => M R (**)
  | LRT_Fun A rest => forall (a : A), denote_LetRecType M (rest a) end.

#[global] Instance LetRecTypeEncodes : EncodedType LetRecType :=
  denote_LetRecType.

Variant call_dep_type := 
  ct_intro (A : Type) (B : A -> Type).
Notation call_stack := (list call_dep_type).
Inductive call_var : call_stack -> call_dep_type -> Type :=
| VarZ  : forall (G:call_stack) t, call_var (t::G) t
| VarS  : forall (G:call_stack) u t,
    call_var G t -> call_var (u::G) t.

Definition call_dep_type_trans (c : call_dep_type) : Type@{entree_u} :=
  match c with ct_intro A B => call_depE A B end.

#[global] Instance call_dep_type_trans_encodes (C : call_dep_type) : 
  EncodedType (call_dep_type_trans C) :=
 match C as C' return (call_dep_type_trans C' -> Type) with
   ct_intro A B =>
     fun c => match c with CallDep _ _ a => B a end end.

Definition uncall {A B} (c : call_depE A B) : A :=
  match c with CallDep _ _ a => a end.








(* I think there is an associativity issue here want + E to be at the top
   maybe the way to do that is have nil map to void and only add E at the top level
*)
Fixpoint denote_call_stack (E : Type) (Γ : call_stack) : Type :=
  match Γ with
  | nil => E
  | C :: Γ' => call_dep_type_trans C + denote_call_stack E Γ' end.
(*
Print Instances EncodedType.
Definition denote_call_ctx_encodes_ (E : Type) `{EncodedType E} (Γ : call_ctx) : 
  denote_call_ctx E Γ -> Type. *)

(* replace with sanely written one *)
#[global] Instance denote_call_ctx_encodes E `{EncodedType E} Γ : EncodedType (denote_call_stack E Γ).
induction Γ.
- exact encodes.
- simpl. apply EncodedSum. exact (call_dep_type_trans_encodes a).
  exact IHΓ.
Defined.

#[global] Instance denote_call_ctx_resum E Γ : ReSum E (denote_call_stack E Γ).
induction Γ.
- simpl. intros e. exact e.
- simpl. intros e. apply ReSum_inr. exact (IHΓ e).
Defined.

#[global] Instance denote_call_ctx_resumret E Γ `{EncodedType E} : ReSumRet E (denote_call_stack E Γ).
induction Γ.
- simpl. intros e. unfold resum. intros x. exact x.
- simpl. intros e. apply IHΓ.
Defined.




#[global] Instance SpecM_Monad {E} `{EncodedType E} Γ : Monad (SpecM E Γ) :=
  {|
    ret := fun A a => RetS a;
    bind := fun A B m k => BindS m k;
  |}.
