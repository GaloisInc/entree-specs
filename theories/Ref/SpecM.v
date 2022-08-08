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

From Coq Require Import Lists.List
     Logic.JMeq
.

From Paco Require Import paco.

From Equations Require Import Equations Signature.

Local Open Scope entree_scope.
Local Open Scope list_scope.


Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

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

Equations function_sig_nil {A : Type} (lrt : LetRecType) (x : function_var lrt nil) : A := .

(* this was a key missing piece *)
Equations LRTinjection (lrt : LetRecType) (lrts : function_sigs) (x : function_var lrt lrts) (args : LRTInput lrt) : LRTsInput lrts  :=
  LRTinjection lrt (lrt :: lrts) (VarZ lrt lrts) args := inl args;
  LRTinjection lrt (lrt' :: lrts) (VarS lrt lrt' lrts y) args := inr (LRTinjection lrt lrts y args).


Equations LRTsOutput (lrts : function_sigs) (args : LRTsInput lrts) : Type@{entree_u} :=
  LRTsOutput nil args := match args : void with end;
  LRTsOutput (lrt :: lrts') (inl args') := LRTOutput lrt args';
  LRTsOutput (lrt :: lrts') (inr args') := LRTsOutput lrts' args'.
(*
Fixpoint LRTsOutputProjection (lrts : function_sigs) (lrt : LetRecType)
         (args : LRTInput lrt) (x : function_var lrt lrts)
    (ret : LRTsOutput lrts (LRTinjection lrt lrts x args)) :
    LRTOutput lrt args.
  LRTsOutputProjection lrts lrt (inl args') (VarZ lrt lrts) ret := LRTOutput lrt args';
  LRTsOutputProjection lrts lrt (inr args') (VarS lrt lrt' lrts y) ret :=  LRTsOutputProjection lrts lrt args' y ret.
*)
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

Definition function_stackE_lrt_resum (E : Type) (Γ : function_stack) (lrts : function_sigs)
 (lrt : LetRecType) (x : function_var lrt lrts) (args : LRTInput lrt) : function_stackE E (lrts :: Γ) :=
  inl (LRTinjection lrt lrts x args).

#[global] Instance function_stackE_lrt_resum' (E : Type) (Γ : function_stack) (lrts : function_sigs)
 (lrt : LetRecType) (x : function_var lrt lrts) : ReSum (LRTInput lrt) (function_stackE E (lrts :: Γ)) :=
  function_stackE_lrt_resum E Γ lrts lrt x.

(* TODO write this with equations*)
Definition function_stackE_lrt_resum_ret (E : Type) `{EncodedType E} (Γ : function_stack) (lrts : function_sigs)
 (lrt : LetRecType) (x : function_var lrt lrts) : @ReSumRet (LRTInput lrt) (function_stackE E (lrts :: Γ)) _ _ 
                                                            (function_stackE_lrt_resum E Γ lrts lrt x).
red. intros args ret. unfold encodes. unfold encodes in ret. simpl in ret. unfold LRTOutputEncoded.
induction x.
- simp LRTinjection in ret. simp LRTsOutput in ret.
- apply IHx. simp LRTinjection in ret.
Defined.
(*
Equations function_stackE_lrt_resum_ret' (E : Type) `{EncodedType E} (Γ : function_stack) (lrts : function_sigs)
 (lrt : LetRecType) (x : function_var lrt lrts)  : 
  @ReSumRet (LRTInput lrt) (function_stackE E (lrts :: Γ)) _ _ (function_stackE_lrt_resum E Γ lrts lrt x) :=
function_stackE_lrt_resum_ret' E Γ lrts lrt (VarZ lrt lrts) := 
  fun (args : LRTInput lrt) (ret : encodes (resum args)) => ret;
function_stackE_lrt_resum_ret' E Γ lrts lrt (VarS lrt' lrts)
*)
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
Arguments CallS {_ _ _ _ _} _.
Arguments MultiFixS {_ _ _}.

(* I am concerned that this might not reduce, hopefully equations won't fail me now *)

Equations LRTsInput_proj (lrts : function_sigs) (args : LRTsInput lrts) : 
  {lrt : LetRecType & (function_var lrt lrts) * { args' : LRTInput lrt & (LRTOutput lrt args' -> LRTsOutput lrts args) }}%type :=
  LRTsInput_proj (lrt :: lrts) (inl args) := existT _ lrt (VarZ lrt lrts, existT _ args _);
  LRTsInput_proj (lrt :: lrts) (inr args) := let '(existT _ lrt' (x , (existT _ args' f))) := LRTsInput_proj lrts args in
                                            existT _ lrt' (VarS _ _ _ x, existT _ args' f ).
Next Obligation. simp LRTsOutput.
Defined.

(**)

Equations LRTsOutput_projection (lrts : function_sigs) (lrt : LetRecType) 
          (args : LRTInput lrt) (x : function_var lrt lrts) : LRTsOutput lrts (LRTinjection lrt lrts x args) ->
                                                              LRTOutput lrt args :=
  LRTsOutput_projection lrts lrt args (VarZ lrt lrts) := fun ret => ret;
  LRTsOutput_projection lrts lrt args (VarS lrt lrt' lrts y) := LRTsOutput_projection lrts lrt args y.

Definition LRTsOutput_projection':
  forall (lrts : function_sigs) (lrt : LetRecType)
         (args : LRTInput lrt) (x : function_var lrt lrts),
    LRTsOutput lrts (LRTinjection lrt lrts x args) ->
    LRTOutput lrt args.
Proof.
  intros lrts lrt args x ret.
  induction x.
  - simp LRTinjection in ret. simp LRTsOutput in ret.
  - apply IHx. simp LRTinjection in ret.
Defined.
(*
Equations LRTsOutput_projection' (lrts : function_sigs) 
*)

Lemma LRTsOutputLRTOutput : forall (lrts : function_sigs) (lrt : LetRecType)
         (args : LRTInput lrt) (x : function_var lrt lrts),
    LRTsOutput lrts (LRTinjection lrt lrts x args) = LRTOutput lrt args.
Proof.
  intros. induction x.
  - simp LRTinjection. simp LRTsOutput. reflexivity.
  - simp LRTinjection. rewrite <- IHx. simp LRTsOutput. reflexivity.
Qed.

Lemma LRTsOutput_projection_JMeq : forall (lrts : function_sigs) (lrt : LetRecType)
         (args : LRTInput lrt) (x : function_var lrt lrts) 
         (ret : LRTsOutput lrts (LRTinjection lrt lrts x args) ) ,
    JMeq ret (LRTsOutput_projection _ _ _ _ ret).
Proof.
  intros.
  induction x.
  - cbv. reflexivity.
  - specialize (IHx args ret). eapply JMeq_trans. eapply IHx. cbn. reflexivity. 
Qed.
(* doesn't even require any axioms *)

(* maybe using equations for LRTinjection is a mistake? will it reduce when *)
Definition call_spec {E : Type@{entree_u}} `{EncodedType E} {lrts : function_sigs} {Γ} {lrt : LetRecType} 
           (args : LRTInput lrt) (x : function_var lrt lrts) : entree_spec (function_stackE E (lrts :: Γ)) (LRTOutput lrt args) :=
Vis (Spec_vis (inl (LRTinjection lrt lrts x args)))
  (fun ret => Ret (LRTsOutput_projection lrts lrt args x ret)).
(*
Equations denote_SpecM (E : Type@{entree_u}) `{EncodedType E} (Γ : function_stack) (A : Type) (spec : SpecM E Γ A) :
  entree_spec (function_stackE E Γ) A :=
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
Definition multifix_spec {E : Type@{entree_u}} `{EncodedType E} (lrts : function_sigs) {Γ : function_stack} 
           (bodies : forall lrt : LetRecType, function_var lrt lrts -> forall args : LRTInput lrt, SpecM E (lrts :: Γ) (LRTOutput lrt args))
           (lrt : LetRecType) (x : function_var lrt lrts) (args : LRTInput lrt) : SpecM E Γ (LRTOutput lrt args) :=
mrec_spec 
*)

(* error in defining this function, not sure how important it is? *)
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


#[global] Instance Monad_entree_spec {E} `{EncodedType E} : Monad (entree_spec E) :=
  Monad_entree.

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
  | CallS x args => call_spec args x
  (* some weird error when defining LRTinjection_ret with equations *)
  | MultiFixS lrts bodies lrt x args => 
      ret <- (mrec_spec (fun args : LRTsInput lrts => 
                   let '(existT _ lrt (x, existT _ args' f)) := LRTsInput_proj lrts args in 
                   ret <- (denote_SpecM E _ _ (bodies lrt x args'));;
                   Ret (f ret)
                )
                (LRTinjection lrt lrts x args));;
      Ret (LRTinjection_ret lrt lrts x args ret)
  end.

#[global] Instance SpecM_Monad {E} `{EncodedType E} Γ : Monad (SpecM E Γ) :=
  {|
    ret := fun A a => RetS a;
    bind := fun A B m k => BindS m k;
  |}.
