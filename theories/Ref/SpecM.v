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
     Ref.FixTree
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



(**
 ** EncodingType and ReSum instances for defining SpecM
 **)

(* The error event type *)
Inductive ErrorE : Set :=
| mkErrorE : string -> ErrorE.

Global Instance EncodingType_ErrorE : EncodingType ErrorE := fun _ => Empty_set.

(* The event type for SpecM computations, given an underlying event type *)
Definition SpecE (E : EvType@{entree_u}) : Type@{entree_u} :=
  SpecEvent (ErrorE + E).

(* The return type for a SpecEE effect in a SpecM computation *)
Definition SpecERet E (e:SpecE E) : Type@{entree_u} := encodes e.

Definition SpecEv E : EvType := Build_EvType (SpecE E) _.

Global Instance EncodingType_SpecE E : EncodingType (SpecE E) := SpecERet E.

Global Instance ReSum_SpecE_E (E : EvType) : ReSum E (SpecE E) :=
  fun e => Spec_vis (inr e).

Global Instance ReSumRet_SpecE_E (E : EvType) : ReSumRet E (SpecE E) :=
  fun _ r => r.

Global Instance ReSum_SpecE_Error (E : EvType) : ReSum ErrorE (SpecE E) :=
  fun e => Spec_vis (inl e).

Global Instance ReSumRet_SpecE_Error (E : EvType) : ReSumRet ErrorE (SpecE E) :=
  fun _ r => r.


(**
 ** The SpecM monad
 **)

(* The SpecM monad is an entree spec over FunStackE events *)
Definition SpecM (E:EvType) stack A : Type :=
  fixtree (SpecEv E) stack A.

#[global] Instance Monad_SpecM {E stk} : Monad (SpecM E stk) := Monad_fixtree.

(* The monadic operations on SpecM *)
Definition RetS {E} {stk A} (a : A) : SpecM E stk A := ret a.
Definition BindS {E} {stk A B} (m : SpecM E stk A) (k : A -> SpecM E stk B) :=
  bind m k.

Definition ForallS {E} {stk} (A : Type) `{QuantType A} : SpecM E stk A :=
  Fx_Vis (Spec_forall quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).
Definition ExistsS {E} {stk} (A : Type) `{QuantType A} : SpecM E stk A :=
  Fx_Vis (Spec_exists quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).

Definition AssumeS {E} {stk} (P : Prop) : SpecM E stk unit :=
  BindS (ForallS P) (fun _ => ret tt).
Definition AssertS {E} {stk} (P : Prop) : SpecM E stk unit :=
  BindS (ExistsS P) (fun _ => ret tt).

Definition TriggerS {E:EvType} {stk} (e : E) : SpecM E stk (encodes e) :=
  Fx_Vis (resum e : SpecEv E) (fun x => Fx_Ret x).

Definition ErrorS {E} {stk} A (str : string) : SpecM E stk A :=
  Fx_Vis ((Spec_vis (inl (mkErrorE str))) : SpecEv E)
    (fun (x:Empty_set) => match x with end).


(**
 ** Making and calling tpElems
 **)

(* An element of a type description that uses SpecM for the monadic type *)
Fixpoint SpecElem E stk T : Type@{entree_u} :=
  match T with
  | Tp_M R => SpecM E stk (tpElem (SpecEv E) stk R)
  | Tp_Pi A B => forall a, SpecElem E stk (B a)
  | Tp_Arr A B =>
      forall stk' (incl : stackIncl stk stk'),
        tpElem (SpecEv E) stk' A -> SpecElem E stk' B
  | Tp_SType A => tpElem (SpecEv E) stk (Tp_SType A)
  | Tp_Pair A B => tpElem (SpecEv E) stk (Tp_Pair A B)
  | Tp_Sum A B => tpElem (SpecEv E) stk (Tp_Sum A B)
  | Tp_Sigma A B => tpElem (SpecEv E) stk (Tp_Sigma A B)
  end.

Definition PolySpecElem E stk T : Type@{entree_u} :=
  forall stk' (incl : stackIncl stk stk'), SpecElem E stk' T.

Fixpoint SpecElemToMonoInterp E stk T : SpecElem E stk T -> MonoInterp (SpecEv E) stk T :=
  match T return SpecElem E stk T -> MonoInterp (SpecEv E) stk T with
  | Tp_M R => fun elem args => elem
  | Tp_Pi A B =>
      fun elem args =>
        SpecElemToMonoInterp E stk (B (projT1 args)) (elem (projT1 args)) (projT2 args)
  | Tp_Arr A B =>
      fun elem args =>
        SpecElemToMonoInterp E stk B (elem stk (reflListIncl _) (fst args)) (snd args)
  | Tp_SType A => fun elem args => match args with end
  | Tp_Pair A B => fun elem args => match args with end
  | Tp_Sum A B => fun elem args => match args with end
  | Tp_Sigma A B => fun elem args => match args with end
  end.

Definition SpecElemToInterp E stk T (elem: PolySpecElem E stk T)
  : FixTree.FxInterp (SpecEv E) stk T :=
  fun stk' incl => SpecElemToMonoInterp E stk' T (elem stk' incl).

Fixpoint InterpToSpecElem {E stk} T
 : isFunTp T -> FxInterp (SpecEv E) stk T -> SpecElem E stk T :=
  match T return isFunTp T -> FxInterp (SpecEv E) stk T -> SpecElem E stk T with
  | Tp_M R => fun _ m => m stk (reflListIncl _) tt
  | Tp_Pi A B => fun isfun f a =>
                   InterpToSpecElem (B a) (isfun a)
                     (fun stk' incl args => f stk' incl (existT _ a args))
  | Tp_Arr A B =>
      fun isfun f stk' incl arg =>
        InterpToSpecElem B isfun (fun stk'' incl' args =>
                                    f stk'' (compListIncl incl incl')
                                      (liftTpElem incl' arg, args))
  | Tp_SType _ => fun isfun => match isfun with end
  | Tp_Pair _ _ => fun isfun => match isfun with end
  | Tp_Sum _ _ => fun isfun => match isfun with end
  | Tp_Sigma _ _ => fun isfun => match isfun with end
  end.

Definition callStkFun {E stk T} (stkf : StkFun stk T) : SpecElem E stk T :=
  match stkf with
  | MkStkFun _ _ n isn isfun =>
      InterpToSpecElem T isfun
        (fun stk' incl args =>
           Fx_Call (MkStackCall _ _ T
                      (applyListIncl incl n) (applyListInclNth incl isn) args)
             (fun x => Fx_Ret x))
  end.

Fixpoint CallS {E stk T} : tpElem (SpecEv E) stk T -> SpecElem E stk T :=
  match T return tpElem (SpecEv E) stk T -> SpecElem E stk T with
  | Tp_M R =>
      fun elem => match elem with
                  | inl stkf => callStkFun stkf
                  | inr m => embedEntree m
                  end
  | Tp_Pi A B =>
      fun elem => match elem with
                  | inl stkf => callStkFun stkf
                  | inr f => fun a => CallS (f a)
                  end
  | Tp_Arr A B =>
      fun elem => match elem with
                  | inl stkf => callStkFun stkf
                  | inr f => fun stk' incl arg => CallS (f stk' incl arg)
                  end
  | Tp_SType _ => fun elem => elem
  | Tp_Pair _ _ => fun elem => elem
  | Tp_Sum _ _ => fun elem => elem
  | Tp_Sigma _ _ => fun elem => elem
  end.


(**
 ** Defining MultiFixS
 **)

(* A monadic function whose type is described by the encoding lrt *)
Definition SpecFun E stack lrt : Type@{entree_u} :=
  lrtPi stack lrt (fun args => SpecM E stack (LRTOutput _ lrt args)).

(* A trivially inhabited "default" SpecFun of type default_lrt *)
Definition defaultSpecFun E stack : SpecFun E stack default_lrt :=
  fun (v:Empty_set) => match v with end.

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
Definition defaultSpecDef E : SpecDef E default_lrt :=
  {|
    defStack := pnil;
    defFuns := fun _ _ => tt;
    defBody := fun stk' _ => defaultSpecFun E stk'
  |}.

(* Complete a SpecDef to a SpecM computation *)
Definition completeSpecDef E lrt (d : SpecDef E lrt)
  (args : LRTInput (defStack E lrt d) lrt) :
  SpecM E pnil (LRTOutput _ _ args) :=
  LetRecS E _ (defStack _ _ d)
    (defFuns _ _ d (defStack _ _ d) (reflStackIncl _))
    (lrtApply _ _ _ (defBody _ _ d (defStack _ _ d) (reflStackIncl _)) args).

(* An import of a SpecDef is an lrt plus a SpecDef with that type *)
Record SpecImp E : Type@{lrt_u} :=
  { SpecImpType : LetRecType;
    SpecImpDef : SpecDef E SpecImpType; }.

Definition defaultSpecImp E : SpecImp E :=
  {|
    SpecImpType := default_lrt;
    SpecImpDef := defaultSpecDef E |}.

Definition SpecImpStack E imp : FunStack := defStack E _ (SpecImpDef E imp).

(* A list of spec imports with their LetRecTypes *)
Definition impsList E : Type@{lrt_u} := plist (SpecImp E).

(* Build the concatenated FunStack for a list of imported spec defs *)
Definition impsStack E (imps:impsList E) : FunStack :=
  pconcat (pmap (SpecImpStack E) imps).

(* Build the list of recursive functions for a list of imported spec defs *)
Fixpoint impsFuns E imps
  : PolyStackTuple E (impsStack E imps) (impsStack E imps) :=
  match imps return PolyStackTuple E (impsStack E imps) (impsStack E imps) with
  | pnil => fun _ _ => tt
  | pcons imp imps' =>
      appPolyStackTuple _ _ _ _
        (inclPolyStackTuple _ _ _ _
           (weakenRightStackIncl _ _)
           (defFuns _ _ (SpecImpDef E imp)))
        (inclPolyStackTuple _ _ _ _
           (weakenLeftStackIncl _ _)
           (impsFuns E imps'))
  end.

(* The combined function stack for defineSpec *)
Definition defineSpecStack E stk (imps: impsList E) : FunStack :=
  papp stk (impsStack E imps).

(* Define a spec from: a list of imported spec definitions; a tuple of
recursively-defined functions; and a body that can call into either *)
Definition defineSpec E stk lrt (imps : impsList E)
  (recs : PolyStackTuple E (defineSpecStack E stk imps) stk)
  (body : PolySpecFun E (defineSpecStack E stk imps) lrt) : SpecDef E lrt :=
  {|
    defStack := defineSpecStack E stk imps;
    defFuns :=
      appPolyStackTuple _ _ _ _
        recs (inclPolyStackTuple _ _ _ _
                (weakenLeftStackIncl _ _) (impsFuns E imps));
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
Definition localIncl E stk imps : stackIncl stk (defineSpecStack E stk imps) :=
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
Definition mkLocalLRTClos E stk imps stk'
  (incl: stackIncl (defineSpecStack E stk imps) stk') n
  : LRTClos stk' (nthLRT stk n) :=
  mkLRTClosIncl stk stk' (compStackIncl (localIncl E stk imps) incl) n.

(* Get the nth spec import from an import list *)
Definition nthImport E (imps: impsList E) n : SpecImp E :=
  nth_default' (defaultSpecImp E) imps n.

(* Build a stackIncl from the stack of an import to an impsStack containing it *)
Fixpoint nthImpInclImpStack E imps n :
  stackIncl (SpecImpStack E (nthImport E imps n)) (impsStack E imps) :=
  match imps return
        stackIncl (SpecImpStack E (nthImport E imps n)) (impsStack E imps) with
  | pnil => nilStackIncl _
  | pcons imp imps' =>
      match n return
            stackIncl (SpecImpStack E (nthImport E (pcons imp imps') n))
              (impsStack E (pcons imp imps')) with
      | 0 => weakenRightStackIncl _ _
      | S n' => compStackIncl (nthImpInclImpStack E imps' n') (weakenLeftStackIncl _ _)
      end
  end.

(* Build a stackIncl from the stack of an import to that of a spec that imports it *)
Definition nthImpIncl E stk imps n :
  stackIncl (SpecImpStack E (nthImport E imps n))
    (defineSpecStack E stk imps) :=
  compStackIncl (nthImpInclImpStack E imps n) (weakenLeftStackIncl _ _).

(* Call the body of the nth import *)
Definition callNthImportS E stk imps stk'
  (incl: stackIncl (defineSpecStack E stk imps) stk') n
  : SpecFun E stk' (SpecImpType E (nthImport E imps n)) :=
  defBody _ _ (SpecImpDef E (nthImport E imps n)) stk'
    (compStackIncl (nthImpIncl E stk imps n) incl).

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

(*
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
Program CoFixpoint try_catch {E:EvType} {stk} {A} {B}
    (is_exceptional : FunStackE E stk -> option A)
    (catch : A -> SpecM E stk B) :
    SpecM E stk B -> SpecM E stk B :=
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
*)
