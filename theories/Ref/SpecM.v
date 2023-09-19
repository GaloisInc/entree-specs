
From EnTree Require Import
     Basics.HeterogeneousRelations
     Basics.QuantType
     Core.EnTreeDefinition
     Core.SubEvent
     Ref.EnTreeSpecDefinition
     Ref.FixTree
.
From Coq Require Import
  Arith.Arith
  Strings.String
  Lists.List
  Logic.FunctionalExtensionality
.

Import Monads.


(**
 ** EncodingType and ReSum instances for defining SpecM
 **)

(* The error event type *)
Inductive ErrorE : Set :=
| mkErrorE : string -> ErrorE.

Global Instance EncodingType_ErrorE : EncodingType ErrorE := fun _ => Empty_set.

(* The event type for SpecM computations, given an underlying event type *)
Definition SpecE (E : EvType) : Type@{entree_u} :=
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
 ** Type Descriptions
 **)

Variant ArithKind : Type@{entree_u} :=
| Kind_Nat
| Kind_BV (w:nat)
.

Variant KindDesc : Type@{entree_u} :=
| Kind_Arith (K:ArithKind)
| Kind_Tp
.

Variant ArithUnOp := | Op1_Neg | Op1_Succ.
Variant ArithBinOp := | Op2_Plus | Op2_Times.

Inductive CastOp : ArithKind -> ArithKind -> Type@{entree_u} :=
| Cast_BVToNat w : CastOp (Kind_BV w) Kind_Nat
| Cast_NatToBV w : CastOp Kind_Nat (Kind_BV w)
| Cast_BVResize w1 w2 : CastOp (Kind_BV w1) (Kind_BV w2).

Inductive ArithConst : ArithKind -> Type@{entree_u} :=
| Const_nat (n:nat) : ArithConst Kind_Nat
| Const_bv (w:nat) (bits:VectorDef.t bool w) : ArithConst (Kind_BV w).

Inductive ArithExpr (K:ArithKind) : Type@{entree_u} :=
| Arith_Const (c:ArithConst K)
| Arith_Var (ix:nat)
| Arith_UnOp (op:ArithUnOp) (e:ArithExpr K)
| Arith_BinOp (op:ArithBinOp) (e1 e2:ArithExpr K)
| Arith_Cast K' (op:CastOp K' K) (e:ArithExpr K')
.

(* The natural number 0 as an ArithExpr *)
Definition ArithZ : ArithExpr Kind_Nat := Arith_Const _ (Const_nat 0).

(* The successor function on ArithExprs *)
Definition ArithS (e: ArithExpr Kind_Nat) : ArithExpr Kind_Nat :=
  Arith_UnOp _ Op1_Succ e.

(* Descriptions of types *)
Inductive TpDesc : Type@{entree_u} :=
(* Monadic function types *)
| Tp_M (R : TpDesc)
| Tp_Pi (A : KindDesc) (B : TpDesc)
| Tp_Arr (A : TpDesc) (B : TpDesc)

(* First-order types *)
| Tp_Kind (K : KindDesc)
| Tp_Pair (A : TpDesc) (B : TpDesc)
| Tp_Sum (A : TpDesc) (B : TpDesc)
| Tp_Sigma (K : KindDesc) (B : TpDesc)
| Tp_Vec (A : TpDesc) (n:ArithExpr Kind_Nat)

(* Inductive types and type variables *)
| Tp_Ind (A : TpDesc)
| Tp_Var (n : nat)
| Tp_Void
.

(**
 ** Deciding equality of type descriptions
 **)

Lemma dec_eq_KindDesc (K1 K2:KindDesc) : {K1=K2} + {~K1=K2}.
Proof. repeat decide equality. Qed.

Lemma dec_eq_ArithConst_dep K1 (e1:ArithConst K1) K2 (e2:ArithConst K2) :
  { existT ArithConst K1 e1 = existT ArithConst K2 e2 } +
    { ~ existT ArithConst K1 e1 = existT ArithConst K2 e2 }.
Proof.
Admitted.

Lemma dec_eq_ArithConst K (e1 e2:ArithConst K) : {e1=e2} + {~e1=e2}.
Admitted.

Lemma dec_eq_ArithExpr K (e1 e2 : ArithExpr K) : {e1=e2} + {~e1=e2}.
Proof.
  revert e2; induction e1; intro e2; destruct e2; try (right; intro H; discriminate H).
  - destruct (dec_eq_ArithConst K c c0).
    + rewrite e; left; reflexivity.
    + right; intro H; inversion H; apply n; assumption.
  - destruct (Nat.eq_dec ix ix0).
    + rewrite e; left; reflexivity.
    + right; intro H; inversion H; apply n; assumption.
Admitted.

Definition dec_eq_TpDesc (T U:TpDesc) : { T = U } + {~ T = U}.
Proof.
  repeat decide equality. apply dec_eq_ArithExpr.
Qed.


(**
 ** Elements of kind descriptions
 **)

Definition arithKindElem K :=
  match K with
  | Kind_Nat => nat
  | Kind_BV w => VectorDef.t bool w
  end.

(* An element of a kind *)
Definition kindElem K : Type@{entree_u} :=
  match K with
  | Kind_Tp => TpDesc
  | Kind_Arith K' => arithKindElem K'
  end.

Definition defaultKindElem K : kindElem K :=
  match K return kindElem K with
  | Kind_Arith Kind_Nat => 0
  | Kind_Arith (Kind_BV w) => VectorDef.const false w
  | Kind_Tp => Tp_Void
  end.


(**
 ** Substitution for type descriptions
 **)

(* An element of an environment is a value, i.e., an element of some kind *)
Definition TpEnvElem : Type@{entree_u} := { K & kindElem K }.

(* An environment is a substitution from variables to values *)
Definition TpEnv := list TpEnvElem.

(* Add a value to a type environment *)
Definition envConsElem {K} (elem:kindElem K) (env:TpEnv) : TpEnv :=
  cons (existT kindElem K elem) env.

(* Eliminate a TpEnvElem at a particular kind, returning the default element of
that kind if the kind of the head does not match *)
Definition elimTpEnvElem K (elem:TpEnvElem) : kindElem K :=
  match dec_eq_KindDesc (projT1 elem) K with
  | left e => eq_rect (projT1 elem) kindElem (projT2 elem) K e
  | right _ => defaultKindElem K
  end.

(* Get the head value of a TpEnv at a particular kind, returning the default
element of that kind if the kind of the head does not match or env is empty *)
Definition headTpEnv K (env:TpEnv) : kindElem K :=
  match env with
  | nil => defaultKindElem K
  | elem :: _ => elimTpEnvElem K elem
  end.

(* Turn an element of an arith kind into an expression *)
Definition arithKindElemExpr {K} : arithKindElem K -> ArithExpr K :=
  match K return arithKindElem K -> ArithExpr K with
  | Kind_Nat => fun n => Arith_Const _ (Const_nat n)
  | Kind_BV w => fun bv => Arith_Const _ (Const_bv w bv)
  end.


(* Evaluate a variable of a particular kind relative to an environment at a
given lifting level n, meaning that the environment is a substitution for the
variables starting at n *)
Fixpoint substVar n env K var {struct var} : kindElem K + nat :=
  match var with
  | 0 => match n with
         | 0 => inl (headTpEnv K env)
         | S _ => inr 0
         end
  | S var' =>
      match n with
      | 0 => substVar 0 (tail env) K var'
      | S n' =>
          match substVar n' env K var' with
          | inl ret =>
              (* NOTE: if we were doing lifting, this is where we would do it *)
              inl ret
          | inr v_ret => inr (S v_ret)
          end
      end
  end.

(* Evaluate a variable to a value, using the default value for free variables *)
Definition evalVar n env K var : kindElem K :=
  match substVar n env K var with
  | inl v => v
  | inr _ => defaultKindElem K
  end.

(* Substitute an environment at lifting level n into arithmetic expression e *)
Fixpoint substArithExpr n env {K'} (e:ArithExpr K') : ArithExpr K' :=
  match e with
  | Arith_Const _ c => Arith_Const _ c
  | Arith_Var _ ix =>
      match substVar n env (Kind_Arith K') ix with
      | inl e' => arithKindElemExpr e'
      | inr ix' => Arith_Var _ ix'
      end
  | Arith_UnOp _ op e' => Arith_UnOp _ op (substArithExpr n env e')
  | Arith_BinOp _ op e1 e2 =>
      Arith_BinOp _ op (substArithExpr n env e1) (substArithExpr n env e2)
  | Arith_Cast _ K' op e' => Arith_Cast _ _ op (substArithExpr n env e')
  end.

(* Substitute an environment at lifting level n into type description T *)
Fixpoint tpSubst n env (T:TpDesc) : TpDesc :=
  match T with
  | Tp_M R => Tp_M (tpSubst n env R)
  | Tp_Pi A B => Tp_Pi A (tpSubst (S n) env B)
  | Tp_Arr A B => Tp_Arr (tpSubst n env A) (tpSubst n env B)
  | Tp_Kind K => Tp_Kind K
  | Tp_Pair A B => Tp_Pair (tpSubst n env A) (tpSubst n env B)
  | Tp_Sum A B => Tp_Sum (tpSubst n env A) (tpSubst n env B)
  | Tp_Sigma A B => Tp_Sigma A (tpSubst (S n) env B)
  | Tp_Vec A e => Tp_Vec (tpSubst n env A) (substArithExpr n env e)
  | Tp_Ind A => Tp_Ind (tpSubst (S n) env A)
  | Tp_Var var => match substVar n env Kind_Tp var with
                  | inl U => U
                  | inr var' => Tp_Var var'
                  end
  | Tp_Void => Tp_Void
  end.


(**
 ** Elements of type descriptions
 **)

Fixpoint evalArithExpr (env:TpEnv) {K} (e:ArithExpr K) : arithKindElem K.
Admitted.

(* Inductively defined elements of a type description *)
Inductive indElem : TpEnv -> TpDesc -> Type@{entree_u} :=
| Elem_M {env R} (f:FunIx (Tp_M R)) : indElem env (Tp_M R)
| Elem_Pi {env A B} (f:FunIx (Tp_Pi A B)) : indElem env (Tp_Pi A B)
| Elem_Arr {env A B} (f:FunIx (Tp_Arr A B)) : indElem env (Tp_Arr A B)
| Elem_Kind {env K} (elem:kindElem K) : indElem env (Tp_Kind K)
| Elem_Pair {env A B} (elem1: indElem env A) (elem2: indElem env B)
  : indElem env (Tp_Pair A B)
| Elem_SumL {env A B} (elem: indElem env A) : indElem env (Tp_Sum A B)
| Elem_SumR {env A B} (elem: indElem env B) : indElem env (Tp_Sum A B)
| Elem_Sigma {env K B}
    (elem1: kindElem K) (elem2: indElem (envConsElem elem1 env) B)
  : indElem env (Tp_Sigma K B)
| Elem_VecNil {env A} : indElem env (Tp_Vec A ArithZ)
| Elem_VecCons {env A e} (elem1: indElem env A) (elem2: indElem env (Tp_Vec A e))
  : indElem env (Tp_Vec A (ArithS e))
| Elem_VecCast {env A e1 e2} (e: evalArithExpr env e1 = evalArithExpr env e2)
    (elem: indElem env (Tp_Vec A e1)) : indElem env (Tp_Vec A e2)
| Elem_Ind {env A} (elem: indElem (@envConsElem Kind_Tp
                                     (tpSubst 0 env (Tp_Ind A))
                                     env) A)
  : indElem env (Tp_Ind A)
| Elem_Var {env} var (elem: indElem nil (evalVar 0 env Kind_Tp var)) :
  indElem env (Tp_Var var)
(* No case for Tp_Void *)
.

(* Elements of a type description *)
Fixpoint tpElem env T : Type@{entree_u} :=
  match T with
  | Tp_M R => FunIx (Tp_M R)
  | Tp_Pi K B => FunIx (Tp_Pi K B)
  | Tp_Arr A B => FunIx (Tp_Arr A B)
  | Tp_Kind K => kindElem K
  | Tp_Pair A B => tpElem env A * tpElem env B
  | Tp_Sum A B => tpElem env A + tpElem env B
  | Tp_Sigma K B => { elem: kindElem K & tpElem (envConsElem elem env) B }
  | Tp_Vec A e => VectorDef.t (tpElem env A) (evalArithExpr env e)
  | Tp_Ind A => indElem env (Tp_Ind A)
  | Tp_Var var => indElem nil (evalVar 0 env Kind_Tp var)
  | Tp_Void => Empty_set
  end.


(**
 ** The SpecM monad
 **)

Section SpecM.

Context {Tp} `{IsTpDesc Tp} {E : EvType}.

(* The SpecM monad is an entree spec over SpecE events *)
Definition SpecM A : Type := fixtree Tp (SpecEv E) A.

#[global] Instance Monad_SpecM : Monad SpecM := Monad_fixtree _ _.

(* The monadic operations on SpecM *)
Definition RetS {A} (a : A) : SpecM A := ret a.
Definition BindS {A B} (m : SpecM A) (k : A -> SpecM B) := bind m k.

Definition ForallS (A : Type) `{QuantType A} : SpecM A :=
  Fx_Vis (Spec_forall quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).
Definition ExistsS (A : Type) `{QuantType A} : SpecM A :=
  Fx_Vis (Spec_exists quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).

Definition AssumeS (P : Prop) : SpecM unit :=
  BindS (ForallS P) (fun _ => ret tt).
Definition AssertS (P : Prop) : SpecM unit :=
  BindS (ExistsS P) (fun _ => ret tt).

Definition TriggerS (e : E) : SpecM (encodes e) :=
  Fx_Vis (resum e : SpecEv E) (fun x => Fx_Ret x).

Definition ErrorS {A} (str : string) : SpecM A :=
  Fx_Vis ((Spec_vis (inl (mkErrorE str))) : SpecEv E)
    (fun (x:Empty_set) => match x with end).

Definition errorEntree {R} (s : string) : entree (SpecEv E) R :=
  Vis (Spec_vis (inl (mkErrorE s))) (fun v:Empty_set => match v with end).

Definition interp_SpecM {R} (t:SpecM R) : entree (SpecEv E) R :=
  interp_fixtree (@errorEntree R "Unbound function call") nil t.

End SpecM.
