
From Coq Require Import
  Arith.Arith
  Lists.List
  Eqdep (* NOTE: we actually only need this on decidable types... *)
.
From EnTree Require Import
     Basics.HeterogeneousRelations
     Ref.FixTree
.

Section TpDesc.

(**
 ** Arithmetic Kinds
 **)

(* An arithmetic kind is a description of a type that can be used in arithmetic
expressions in types *)
Class IsArithKind (ArithK:Type@{entree_u}) : Type :=
  {
    (* The types described by an element of ArithK, each of which must have a
    default element *)
    arithKindElem : ArithK -> Type@{entree_u};
    defaultAKElem : forall AK, arithKindElem AK;

    (* The type descriptions and elements must have decidable equality *)
    dec_eq_ArithK : forall (AK1 AK2:ArithK), {AK1=AK2} + {~AK1=AK2};
    dec_eq_arithKElem : forall AK (elem1 elem2:arithKindElem AK),
      {elem1=elem2} + {~elem1=elem2};
  }.

(* We assume some arithmetic kind for the rest of this file *)
Context ArithK `{IsArithKind ArithK}.

(* The type we use for arithmetic kinds must include nat, so we define "the"
type of arithmetic kinds as either nat or a user-defined kind *)
Inductive ArithKind : Type@{entree_u} :=
| Kind_nat
| Kind_other (AK:ArithK).

(* If ArithK is an arithmetic kind then so is ArithKind *)
Global Program Instance IsArithKind_ArithKind : IsArithKind ArithKind :=
  {| arithKindElem :=
      fun AK => match AK with
                | Kind_nat => nat
                | Kind_other AK' => arithKindElem AK'
                end;
    defaultAKElem :=
      fun AK => match AK with
                | Kind_nat => 0
                | Kind_other AK' => defaultAKElem AK'
                end;
  |}.
Next Obligation.
  decide equality. apply dec_eq_ArithK.
Defined.
Next Obligation.
  destruct AK; [ decide equality | apply dec_eq_arithKElem ].
Defined.


(* Types and interpretations of unary and binary operations, which are
   parameterized by their input and output types *)
Class ArithOps (ArithK:Type@{entree_u}) `{IsArithKind ArithK} : Type :=
  {
    arithUnOp : ArithK -> ArithK -> Type@{entree_u};
    arithBinOp : ArithK -> ArithK -> ArithK -> Type@{entree_u};

    dec_eq_UnOp : forall {AK1 AK2} (op1 op2 : arithUnOp AK1 AK2),
      {op1=op2} + {~op1=op2};
    dec_eq_BinOp : forall {AK1 AK2 AK3} (op1 op2 : arithBinOp AK1 AK2 AK3),
      {op1=op2} + {~op1=op2};

    evalUnOp : forall {AK1 AK2},
      arithUnOp AK1 AK2 -> arithKindElem AK1 -> arithKindElem AK2;
    evalBinOp : forall {AK1 AK2 AK3},
      arithBinOp AK1 AK2 AK3 -> arithKindElem AK1 -> arithKindElem AK2 ->
      arithKindElem AK3;
  }.

(* We assume a collection of operations on ArithKind ArithK *)
Context {AOps:ArithOps ArithKind}.

Variant KindDesc : Type@{entree_u} :=
| Kind_Arith (K:ArithKind)
| Kind_Tp
.

(* Arithmetic expressions that can be used in type descriptions *)
Inductive ArithExpr : ArithKind -> Type@{entree_u} :=
| Arith_Const {K} (c:arithKindElem K) : ArithExpr K
| Arith_Var {K} (ix:nat) : ArithExpr K
| Arith_UnOp {K1 K2} (op:arithUnOp K1 K2) (e:ArithExpr K1) : ArithExpr K2
| Arith_BinOp {K1 K2 K3} (op:arithBinOp K1 K2 K3)
    (e1:ArithExpr K1) (e2:ArithExpr K2) : ArithExpr K3
.

(* The natural number N as an ArithExpr *)
Definition ArithN (n:nat) : ArithExpr Kind_nat := @Arith_Const Kind_nat n.

(* The natural number 0 as an ArithExpr *)
Definition ArithZ : ArithExpr Kind_nat := @Arith_Const Kind_nat 0.

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
| Tp_Vec (A : TpDesc) (e:ArithExpr Kind_nat)

(* Inductive types and type variables *)
| Tp_Ind (A : TpDesc)
| Tp_Var (n : nat)
| Tp_Void
.


(**
 ** Deciding equality of type descriptions
 **)

Lemma dec_eq_KindDesc (K1 K2:KindDesc) : {K1=K2} + {~K1=K2}.
Proof. decide equality. apply dec_eq_ArithK. Qed.

Lemma dec_eq_ArithExpr K (e1 e2 : ArithExpr K) : {e1=e2} + {~e1=e2}.
Proof.
  revert e2; induction e1; intro e2; destruct e2; try (right; intro H0; discriminate H0).
  - destruct (dec_eq_arithKElem K c c0).
    + rewrite e; left; reflexivity.
    + right; intro e; inversion e; apply inj_pairT2 in H1; apply n; assumption.
  - destruct (Nat.eq_dec ix ix0).
    + rewrite e; left; reflexivity.
    + right; intro e; inversion e; apply n; assumption.
  - destruct (dec_eq_ArithK K0 K1).
    + subst K0. destruct (dec_eq_UnOp op op0); [ destruct (IHe1 e2) | ].
      * subst op; subst e1; left; reflexivity.
      * right; intro e'; inversion e'; apply n.
        apply inj_pairT2 in H2. assumption.
      * right; intro e'; inversion e'; apply n.
        repeat apply inj_pairT2 in H1. assumption.
    + right; intro e; inversion e. apply n; symmetry; assumption.
  - destruct (dec_eq_ArithK K0 K1); [ destruct (dec_eq_ArithK K3 K2) | ].
    + subst K0; subst K3.
      destruct (dec_eq_BinOp op op0);
        [ destruct (IHe1_1 e2_1); [ destruct (IHe1_2 e2_2) | ] | ].
      * subst op0; subst e1_1; subst e1_2. left; reflexivity.
      * right; intro e'; inversion e'; apply n. apply inj_pairT2 in H3; assumption.
      * right; intro e'; inversion e'; apply n. apply inj_pairT2 in H2; assumption.
      * right; intro e'; inversion e'; apply n.
        repeat apply inj_pairT2 in H1. assumption.
    + right; intro e'; inversion e'; apply n; symmetry; assumption.
    + right; intro e'; inversion e'; apply n; symmetry; assumption.
Qed.

Definition dec_eq_TpDesc (T U:TpDesc) : { T = U } + {~ T = U}.
Proof.
  repeat decide equality; try apply dec_eq_ArithK. apply dec_eq_ArithExpr.
Qed.


(**
 ** Elements of kind descriptions
 **)

(* An element of a kind *)
Definition kindElem K : Type@{entree_u} :=
  match K with
  | Kind_Tp => TpDesc
  | Kind_Arith K' => arithKindElem K'
  end.

Definition defaultKindElem K : kindElem K :=
  match K return kindElem K with
  | Kind_Tp => Tp_Void
  | Kind_Arith AK => defaultAKElem AK
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
Fixpoint substArithExpr n env {K} (e:ArithExpr K) : ArithExpr K :=
  match e in ArithExpr K return ArithExpr K with
  | Arith_Const c => Arith_Const c
  | Arith_Var ix =>
      match substVar n env (Kind_Arith _) ix with
      | inl e' => Arith_Const e'
      | inr ix' => Arith_Var ix'
      end
  | Arith_UnOp op e' => Arith_UnOp op (substArithExpr n env e')
  | Arith_BinOp op e1 e2 =>
      Arith_BinOp op (substArithExpr n env e1) (substArithExpr n env e2)
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

Fixpoint evalArithExpr (env:TpEnv) {K} (e:ArithExpr K) : arithKindElem K :=
  match e in ArithExpr K return arithKindElem K with
  | Arith_Const c => c
  | Arith_Var ix => evalVar 0 env (Kind_Arith _) ix
  | Arith_UnOp op e => evalUnOp op (evalArithExpr env e)
  | Arith_BinOp op e1 e2 =>
      evalBinOp op (evalArithExpr env e1) (evalArithExpr env e2)
  end.

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
| Elem_VecCons {env A n} (elem1: indElem env A)
    (elem2: indElem env (Tp_Vec A (ArithN n)))
  : indElem env (Tp_Vec A (ArithN (S n)))
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

(* Helper function to build a vector indElem with a constant size *)
Fixpoint mkVecIndElemConst {env T n} :
  VectorDef.t (indElem env T) n -> indElem env (Tp_Vec T (ArithN n)) :=
  match n return VectorDef.t (indElem env T) n -> indElem env (Tp_Vec T (ArithN n)) with
  | 0 => fun _ => Elem_VecNil
  | S n' =>
       fun elems =>
         Elem_VecCons (VectorDef.hd elems) (mkVecIndElemConst (VectorDef.tl elems))
  end.

(* Helper function to build a vector indElem from a vector of indElems *)
Definition mkVecIndElem {env T} {e:ArithExpr Kind_nat}
  (elems:VectorDef.t (indElem env T) (evalArithExpr env e)) : indElem env (Tp_Vec T e).
  apply (Elem_VecCast (e1:=ArithN (evalArithExpr env e))); [ reflexivity | ].
  apply mkVecIndElemConst. assumption.
Defined.


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

Fixpoint indToTpElem env {T} (elem : indElem env T) : tpElem env T.
  destruct elem.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - split; apply indToTpElem; assumption.
  - left; apply indToTpElem; assumption.
  - right; apply indToTpElem; assumption.
  - exists elem1. apply indToTpElem; assumption.
  - apply VectorDef.nil.
  - apply VectorDef.cons;
      [ apply (indToTpElem env _ elem1) | apply (indToTpElem env _ elem2) ].
  - simpl. rewrite <- e. apply (indToTpElem env _ elem).
  - constructor. apply elem.
  - apply elem.
Defined.

Fixpoint tpToIndElem env {T} : tpElem env T -> indElem env T.
  destruct T; intro elem.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; destruct elem; apply tpToIndElem; assumption.
  - destruct elem; [ apply Elem_SumL | apply Elem_SumR ];
      apply tpToIndElem; assumption.
  - econstructor. apply (tpToIndElem _ _ (projT2 elem)).
  - apply mkVecIndElem. apply (VectorDef.map (tpToIndElem env T) elem).
  - apply elem.
  - constructor; assumption.
  - destruct elem.
Defined.


End TpDesc.
