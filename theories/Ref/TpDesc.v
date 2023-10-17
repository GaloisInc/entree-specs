
From Coq Require Import
  Arith.Arith
  Lists.List
  Eqdep (* NOTE: we actually only need this on decidable types... *)
.
From EnTree Require Import
     Basics.HeterogeneousRelations
     Ref.FixTree
.
From Bits Require Import operations spec.


(**
 ** Expression Kinds
 **)

(* The descriptions of the types of expressions that can be used in type
descriptions *)
Inductive ExprKind : Type@{entree_u} :=
| Kind_unit
| Kind_bool
| Kind_nat
| Kind_bv (w:nat).

Definition exprKindElem AK : Type@{entree_u} :=
  match AK with
  | Kind_unit => unit
  | Kind_bool => bool
  | Kind_nat => nat
  | Kind_bv w => VectorDef.t bool w
  end.

Definition defaultEKElem EK : exprKindElem EK :=
  match EK return exprKindElem EK with
  | Kind_unit => tt
  | Kind_bool => false
  | Kind_nat => 0
  | Kind_bv w => VectorDef.const false w
  end.

Inductive TpExprUnOp : ExprKind -> ExprKind -> Type@{entree_u} :=
| UnOp_BVToNat w : TpExprUnOp (Kind_bv w) Kind_nat
| UnOp_NatToBV w : TpExprUnOp Kind_nat (Kind_bv w)
.

Inductive TpExprBinOp : ExprKind -> ExprKind -> ExprKind -> Type@{entree_u} :=
| BinOp_AddNat : TpExprBinOp Kind_nat Kind_nat Kind_nat
| BinOp_MulNat : TpExprBinOp Kind_nat Kind_nat Kind_nat
| BinOp_AddBV w : TpExprBinOp (Kind_bv w) (Kind_bv w) (Kind_bv w)
| BinOp_MulBV w : TpExprBinOp (Kind_bv w) (Kind_bv w) (Kind_bv w)
.

Lemma dec_eq_UnOp {EK1 EK2} (op1 op2 : TpExprUnOp EK1 EK2) : {op1=op2} + {~op1=op2}.
Admitted.

Lemma dec_eq_BinOp {EK1 EK2 EK3} (op1 op2 : TpExprBinOp EK1 EK2 EK3)
  : {op1=op2} + {~op1=op2}.
Admitted.

Definition evalUnOp {EK1 EK2} (op: TpExprUnOp EK1 EK2) :
  exprKindElem EK1 -> exprKindElem EK2.
Admitted.

Definition evalBinOp {EK1 EK2 EK3} (op: TpExprBinOp EK1 EK2 EK3) :
  exprKindElem EK1 -> exprKindElem EK2 -> exprKindElem EK3.
Admitted.


(**
 ** Type descriptions themselves
 **)

Variant KindDesc : Type@{entree_u} :=
| Kind_Expr (EK:ExprKind)
| Kind_Tp
.

(* Expressions that can be used in type descriptions *)
Inductive TpExpr : ExprKind -> Type@{entree_u} :=
| TpExpr_Const {EK} (c:exprKindElem EK) : TpExpr EK
| TpExpr_Var {EK} (ix:nat) : TpExpr EK
| TpExpr_UnOp {EK1 EK2} (op:TpExprUnOp EK1 EK2) (e:TpExpr EK1) : TpExpr EK2
| TpExpr_BinOp {EK1 EK2 EK3} (op:TpExprBinOp EK1 EK2 EK3)
    (e1:TpExpr EK1) (e2:TpExpr EK2) : TpExpr EK3
.

(* The natural number N as a TpExpr *)
Definition TpExprN (n:nat) : TpExpr Kind_nat := @TpExpr_Const Kind_nat n.

(* The natural number 0 as a TpExpr *)
Definition TpExprZ : TpExpr Kind_nat := @TpExpr_Const Kind_nat 0.

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
| Tp_Vec (A : TpDesc) (e:TpExpr Kind_nat)
| Tp_Void

(* Inductive types and type variables *)
| Tp_Ind (A : TpDesc)
| Tp_Var (n : nat)

(* Explicit substitutions *)
| Tp_TpSubst (A : TpDesc) (B : TpDesc)
| Tp_ExprSubst (A : TpDesc) (EK:ExprKind) (e : TpExpr EK)
.


(**
 ** Deciding equality of type descriptions
 **)

Lemma dec_eq_ExprKind (EK1 EK2:ExprKind) : {EK1=EK2} + {~EK1=EK2}.
Proof. repeat decide equality. Qed.

Lemma dec_eq_exprKElem {EK} (elem1 elem2: exprKindElem EK)
  : {elem1=elem2} + {~elem1=elem2}.
Admitted.

Lemma dec_eq_KindDesc (K1 K2:KindDesc) : {K1=K2} + {~K1=K2}.
Proof. repeat decide equality. Qed.

Lemma dec_eq_TpExpr K (e1 e2 : TpExpr K) : {e1=e2} + {~e1=e2}.
Proof.
  revert e2; induction e1; intro e2; destruct e2; try (right; intro H0; discriminate H0).
  - destruct (dec_eq_exprKElem c c0).
    + rewrite e; left; reflexivity.
    + right; intro e; inversion e; apply inj_pairT2 in H0; apply n; assumption.
  - destruct (Nat.eq_dec ix ix0).
    + rewrite e; left; reflexivity.
    + right; intro e; inversion e; apply n; assumption.
  - destruct (dec_eq_ExprKind EK0 EK1).
    + subst EK0. destruct (dec_eq_UnOp op op0); [ destruct (IHe1 e2) | ].
      * subst op; subst e1; left; reflexivity.
      * right; intro e'; inversion e'; apply n.
        apply inj_pairT2 in H1. assumption.
      * right; intro e'; inversion e'; apply n.
        repeat apply inj_pairT2 in H0. assumption.
    + right; intro e; inversion e. apply n; symmetry; assumption.
  - destruct (dec_eq_ExprKind EK0 EK1); [ destruct (dec_eq_ExprKind EK3 EK2) | ].
    + subst EK0; subst EK3.
      destruct (dec_eq_BinOp op op0);
        [ destruct (IHe1_1 e2_1); [ destruct (IHe1_2 e2_2) | ] | ].
      * subst op0; subst e1_1; subst e1_2. left; reflexivity.
      * right; intro e'; inversion e'; apply n. apply inj_pairT2 in H2; assumption.
      * right; intro e'; inversion e'; apply n. apply inj_pairT2 in H1; assumption.
      * right; intro e'; inversion e'; apply n.
        repeat apply inj_pairT2 in H0. assumption.
    + right; intro e'; inversion e'; apply n; symmetry; assumption.
    + right; intro e'; inversion e'; apply n; symmetry; assumption.
Qed.

Definition dec_eq_TpDesc (T U:TpDesc) : { T = U } + {~ T = U}.
Proof.
(*
  repeat decide equality; try apply dec_eq_ExprKind. apply dec_eq_TpExpr.
Qed.
*)
Admitted.


(**
 ** Elements of kind descriptions
 **)

(* An element of a kind *)
Definition kindElem K : Type@{entree_u} :=
  match K with
  | Kind_Tp => TpDesc
  | Kind_Expr K' => exprKindElem K'
  end.

Definition defaultKindElem K : kindElem K :=
  match K return kindElem K with
  | Kind_Tp => Tp_Void
  | Kind_Expr EK => defaultEKElem EK
  end.


(**
 ** Substitution and evaluation for type descriptions
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


(* Substitute an environment into a variable of a particular kind at lifting
level n, meaning that the environment is a substitution for the variables
starting at n. Return the new value of the variable if it was substituted for
(meaning it has index n + i for some index i in the environment) or the new
variable number if it was not. *)
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

(* Substitute an environment at lifting level n into type-level expression e *)
Fixpoint substTpExpr n env {K} (e:TpExpr K) : TpExpr K :=
  match e in TpExpr K return TpExpr K with
  | TpExpr_Const _ c => TpExpr_Const c
  | TpExpr_Var _ ix =>
      match substVar n env (Kind_Expr _) ix with
      | inl e' => TpExpr_Const e'
      | inr ix' => TpExpr_Var ix'
      end
  | TpExpr_UnOp _ _ op e' => TpExpr_UnOp op (substTpExpr n env e')
  | TpExpr_BinOp _ _ _ op e1 e2 =>
      TpExpr_BinOp op (substTpExpr n env e1) (substTpExpr n env e2)
  end.

(* Evaluate a type-level expression to a value *)
Fixpoint evalTpExpr (env:TpEnv) {K} (e:TpExpr K) : exprKindElem K :=
  match e in TpExpr K return exprKindElem K with
  | TpExpr_Const _ c => c
  | TpExpr_Var _ ix => evalVar 0 env (Kind_Expr _) ix
  | TpExpr_UnOp _ _ op e => evalUnOp op (evalTpExpr env e)
  | TpExpr_BinOp _ _ _ op e1 e2 =>
      evalBinOp op (evalTpExpr env e1) (evalTpExpr env e2)
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
  | Tp_Vec A e => Tp_Vec (tpSubst n env A) (substTpExpr n env e)
  | Tp_Void => Tp_Void
  | Tp_Ind A => Tp_Ind (tpSubst (S n) env A)
  | Tp_Var var => match substVar n env Kind_Tp var with
                  | inl U => U
                  | inr var' => Tp_Var var'
                  end
  | Tp_TpSubst A B =>
      tpSubst n (@envConsElem Kind_Tp (tpSubst n env B) env) A
  | Tp_ExprSubst A EK e =>
      tpSubst n (@envConsElem (Kind_Expr EK) (evalTpExpr env e) env) A
  end.

(* Substitute a single value into a type description *)
Definition tpSubst1 {K} (elem:kindElem K) T : TpDesc :=
  tpSubst 0 (cons (existT kindElem K elem) nil) T.


(**
 ** Elements of type descriptions
 **)

(* Unfold an inductive type description Tp_Ind A by substituting the current
environment augmented with the mapping from deBruijn index 0 to Tp_Ind A *)
Definition unfoldIndTpDesc env A : TpDesc :=
  tpSubst 0 (@envConsElem Kind_Tp (tpSubst 0 env (Tp_Ind A)) env) A.

(* Inductively defined elements of a type description *)
Inductive indElem : TpEnv -> TpDesc -> Type@{entree_u} :=
| Elem_M {env R} (f:FunIx (tpSubst 0 env (Tp_M R))) : indElem env (Tp_M R)
| Elem_Pi {env A B} (f:FunIx (tpSubst 0 env (Tp_Pi A B))) : indElem env (Tp_Pi A B)
| Elem_Arr {env A B} (f:FunIx (tpSubst 0 env (Tp_Arr A B))) : indElem env (Tp_Arr A B)
| Elem_Kind {env K} (elem:kindElem K) : indElem env (Tp_Kind K)
| Elem_Pair {env A B} (elem1: indElem env A) (elem2: indElem env B)
  : indElem env (Tp_Pair A B)
| Elem_SumL {env A B} (elem: indElem env A) : indElem env (Tp_Sum A B)
| Elem_SumR {env A B} (elem: indElem env B) : indElem env (Tp_Sum A B)
| Elem_Sigma {env K B}
    (elem1: kindElem K) (elem2: indElem (envConsElem elem1 env) B)
  : indElem env (Tp_Sigma K B)
| Elem_VecNil {env A} : indElem env (Tp_Vec A TpExprZ)
| Elem_VecCons {env A n} (elem1: indElem env A)
    (elem2: indElem env (Tp_Vec A (TpExprN n)))
  : indElem env (Tp_Vec A (TpExprN (S n)))
| Elem_VecCast {env A e1 e2} (e: evalTpExpr env e1 = evalTpExpr env e2)
    (elem: indElem env (Tp_Vec A e1)) : indElem env (Tp_Vec A e2)
(* No case for Tp_Void *)
| Elem_Ind {env A} (elem: indElem nil (unfoldIndTpDesc env A))
  : indElem env (Tp_Ind A)
| Elem_Var {env} var (elem: indElem nil (evalVar 0 env Kind_Tp var)) :
  indElem env (Tp_Var var)
| Elem_TpSubst {env A B}
    (elem: indElem (@envConsElem Kind_Tp (tpSubst 0 env B) env) A)
  : indElem env (Tp_TpSubst A B)
| Elem_ExprSubst {env A EK e}
    (elem: indElem (@envConsElem (Kind_Expr EK) (evalTpExpr env e) env) A)
  : indElem env (Tp_ExprSubst A EK e)
.

(* Helper function to build a vector indElem with a constant size *)
Fixpoint mkVecIndElemConst {env T n} :
  VectorDef.t (indElem env T) n -> indElem env (Tp_Vec T (TpExprN n)) :=
  match n return VectorDef.t (indElem env T) n -> indElem env (Tp_Vec T (TpExprN n)) with
  | 0 => fun _ => Elem_VecNil
  | S n' =>
       fun elems =>
         Elem_VecCons (VectorDef.hd elems) (mkVecIndElemConst (VectorDef.tl elems))
  end.

(* Helper function to build a vector indElem from a vector of indElems *)
Definition mkVecIndElem {env T} {e:TpExpr Kind_nat}
  (elems:VectorDef.t (indElem env T) (evalTpExpr env e)) : indElem env (Tp_Vec T e).
  apply (Elem_VecCast (e1:=TpExprN (evalTpExpr env e))); [ reflexivity | ].
  apply mkVecIndElemConst. assumption.
Defined.


(* Elements of a type description relative to an environment *)
Fixpoint tpElemEnv env T : Type@{entree_u} :=
  match T with
  | Tp_M R => FunIx (tpSubst 0 env (Tp_M R))
  | Tp_Pi K B => FunIx (tpSubst 0 env (Tp_Pi K B))
  | Tp_Arr A B => FunIx (tpSubst 0 env (Tp_Arr A B))
  | Tp_Kind K => kindElem K
  | Tp_Pair A B => tpElemEnv env A * tpElemEnv env B
  | Tp_Sum A B => tpElemEnv env A + tpElemEnv env B
  | Tp_Sigma K B => { elem: kindElem K & tpElemEnv (envConsElem elem env) B }
  | Tp_Vec A e => VectorDef.t (tpElemEnv env A) (evalTpExpr env e)
  | Tp_Void => Empty_set
  | Tp_Ind A => indElem nil (unfoldIndTpDesc env A)
  | Tp_Var var => indElem nil (evalVar 0 env Kind_Tp var)
  | Tp_TpSubst A B =>
      tpElemEnv (@envConsElem Kind_Tp (tpSubst 0 env B) env) A
  | Tp_ExprSubst A EK e =>
      tpElemEnv (@envConsElem (Kind_Expr EK) (evalTpExpr env e) env) A
  end.

(* Elements of a type description = elements relative to the empty environment *)
Definition tpElem := tpElemEnv nil.

(* Convert an inductively-defined element to a recursively-defined one *)
Fixpoint indToTpElem env {T} (elem : indElem env T) : tpElemEnv env T.
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
  - apply elem.
  - apply elem.
  - simpl; apply indToTpElem; assumption.
  - simpl; apply indToTpElem; assumption.
Defined.

(* Convert a recursively-defined element to an inductively-defined one *)
Fixpoint tpToIndElem env {T} : tpElemEnv env T -> indElem env T.
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
  - destruct elem.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; apply tpToIndElem; assumption.
  - constructor; apply tpToIndElem; assumption.
Defined.


(**
 ** Function elements of type descriptions
 **)

(* A tuple of inputs to a functional type description *)
Fixpoint TpFunInput env (T:TpDesc) : Type@{entree_u} :=
  match T with
  | Tp_M _ => unit
  | Tp_Pi K B => { elem:kindElem K & TpFunInput (envConsElem elem env) B }
  | Tp_Arr A B => tpElemEnv env A * TpFunInput env B
  | _ => Empty_set
  end.

(* The output type of a monadic function of type T with the given inputs *)
Fixpoint TpFunOutput {env T} : TpFunInput env T -> Type@{entree_u} :=
  match T return TpFunInput env T -> Type with
  | Tp_M R => fun _ => tpElemEnv nil (tpSubst 0 env R)
  | Tp_Pi K B => fun args => TpFunOutput (projT2 args)
  | Tp_Arr A B => fun args => TpFunOutput (snd args)
  | _ => fun _ => Empty_set
  end.

(* The above define input and output function types for TpDescs *)
Global Instance IsTpDesc_TpDesc : IsTpDesc TpDesc :=
  {|
    FunInput := @TpFunInput nil;
    FunOutput := @TpFunOutput nil;
    dec_eq_Tp := dec_eq_TpDesc
  |}.

(* A monadic function of a given type description *)
Fixpoint funElem (E:EvType) env T : Type@{entree_u} :=
  match T with
  | Tp_M R => fixtree TpDesc E (tpElemEnv nil (tpSubst 0 env R))
  | Tp_Pi K B => forall (elem:kindElem K), funElem E (envConsElem elem env) B
  | Tp_Arr A B => tpElemEnv env A -> funElem E env B
  | _ => unit
  end.

(* Convert a monadic function to an FxInterp relative to an environment *)
Fixpoint funElemToInterpEnv {E env T} : funElem E env T ->
                                        forall args:TpFunInput env T,
                                          fixtree TpDesc E (TpFunOutput args) :=
  match T return funElem E env T ->
                 forall args:TpFunInput env T,
                   fixtree TpDesc E (TpFunOutput args) with
  | Tp_M R => fun m _ => m
  | Tp_Pi K B => fun f args => funElemToInterpEnv (f (projT1 args)) (projT2 args)
  | Tp_Arr A B => fun f args => funElemToInterpEnv (f (fst args)) (snd args)
  | _ => fun _ (v:Empty_set) => match v with end
  end.

(* Convert a monadic function to an FxInterp in the top-level environment *)
Definition funElemToInterp {E T} : funElem E nil T -> @FxInterp TpDesc _ E T :=
  funElemToInterpEnv.

(* Convert an FxInterp to a monadic function relative to an environment *)
Fixpoint funInterpToElemEnv {E env T} : (forall args:TpFunInput env T,
                                            fixtree TpDesc E (TpFunOutput args)) ->
                                        funElem E env T :=
  match T return (forall args:TpFunInput env T,
                     fixtree TpDesc E (TpFunOutput args)) ->
                 funElem E env T with
  | Tp_M R => fun f => f tt
  | Tp_Pi K B => fun f elem =>
                   funInterpToElemEnv (fun args => f (existT _ elem args))
  | Tp_Arr A B => fun f arg =>
                    funInterpToElemEnv (fun args => f (arg, args))
  | _ => fun _ => tt
  end.

(* Convert an FxInterp to a monadic function in the top-level environment *)
Definition funInterpToElem {E T} : @FxInterp TpDesc _ E T -> funElem E nil T :=
  funInterpToElemEnv.
