Require Import Coq.Lists.List.
Require Import Coq.Logic.JMeq. 
From Equations Require Import Equations Signature.
Require Import Coq.Program.Equality.
Open Scope list_scope.
Import ListNotations.
Inductive var {A : Type} : A -> list A -> Type := 
  | VarZ (a : A) l : var a (a :: l)
  | VarS (a b : A) l : var a l -> var a (b :: l).

Equations remove {A : Type} (a : A) (l : list A) (x : var a l) : list A :=
  remove a (a :: l) (VarZ a l) := l;
  remove a (b :: l) (VarS _ _ y) := b :: (remove a l y).

Inductive var_eq {A : Type} : forall (a b : A) (l : list A), var a l -> var b l -> Type :=
  | var_eq_ZZ a l : var_eq a a (a :: l) (VarZ a l) (VarZ a l)
  | var_eq_SS a b c l x y : var_eq a b l x y -> var_eq a b (c :: l) (VarS a c l x) (VarS b c l y).

Inductive var_neq {A : Type} : forall (a b : A) (l : list A), var a l -> var b l -> Type :=
  | var_neq_ZS a b l x : var_neq a b (a :: l) (VarZ a l) (VarS b a l x)
  | var_neq_SZ a b l x : var_neq a b (b :: l) (VarS a b l x) (VarZ b l)
  | var_neq_SS a b c l x y : 
    var_neq a b l x y -> var_neq a b (c :: l) (VarS a c l x) (VarS b c l y)
.
Arguments var_eq  {_ _ _ _}.
Arguments var_neq {_ _ _ _}.

Equations var_eq_neq {A} (a b : A) (l : list A) (x : var a l) (y : var b l) : var_eq x y + var_neq x y:=
  var_eq_neq _ _ _ (VarZ a l) (VarZ a l) := inl (var_eq_ZZ a l);
  var_eq_neq _ _ _ (VarZ a l) (VarS b a l y) := inr (var_neq_ZS a b l y);
  var_eq_neq _ _ _ (VarS a b l x) (VarZ b l) := inr (var_neq_SZ a b l x);
  var_eq_neq _ _ _ (VarS a c l x) (VarS b c l y) := match (var_eq_neq a b l x y) with
                                                    | inl e => inl (var_eq_SS a b c l x y e)
                                                    | inr n => inr (var_neq_SS a b c l x y n) end.

Equations var_neq_sym {A} {a b : A} {l} (x : var a l) (y : var b l) (Hn : var_neq x y) : var_neq y x :=
  var_neq_sym a b (var_neq_ZS a b l x) := var_neq_SZ b a l x;
  var_neq_sym a b (var_neq_SZ a b l x) := var_neq_ZS b a l x;
  var_neq_sym a b (var_neq_SS a b c l x y Hn) := var_neq_SS b a c l y x (var_neq_sym x y Hn).



Lemma var_eq_surj A (a b : A) (l : list A) (x : var a l) (y : var b l) :
  var_eq x y -> a = b.
Proof.
  intros Heq. induction Heq; auto.
Qed.

Lemma var_eq_eq A (a : A) l (x y : var a l) : var_eq x y -> x = y.
Proof.
  intros Heq. dependent induction Heq.
  auto. erewrite IHHeq; eauto.
Defined.

Equations var_eq_eq' {A} {a b : A} {l : list A} (x : var a l) (y : var b l) (Heq : var_eq x y) :
  a = b :=
  var_eq_eq' _ _ (var_eq_ZZ _ _) := eq_refl;
  var_eq_eq' _ _ (var_eq_SS _ _ _ _ x y Heq) :=
    var_eq_eq' x y Heq.

Equations var_eq_elim {A} {ll : list (list A)} {l1 l2 : list A} {a : A}
          (xl : var l1 ll) (yl : var l2 ll) (Heq : var_eq xl yl) (x : var a l2) : var a l1 :=
  var_eq_elim _ _ (var_eq_ZZ _ _) x := x;
  var_eq_elim _ _ (var_eq_SS _ _ _ _ xl yl Heq) x :=
    var_eq_elim xl yl Heq x.


Lemma var_neq_JMeq A (a b : A) (l : list A) (x : var a l) (y : var b l) : JMeq x y \/ (exists n : var_neq x y, True) .
Proof.
  specialize (var_eq_neq a b l x y) as [ | ].
  - assert (a = b). apply var_eq_surj in v; auto. subst. 
    left. apply var_eq_eq in v. subst. auto.
  - right. eauto.
Qed.

Equations var_eqb {A : Type} {l : list A} {a b} (x : var a l) (y : var b l) : bool :=
  var_eqb (VarZ a l) (VarZ a l) := true;
  var_eqb (VarS a c l x) (VarS b c l y) := var_eqb x y;
  var_eqb _ _ := false.
(*
Inductive var_eq {A : Type} : forall (a b : A) (l : list A), var a l -> var b l -> Type := .
*)
(*
Definition remove_var {A : Type} (a b : A) (l : list A) (x : var a l) (y : var b l) 
  (vn : var_neq x y) : var b (remove a l x).
induction vn.
- exact x.
- exact (VarZ b (remove a l x)).
- exact (VarS b c (remove a l x) IHvn).
Defined.
*)

  

Equations remove_var {A : Type} (a b : A) (l : list A) (x : var a l) (y : var b l) 
  (vn : var_neq x y) : var b (remove a l x) :=
  remove_var a b _ _ _ (var_neq_ZS a b _ x)  := x;
  remove_var a b _ _ _ (var_neq_SZ a b _ x) := VarZ b (remove a _ x);
  remove_var a b _ _ _ (var_neq_SS a b c l x y vn) := VarS b c (remove a _ x) (remove_var a b _ x y vn).


Equations append_var {A : Type} (l1 l2 : list A) (a : A) (x : var a l1) : var a (l1 ++ l2) :=
  append_var (a :: l1) l2 a (VarZ a l1) := VarZ a (l1 ++ l2);
  append_var (b :: l1) l2 a (VarS a b l1 y) := VarS a b (l1 ++ l2) (append_var l1 l2 a y).


Inductive perm {A : Type} : list A -> list A -> Type :=
  | perm_nil : perm nil nil
  | perm_skip x l1 l2 : perm l1 l2 -> perm (x :: l1) (x :: l2)
  | perm_swap x y l1 l2 : perm l1 l2 -> perm (x :: y :: l1) (y :: x :: l2)
  | perm_trans l1 l2 l3 : perm l1 l2 -> perm l2 l3 -> perm l1 l3.

Derive Signature NoConfusion for perm.

Fixpoint perm_refl {A : Type} (l : list A) : perm l l :=
  match l with
  | nil => perm_nil
  | x :: l' => perm_skip x l' l' (perm_refl l') 
  end.

(*
Definition perm_var {A : Type} (a : A) l1 l2 (x : var a l1) (Hperm : perm l1 l2) : 
  var a l2.
revert x. induction Hperm.
- intros. inversion x.
- intros. inversion x0; subst.
  + apply VarZ.
  + apply VarS. apply IHHperm. exact X.
- intros. inversion x0; subst.
  + apply VarS. apply VarZ.
  + inversion X; subst.
    * apply VarZ.
    * apply VarS. apply VarS. apply IHHperm. apply X0.
- intro. apply IHHperm2. apply IHHperm1. exact x.
Defined.
*)

(* takes a long time to compile *)
Equations perm_var {A : Type} (a : A) l1 l2 (x : var a l1) (Hperm : perm l1 l2) : 
  var a l2 :=
  perm_var a (a :: l1) (a :: l2) (VarZ a l1)  (perm_skip _ _ _) := VarZ a l2;
  perm_var a (b :: l1) (b :: l2) (VarS a b l1 y) (perm_skip b l1 l2 Hperm) := VarS a b _ (perm_var a l1 l2 y Hperm);
  perm_var a (a :: _ ) (b :: _) (VarZ a _) (perm_swap a b l1 l2 _) :=
    VarS a b (a :: l2) (VarZ a l2);
  perm_var a (b :: _) (a :: _) (VarS a b _ (VarZ a l1))  (perm_swap b a l1 l2 _) :=
    VarZ a (b :: l2);
  perm_var a (b :: _) (c :: _) (VarS a b _ (VarS a c l1 y)) (perm_swap _ _ l1 l2 Hperm) :=
    VarS a c _ (VarS a b _ (perm_var a l1 l2 y Hperm));
  perm_var b l1' l3' y (perm_trans l1' l2' l3' Hperm12 Hperm23) :=
    perm_var b l2' l3' (perm_var b l1' l2' y Hperm12) Hperm23.


Equations bring_to_front_perm {A : Type} (a : A) (l : list A) (x : var a l) :
  perm l (a :: remove a l x) :=
  bring_to_front_perm a (a :: l) (VarZ _ l) := perm_refl (a :: l);
  bring_to_front_perm a (b :: l') (VarS a b l' y) :=  
    perm_trans (b :: l') (b :: a :: remove a l' y) (a :: b :: remove a l' y)
     (perm_skip b l' (a :: remove a l' y)
                   (bring_to_front_perm a l' y)) 
     (perm_swap  b a (remove a l' y) (remove a l' y) (perm_refl _)) .

Equations perm_map {A B : Type} {f : A -> B} {l1 l2 : list A} (Hperm : perm l1 l2) :
  perm (List.map f l1) (List.map f l2) :=
  perm_map  perm_nil := perm_nil;
  perm_map (perm_skip x l1 l2 Hperm) := perm_skip (f x) _ _ (perm_map Hperm);
  perm_map (perm_swap x y l1 l2 Hperm) :=
    perm_swap (f x) (f y) _ _ (perm_map  Hperm);
  @perm_map _ _ f l1 l3 (perm_trans l1 l2 l3 Hperm12 Hperm23) :=
    perm_trans (map f l1) (map f l2) (map f l3) (perm_map Hperm12) (perm_map Hperm23).
Arguments VarZ {_ _ _}.
Arguments VarS {_ _ _ _}.
Arguments perm_trans {_ _ _ _}.
Arguments perm_swap {_ _ _ _ _}.
Arguments perm_refl {_ _ }.
Arguments perm_skip {_ _ _ _}.
Arguments perm_var {_ _ _ _}.


Lemma perm_var_trans A (a : A) l1 l2 l3 (x : var a l1) (Hperm1 : perm l1 l2) (Hperm2 : perm l2 l3)
      : perm_var x (perm_trans Hperm1 Hperm2) =
          perm_var (perm_var x Hperm1) Hperm2.
Proof.
  dependent destruction x.
  - destruct l3; simp perm_var; auto.
  - destruct l3; simp perm_var; auto.
Qed.

Definition weaken_var_r {A} : forall (l1 l2 : list A) (a : A), var a l1 -> var a (l1 ++ l2) := @append_var A.

Equations weaken_var_l {A} (l1 l2 : list A) (a : A) (x : var a l2) : var a (l1 ++ l2) :=
  weaken_var_l nil l2 a x := x;
  weaken_var_l (b :: l1) l2 a x := VarS (weaken_var_l l1 l2 a x). 
Transparent weaken_var_l.
Equations swap_var {A} (l: list A) (a b c: A) (x : var a ([b] ++ [c] ++ l) ) :
  var a ([c] ++ [b] ++ l) :=
  swap_var l a a c VarZ :=  VarS VarZ;
  swap_var l a b a (VarS VarZ) := VarZ;
  swap_var l a b c (VarS (VarS y) ) := VarS (VarS y).


Equations weaken_var_mid {A} (l1 l2 l3 : list A) (a : A) (x : var a (l1 ++ l3) ) :
  var a (l1 ++ l2 ++ l3)  :=
  weaken_var_mid (b :: l1) _ _ b VarZ := VarZ;
  weaken_var_mid (b :: l1) l2 l3 a (VarS y) := VarS (weaken_var_mid _ _ _ a y);
  weaken_var_mid nil l2 l3 a y := weaken_var_l l2 l3 a y.

Equations exchange_var_r_perm {A} (l1 l2 : list A) (a b : A) : 
  perm ([a] ++ l1 ++ [b] ++ l2) ([b] ++ l1 ++ [a] ++ l2) :=
  exchange_var_r_perm [] l2 a b := perm_swap perm_refl;
  exchange_var_r_perm (c :: l1) l2 a b :=
    let IHl2 := exchange_var_r_perm l1 l2 a b in
    perm_trans (perm_swap perm_refl) (perm_trans (perm_skip IHl2) (perm_swap perm_refl)).

Equations exchange_var_perm {A} (G1 G2 G3 : list A) (u1 u2 : A) :
  perm (G1 ++ [u1] ++ G2 ++ [u2] ++ G3) (G1 ++ [u2] ++ G2 ++ [u1] ++ G3 ) :=
  exchange_var_perm [] G2 G3 u1 u2 := exchange_var_r_perm G2 G3 u1 u2;
  exchange_var_perm (c :: G1) G2 G3 u1 u2 :=
    perm_skip (exchange_var_perm G1 G2 G3 u1 u2).

Definition exchange_var {A} (G1 G2 G3 : list A) (u1 u2 t : A) 
           (x : var t (G1 ++ [u1] ++ G2 ++ [u2] ++ G3)) : 
  var t (G1 ++ [u2] ++ G2 ++ [u1] ++ G3 ) :=
  perm_var x (exchange_var_perm G1 G2 G3 u1 u2).

Equations var_map_skip {A} (l1 l2 : list A) (b : A) (f : forall c, var c l1 -> var c l2) a
          (x : var a (b :: l1)) : var a (b :: l2) :=
  var_map_skip l1 l2 _ _ f VarZ := VarZ;
  var_map_skip l1 l2 _ _ f (VarS y) := VarS (f _ y).

Arguments var_map_skip {_ _ _ _}.
