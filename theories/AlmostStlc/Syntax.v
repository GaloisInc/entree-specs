Require Export MrecMonad.
Require Export HeterogeneousRelations.
Require Export EnTreeDefinition.
From Coq Require Import Lists.List.


Inductive var {T : Type} : T -> list T -> Type := 
  | VarZ (x : T) l : var x (x :: l)
  | VarS (x y : T) l : var x l -> var x (y :: l).


Inductive type : Type :=
  | Nat : type
  | List : type -> type
                   (* should really be a nonempty list *)
  | Arrow : type -> list (type * type) -> type -> type
.
Notation ctx := (list type).
Notation rec_ctx := (list (type * type))%type.



(*TODO : add some basic natural number operations *)
Inductive term : type -> ctx -> rec_ctx -> Type := 
  | term_const (n : nat) Γ R : term Nat Γ R
  | term_nil t Γ R : term (List t) Γ R
  | term_cons t Γ R (head : term t Γ R) (tail : term (List t) Γ R) : term (List t) Γ R
  | term_var t Γ R (x : var t Γ) : term t Γ R

  | term_match_nat t Γ R (en : term Nat Γ R) (eZ : term t Γ R) (eS : term t (Nat :: Γ) R ) : term t Γ R
  | term_match_list t1 t2 Γ R (el : term (List t1) Γ R ) (enil : term t2 Γ R) (econs : term t2 (t1 :: Γ) R) : term t2 Γ R
  (* might be some subtleties in the application rule you are not sufficiently considering *)
  | term_app t1 t2 Γ R (e1 : term (Arrow t1 R t2) Γ R) (e2 : term t1 Γ R) : term t2 Γ R
  (* same here *)
  | term_abs t1 t2 Γ R R' (e : term t2 (t1 :: Γ) R') : term (Arrow t1 R' t2) Γ R
  | term_call t1 t2 Γ R (x : var (t1,t2) R) (arg : term t1 Γ R) : term t2 Γ R
  (* this is the most novel part so be very careful *)
  | term_mfix t Γ R R' (bodies : mfix_bodies Γ R R) (e : term t Γ R) : term t Γ R'


with mfix_bodies : ctx -> rec_ctx -> rec_ctx -> Type := 
  | mfix_bodies_nil Γ R : mfix_bodies Γ R nil
  | mfix_bodies_cons Γ R t1 t2 R' (body : term t2 (t1 :: Γ) R) : mfix_bodies Γ R ((t1,t2) :: R')
.


Variant void : Set := .
Global Instance voidEncodedType : EncodedType void := fun v => match v with end.

Fixpoint denote_rec_ctx (Rt Rc : list (Type * Type) ) : Type@{entree_u} :=
  match Rc with
  | nil => void
  | cons (T1, _)  Rc => T1 + denote_rec_ctx Rt Rc end.

Fixpoint encoded_rec_ctx (Rt Rc : list (Type * Type)) : EncodedType (denote_rec_ctx Rt Rc) :=
  match Rc with
  | nil => fun _ => void
  | cons (_, T2) Rc' => fun x => match x with 
                             | inl y => T2
                             | inr y => encoded_rec_ctx Rt Rc' y end end.

(* need callE *)
Set Printing Universes.
(* universe inconsistenty, need to be more careful about universe levels*)
Fixpoint denote_type (t : type) : Type@{entree_u} :=
  match t with
  | Nat => nat
  | List t => list (denote_type t)
  | Arrow t1 R t2 => 
      let R' := List.map (fun '(t1,t2) => (denote_type t1, denote_type t2)) R in
      denote_type t1 -> mtree (denote_rec_ctx R' R') (denote_type t2)
  end.
with denote_rec_ctx (R : rec_ctx) : {T : Type & EncodedType T} :=
   match R with
   | nil => existT void voidEncodedType
   | (t1,t2) :: R' =>
       existT ()

(* Fixpoint subst_term t1 t2 Γ R (e : ) *)


(*
TODO: substitution, value, small step semantics
      mrec monad, denotational semantics

      prove denotational semantics is adequate wrt small step

      

*)
