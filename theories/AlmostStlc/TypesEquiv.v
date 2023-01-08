Require Export TypedVar.
Require Export SyntaxSeq.
Require Export SmallStepSeq.
Require Export DenotationFacts.
Require Export DenotationSeq.
Require Export Rutt.
Require Export RuttFacts.
Require Import ITree.Basics.HeterogeneousRelations.
Import List.ListNotations.
Open Scope list_scope.
From Equations Require Import Equations Signature.
Require Import Coq.Program.Equality.
Require Import ExtLib.Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

Inductive list_rel {A} (R : Rel A A): Rel (list A) (list A) :=
  | list_rel_nil : list_rel R nil nil
  | list_rel_cons a b l1 l2 : R a b ->list_rel R l1 l2 -> list_rel R (cons a l1) (cons a l2).

Section types_equiv.

(*

Inductive types_equiv : forall t : type, Rel (denote_type t) (denote_type t) := 
  | types_equiv_Nat n : types_equiv Nat n n
  | types_equiv_Pair t1 t2 p1 p2 : prod_rel (types_equiv t1) (types_equiv t2) p1 p2 ->
                                   types_equiv (Pair t1 t2) p1 p2
  | types_equiv_List t l1 l2 : list_rel (types_equiv t) l1 l2 ->
                               types_equiv (List t) l1 l2
  | types_equiv_Arrow t1 MR t2 f g : 
    (forall x y, types_equiv t1 x y -> rutt hole hole (types_equiv t2) (f x) (g x) ) ->
    types_equiv (Arrow t1 MR t2) f g
.
the arrow type requires non strict positive application, needs to be a fixpoint


*)

(* seems to not be recognizing  that this is well founded, probably a dependent 
   pattern matching problem, first thing to try might be to do this in equations
   after that maybe consider some gas-like solution

   this might take much of tomorrow, I am concerned about the march deadline,
   but if we miss it thats not really a problem talk about the next deadline with steve next week

  *)
(* maybe also create a generalized version of this so that we can get some more 
   general equational theory working 
   maybe also a relation for any mtree, built on top of rutt and do some of the 
   theory at that level
*)
Equations types_equiv (t : type) : Rel (denote_type t) (denote_type t) := {
    types_equiv Nat := eq;
    types_equiv (Pair t1 t2) := prod_rel (types_equiv t1) (types_equiv t2);
    types_equiv (List t) := list_rel (types_equiv t);
    types_equiv (Arrow t1 MR t2) :=
    fun f g => forall x y, types_equiv t1 x y -> 
                   rutt (mfix_pre_equiv MR) (mfix_post_equiv MR) (types_equiv t2) (f x) (g y)
}
where mfix_pre_equiv (MR : mfix_ctx) : 
  Rel (denote_mrec_ctx (denote_mfix_ctx MR)) (denote_mrec_ctx (denote_mfix_ctx MR)) :=
{
  mfix_pre_equiv nil := fun _ _ => False;
  mfix_pre_equiv (cons cf MR) :=
    sum_rel (call_frame_pre_equiv cf) (mfix_pre_equiv MR);
}
where call_frame_pre_equiv (cf : call_frame) :
  Rel (denote_call_frame cf) (denote_call_frame cf) := 
{
  call_frame_pre_equiv nil := fun _ _ => False;
  call_frame_pre_equiv (cons (t1,t2) cf') :=
    sum_rel (types_equiv t1) (call_frame_pre_equiv cf')
}
where mfix_post_equiv (MR : mfix_ctx) : 
  PostRel (denote_mrec_ctx (denote_mfix_ctx MR)) (denote_mrec_ctx (denote_mfix_ctx MR)) :=
{
  mfix_post_equiv nil := fun _ _ _ _ => False;
  mfix_post_equiv (cons cf MR) := SumPostRel (call_frame_post_equiv cf) (mfix_post_equiv MR);
}
where call_frame_post_equiv (cf : call_frame) : 
  PostRel (denote_call_frame cf) (denote_call_frame cf) :=
{
  call_frame_post_equiv nil := fun _ _ _ _ => False;
  call_frame_post_equiv (cons (t1,t2) cf ) :=
    SumPostRel (fun _ _ => types_equiv t2) (call_frame_post_equiv cf);
}.
(* use to create relations for [Γ] -> mtree [MR] [t] *)

Fixpoint ctx_equiv (Γ : ctx) : Rel (denote_ctx Γ) (denote_ctx Γ) :=
  match Γ with
  | nil => fun _ _ => True
  | cons t Γ => prod_rel (types_equiv t) (ctx_equiv Γ)
  end.

Definition comp_equiv {t Γ MR} :=
    fun c1 c2 => forall hyps1 hyps2, ctx_equiv Γ hyps1 hyps2 ->
              rutt (mfix_pre_equiv MR) (mfix_post_equiv MR) (types_equiv t) (c1 hyps1) (c2 hyps2).


(*
Should be a PER 


rewrite with eutt

it should generalize eutt

should be the case that if it is a denotation, then it is self related
so it acts as an equivalence relation on its actual domain


tomorrow would be a good time to get a basic sketch of rutt done at least,
leave implementations of lemmas for later, there is a sense in which it is not
along a critical path because it is known to be true, where as
other things might actually include some bugs

on monday work on this but also dedicate some time to the proposal intro


*)
