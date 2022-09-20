From Coq Require Import
     Program
     Setoid
     Morphisms
     Relations.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Tacs
     Basics.HeterogeneousRelations
     Eq.Paco2.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Core.SubEvent
.

Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.

Require Import ITree.Basics.Basics.

Require Export TypedVar.

From Equations Require Import Equations Signature.

Variant void : Set := .
Global Instance voidEncodedType : EncodedType void := fun v => match v with end.


Fixpoint denote_rec_ctx (R: list (Type * Type) ) : Type@{entree_u} :=
  match R with
  | nil => void
  | cons (T1, _)  R => T1 + denote_rec_ctx R end.
(*
Definition fold_rec_ctx_inr' (Rt Rc : list (Type * Type)) T1 T2 (arg : denote_rec_ctx' Rt Rc) : denote_rec_ctx' Rt ((T1,T2) :: Rc) :=
  inr arg.
*)
Fixpoint encoded_rec_ctx (R : list (Type * Type)) : EncodedType (denote_rec_ctx R) :=
  match R with
  | nil => fun _ => void
  | cons (_, T2) R => fun x => match x with 
                             | inl y => T2
                             | inr y => encoded_rec_ctx R y end 
  end.

Global Instance encoded_rec_ctx_instance R : EncodedType (denote_rec_ctx R) := encoded_rec_ctx R.

Definition mtree (R : list (Type * Type)) (A : Type) : Type@{entree_u} :=
  @entree (denote_rec_ctx R) (encoded_rec_ctx R) A.
Notation mtree' R A := (entree' (denote_rec_ctx R) A).
(* call *)

(* the pattern is correct but I need to rethink this a bit
   also this should be named bring to front

*)
(*
maybe try to write int terms of permutations, a permutation refl function would be useful


*)
(*
The term "inr e0" has type
 "(In * (Out -> A) +
   {e : denote_rec_ctx (remove (In, Out) R y) & encodes e -> A})%type"
while it is expected to have type
 "(In * (Out -> A) +
   {e
   : denote_rec_ctx
       (remove (In, Out) ((T1, T2) :: R) (VarS (In, Out) (T1, T2) R y)) &
   encodes e -> A})%type"

*)

Equations bring_to_front {A : Type} (R : list (Type * Type)) (In Out : Type)
          (x : var (In,Out) R)
          (e : denote_rec_ctx R)
          (k : encodes e -> A)
  : (In * (Out -> A)) + {e : denote_rec_ctx (remove (In,Out) R x) & encodes e -> A}   :=
  bring_to_front ((In,Out) :: R) In Out (VarZ _ R) (inl i) k :=
    inl (i, k);
  bring_to_front ((In,Out) :: R) In Out (VarZ _ R) (inr e) k := inr (existT _ e k);
  bring_to_front ((T1,T2) :: R) In Out (VarS _ _ R y) (inl i) k := inr (existT _ (inl i) k);
  bring_to_front ((T1,T2) :: R) In Out (VarS _ _ R y) (inr e) k :=
    match bring_to_front R In Out y e k with
    | inl (i,k ) => inl (i, k)
    | inr (existT _ e k) => inr (existT _ (inr e) k )
    end.

Lemma bring_to_front_k_inl_jmeq : forall A R In Out (x : var (In,Out) R) (e : denote_rec_ctx R) (k : encodes e -> A) i k',
    bring_to_front R In Out x e k = inl (i, k') -> k ~= k'.
Proof.
  intros A R In Out x. dependent induction x.
  - intros [ | ]; intros; try discriminate.
    simp bring_to_front in H. injection H. intros. subst. auto.
  - destruct b. cbn. intros [ | ]; try discriminate.
    simp bring_to_front. intros. eapply IHx; eauto. Unshelve. all : auto.
    simp bring_to_front in H. destruct (bring_to_front l In Out x d k) as [ | ]; try discriminate.
    + destruct p. injection H. intros. subst. auto.
    + destruct s. discriminate.
Qed.


Lemma bring_to_front_k_inr_jmeq : forall A R In Out (x : var (In,Out) R) (e : denote_rec_ctx R) (k : encodes e -> A) e' k',
    bring_to_front R In Out x e k = inr (existT _ e' k') -> k ~= k'.
Proof.
  intros A R In Out x. dependent induction x.
  - intros [ | ]; intros; try discriminate. simp bring_to_front in H.
    cbn in *.  setoid_rewrite bring_to_front_equation_3 in H.
    injection H. intros. subst. dependent destruction H0. auto.
  - destruct b. cbn in *. intros [ | ]; intros; try discriminate.
    + intros. simp bring_to_front in H. injection H. intros. subst.
      match goal with H : inr ?a1 = inr ?a2 |- _ => remember a1 as ek1; remember a2 as ek2; 
                                                  assert (ek1 = ek2) end.
      injection H. intros; auto.
      rewrite Heqek1 in H0. rewrite Heqek2 in H0.
      apply inj_pair2 in H0. subst. auto.
    + cbn in H. simp remove in *. simp bring_to_front in H.
      destruct (bring_to_front l In Out x d k ) as [ | ] eqn :Heq.
      * destruct p. discriminate.
      * destruct s as [e k''].
        injection H. intros. subst. eapply IHx; eauto.
        rewrite Heq.
        match goal with H : inr ?a1 = inr ?a2 |- _ => remember a1 as ek1; remember a2 as ek2; 
                                                  assert (ek1 = ek2) end.
        { injection H. auto. }
        clear H. rewrite Heqek1 in H0. rewrite Heqek2 in H0.
        apply inj_pair2 in H0. subst. auto.
Qed.

(*
Equations bring_to_front (R : list (Type * Type)) (In Out : Type)
          (x : var (In,Out) R)
          (e : denote_rec_ctx R) 
          
  : In + denote_rec_ctx (remove (In,Out) R x)  :=
  bring_to_front ((In,Out) :: R) In Out (VarZ _ R) (inl i) :=
    inl i;
  bring_to_front ((In,Out) :: R) In Out (VarZ _ R) (inr e) := inr e;
  bring_to_front ((T1,T2) :: R) In Out (VarS _ _ R y) (inl i) := inr (inl i);
  bring_to_front ((T1,T2) :: R) In Out (VarS _ _ R y) (inr e) :=
    match bring_to_front  R In Out y e with
    | inl i => inl i
    | inr e => inr (inr e) 
    end.
*)
(*essentially, we want a proof *)
(*
Equations bring_to_front_k {A} (R : list (Type * Type)) (In Out : Type)
          (x : var (In,Out) R)
          (e : denote_rec_ctx R)
          (k : encodes e -> A)
          () : A :=
  bring_to_front_k ((In,Out) :: R) In Out (VarZ _ R) k (inl i) := (k (inl i));
  brint_to_front_k ((In,Out) :: R) In Out (VarZ _ R) k (inr e') := (k e').
*)

(* 
(* don't know if the f does much here *)
R (T1,T2) (x : var (T1,T2) R) (e : denote_rec_ctx R) (f : T1 -> A) -> T1 + denote_rec_ctx (remove x R)

*)

Section interp_mtree.
Context (R : list (Type * Type)) (In Out: Type) (x : var (In,Out) R).

Context (body : forall i : In, mtree R Out).

CoFixpoint interp_mtree' {A} (om : mtree' R A) : mtree (remove (In, Out) R x) A :=
  match om with
  | RetF r => Ret r
  | TauF t => Tau (interp_mtree' (observe t))
  | VisF e k => 
      match bring_to_front R In Out x e k with
      (* need to inject out into encodes e or change k*)
      | inl (i, k') => Tau (interp_mtree' (observe (EnTree.bind (body i) k')))
      | inr (existT _ e' k') => Vis e' (fun x  => interp_mtree' (observe (k' x)) )
      end
  end.

Definition interp_mtree {A} (m : mtree R A) : mtree (remove (In, Out) R x) A :=
  interp_mtree' (observe m).

End interp_mtree.
