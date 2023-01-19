Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.

Require Import ITree.Basics.Basics.
Require Import HeterogeneousRelations.

Section entree.

Context (E : Type@{entree_u}) `{EncodedType E} (R : Type@{entree_u}).

Variant entreeF (F : Type@{entree_u} ) : Type@{entree_u} :=
  | RetF (r : R)
  | TauF (t : F)
  | VisF (e : E) (k : encodes e -> F ).

CoInductive entree : Type@{entree_u} :=
  go { _observe : entreeF entree }.

End entree.

Arguments entree _ {_} _.
Arguments entreeF _ {_} _ _ .
Arguments RetF {_ _ _ _} _.
Arguments TauF {_ _ _ _} _.
Arguments VisF {_ _ _ _} _ _.
Notation entree' E R := (entreeF E R (entree E R)).
Notation Tau t := {| _observe := TauF t |}.
Notation Ret r := {| _observe := RetF r |}.
Notation Vis e k := {| _observe := VisF e k |}.

Definition observe {E R} `{EncodedType E} (t : entree E R) : entree' E R :=
  _observe _ _ t.


Declare Scope entree_scope.
Bind Scope entree_scope with entree.
Delimit Scope entree_scope with entree.
Local Open Scope entree_scope.
Create HintDb itree.


Module EnTree.

Definition subst' {E : Type@{entree_u}} `{EncodedType E} {R S : Type@{entree_u}}
           (k : R -> entree E S) : entree' E R -> entree E S  :=
  cofix _subst (ot : entree' E R) :=
    match ot with
    | RetF r => k r
    | TauF t => Tau (_subst (observe t))
    | VisF e k => Vis e (fun x => _subst (observe (k x)))
    end.

Definition subst {E : Type@{entree_u}} `{EncodedType E} {R S : Type@{entree_u}}
           (k : R -> entree E S) : entree E R -> entree E S :=
  fun t => subst' k (observe t).

Definition bind {E} `{EncodedType E} {R S : Type@{entree_u}} 
           (t : entree E R) (k : R -> entree E S) :=
  subst k t.

Definition iter {E} `{EncodedType E} {I R : Type@{entree_u}}
           (body : I -> entree E (I + R) ) : I -> entree E R :=
  cofix _iter i :=
    bind (body i) (fun ir => match ir with
                          | inl i' => Tau (_iter i')
                          | inr r => Ret r
                          end).

Definition map {E} `{EncodedType E} {R S} (f : R -> S) (t : entree E R) :=
  bind t (fun r => Ret (f r)).

Definition trigger {E} `{EncodedType E} (e : E) : entree E (encodes e) :=
  Vis e (fun x => Ret x).

CoFixpoint spin {E R} `{EncodedType E} : entree E R := Tau spin.

(* are there multiple definitions of trigger ? *)

End EnTree.

Module EnTreeNotations.

Notation "t1 >>= k2" := (EnTree.bind t1 k2)
                        (at level 58, left associativity) : entree_scope.
Notation "x <- t1 ;; t2" := (EnTree.bind t1 (fun x => t2) )
                        (at level 61, t1 at next level, right associativity) : entree_scope.
Notation "t1 ;; t2" := (EnTree.bind t1 (fun _ => t2))
                       (at level 61, right associativity) : entree_scope.
Notation "' p <- t1 ;; t2" :=
  (EnTree.bind t1 (fun x_ => match x_ with p => t2 end) )
  (at level 61, t1 at next level, p pattern, right associativity) : entree_scope.


End EnTreeNotations.

#[global] Instance Functor_entree {E} `{EncodedType E} : Functor (entree E) :=
  { fmap := @EnTree.map E _ }.

#[global] Instance Applicative_entree {E} `{EncodedType E} : Applicative (entree E) :=
  {
    pure := fun _  x => Ret x;
    ap := fun _ _ f x =>
            EnTree.bind f (fun f => EnTree.bind x (fun x => Ret (f x)) );

  }.

#[global] Instance Monad_entree {E} `{EncodedType E} : Monad (entree E) :=
  {
    ret := fun _ x => Ret x;
    bind := @EnTree.bind E _;
  }.

#[global] Instance MonadIter_entree {E} `{EncodedType E} : MonadIter (entree E) :=
  fun _ _ => EnTree.iter.




(* Import ITree basics*)

Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.

Ltac rewrite_everywhere lem :=
  progress ((repeat match goal with [H: _ |- _] => rewrite lem in H end); repeat rewrite lem).
Ltac rewrite_everywhere_except lem X :=
  progress ((repeat match goal with [H: _ |- _] =>
                 match H with X => fail 1 | _ => rewrite lem in H end
             end); repeat rewrite lem).
Ltac genobs x ox := remember (observe x) as ox.
Ltac genobs_clear x ox := genobs x ox; match goal with [H: ox = observe x |- _] => clear H x end.
Ltac simpobs := repeat match goal with [H: _ = observe _ |- _] =>
                    rewrite_everywhere_except (@eq_sym _ _ _ H) H
                end.
Ltac desobs t H := destruct (observe t) eqn:H.
