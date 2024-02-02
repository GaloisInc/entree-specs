Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.

Require Import ITree.Basics.Basics.
Require Import HeterogeneousRelations.


(*** The definition of entrees ***)
Section entree.

Context (E : Type@{entree_u}) `{EncodingType E} (R : Type@{entree_u}).

(* The functor defining a single constructor of an entree *)
Variant entreeF (F : Type@{entree_u} ) : Type@{entree_u} :=
  | RetF (r : R)
  | TauF (t : F)
  | VisF (e : E) (k : encodes e -> F ).

(* "Tying the knot" by defining entrees as the greatest fixed-point of entreeF *)
CoInductive entree : Type@{entree_u} :=
  go { _observe : entreeF entree }.

End entree.

(* Implicit arguments and helpful notations for entrees *)
Arguments entree _ {_} _.
Arguments entreeF _ {_} _ _ .
Arguments RetF {_ _ _ _} _.
Arguments TauF {_ _ _ _} _.
Arguments VisF {_ _ _ _} _ _.
Notation entree' E R := (entreeF E R (entree E R)).
Notation Tau t := {| _observe := TauF t |}.
Notation Ret r := {| _observe := RetF r |}.
Notation Vis e k := {| _observe := VisF e k |}.

(* "Observe" the top-most constructor of an entree by unwrapping it one step *)
Definition observe {E R} `{EncodingType E} (t : entree E R) : entree' E R :=
  _observe _ _ t.


Declare Scope entree_scope.
Bind Scope entree_scope with entree.
Delimit Scope entree_scope with entree.
Local Open Scope entree_scope.
Create HintDb itree.


(*** The basic operations on entrees ***)

Module EnTree.

(* This defines the bind operation by coinduction on the left-hand side of the
   bind; can also be seen as "substituting" an observed computation tree ot for
   the return value of a continuation k *)
Definition subst' {E : Type@{entree_u}} `{EncodingType E} {R S : Type@{entree_u}}
           (k : R -> entree E S) : entree' E R -> entree E S  :=
  cofix _subst (ot : entree' E R) :=
    match ot with
    | RetF r => k r
    | TauF t => Tau (_subst (observe t))
    | VisF e k => Vis e (fun x => _subst (observe (k x)))
    end.

(* Wrap up subst' so it operates on an entree instead of an entree' *)
Definition subst {E : Type@{entree_u}} `{EncodingType E} {R S : Type@{entree_u}}
           (k : R -> entree E S) : entree E R -> entree E S :=
  fun t => subst' k (observe t).

(* Monadic bind for entrees is just subst *)
Definition bind {E} `{EncodingType E} {R S : Type@{entree_u}} 
           (t : entree E R) (k : R -> entree E S) :=
  subst k t.

(* Iterate a body on successive inputs of type I until it returns an R *)
Definition iter {E} `{EncodingType E} {I R : Type@{entree_u}}
           (body : I -> entree E (I + R) ) : I -> entree E R :=
  cofix _iter i :=
    bind (body i) (fun ir => match ir with
                          | inl i' => Tau (_iter i')
                          | inr r => Ret r
                          end).

(* Map a pure function over the return value(s) of an entree *)
Definition map {E} `{EncodingType E} {R S} (f : R -> S) (t : entree E R) :=
  bind t (fun r => Ret (f r)).

(* Build a computation tree that performs a single event / effect in E *)
Definition trigger {E} `{EncodingType E} (e : E) : entree E (encodes e) :=
  Vis e (fun x => Ret x).

(* The nonterminating computation that spins forever and never does anything *)
CoFixpoint spin {E R} `{EncodingType E} : entree E R := Tau spin.

End EnTree.


(*** Notations for monadic computations ***)
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


(*** Instances to show that entrees form a monad ***)

#[global] Instance Functor_entree {E} `{EncodingType E} : Functor (entree E) :=
  { fmap := @EnTree.map E _ }.

#[global] Instance Applicative_entree {E} `{EncodingType E} : Applicative (entree E) :=
  {
    pure := fun _  x => Ret x;
    ap := fun _ _ f x =>
            EnTree.bind f (fun f => EnTree.bind x (fun x => Ret (f x)) );

  }.

#[global] Instance Monad_entree {E} `{EncodingType E} : Monad (entree E) :=
  {
    ret := fun _ x => Ret x;
    bind := @EnTree.bind E _;
  }.

#[global] Instance MonadIter_entree {E} `{EncodingType E} : MonadIter (entree E) :=
  fun _ _ => EnTree.iter.


(*** Useful properties of entrees ***)

(* Extensionality rule for entrees *)
Lemma entree_eta {E} `{EncodingType E} {R} (e : entree E R) :
  e = go _ _ (observe e).
Proof.
  destruct e. reflexivity.
Qed.

(* Destructing the fixed-point constructor is the identity *)
Lemma entree_beta {E} `{EncodingType E} {R} (e : entree' E R) :
  e = observe (go _ _ e).
Proof.
  reflexivity.
Qed.

(* Destruct an equality on VisF constructors into a dependent equality *)
Lemma injection_VisF_eq {E} `{EncodingType E} {R F} {e1 e2 : E}
  {k1 : encodes e1 -> F} {k2 : encodes e2 -> F} :
  VisF (R:=R) e1 k1 = VisF e2 k2 ->
  existT (fun e => encodes e -> F) e1 k1 = existT _ e2 k2.
Proof.
  intro e. inversion e. reflexivity.
Qed.

(* Bind of a Tau equals Tau of a bind *)
Lemma bind_Tau_eq {E} `{EncodingType E} {R S} (m : entree E R) (k : R -> entree E S) :
  EnTree.bind (Tau m) k = Tau (EnTree.bind m k).
Proof.
  rewrite (entree_eta ( EnTree.bind (Tau m) k)).
  rewrite (entree_eta (Tau (EnTree.bind m k))).
  reflexivity.
Qed.

(* Bind of a Vis equals Vis of a bind *)
Lemma bind_Vis_eq {E} `{EncodingType E} {R S} (e:E)
  (k1 : encodes e -> entree E R) (k2 : R -> entree E S) :
  EnTree.bind (Vis e k1) k2 = Vis e (fun x => EnTree.bind (k1 x) k2).
Proof.
  rewrite (entree_eta (EnTree.bind (Vis e k1) k2)).
  rewrite (entree_eta (Vis e (fun x => EnTree.bind (k1 x) k2))).
  reflexivity.
Qed.


(*** Helper tactics ***)

(* Replace a TauF in the goal with observe Tau *)
Ltac observe_tau :=
  (lazymatch goal with
   | |- context F [TauF ?e] => replace (TauF e) with (observe (Tau e)); [ | reflexivity ]
   end).

(* A version of induction that lets the user specify what to induct over *)
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
