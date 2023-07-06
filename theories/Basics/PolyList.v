(***
 *** Lists that are polymorphic in the unviverse level of their type
 ***)

From Coq Require Import
  Arith
.

Polymorphic Inductive plist@{u} (A : Type@{u}) :=
| pnil : plist A
| pcons : A -> plist A -> plist A.
Arguments pnil {A}.
Arguments pcons {A} _ _.

Polymorphic Fixpoint plength@{u} {A : Type@{u}} (xs : plist A) : nat :=
  match xs with
  | pnil => 0
  | pcons _ xs' => S (plength xs')
  end.

Polymorphic Fixpoint pmap@{u} {A B : Type@{u}} (f : A -> B) (xs : plist A) : plist B :=
  match xs with
  | pnil => pnil
  | pcons x xs' => pcons (f x) (pmap f xs')
  end.

Polymorphic Fixpoint papp@{u} {A : Type@{u}} (xs ys : plist A) : plist A :=
  match xs with
  | pnil => ys
  | pcons x xs' => pcons x (papp xs' ys)
  end.

Lemma papp_nil {A} (xs : plist A) : papp xs pnil = xs.
Proof.
  induction xs; [ reflexivity | ].
  simpl. rewrite IHxs. reflexivity.
Qed.

Lemma papp_assoc {A} (xs ys zs : plist A)
  : papp (papp xs ys) zs = papp xs (papp ys zs).
Proof.
  revert ys zs; induction xs; intros; [ reflexivity | ].
  simpl. rewrite IHxs. reflexivity.
Qed.

Lemma plength_papp {A} (xs ys : plist A)
  : plength (papp xs ys) = plength xs + plength ys.
Proof.
  induction xs; [ reflexivity | ].
  simpl. rewrite IHxs. reflexivity.
Qed.

Lemma plength_app_r {A} (xs ys : plist A) : plength xs <= plength (papp xs ys).
Proof.
  induction xs; [ apply le_0_n | ].
  apply le_n_S. assumption.
Qed.

Polymorphic Definition pcons_r@{u} {A : Type@{u}} (xs : plist A) (x:A) : plist A :=
  papp xs (pcons x pnil).

Lemma pcons_r_app {A} xs (x:A) ys : papp (pcons_r xs x) ys = papp xs (pcons x ys).
Proof.
  unfold pcons_r. rewrite papp_assoc. reflexivity.
Qed.

Polymorphic Fixpoint papp_r@{u} {A : Type@{u}} (xs ys : plist A) : plist A :=
  match ys with
  | pnil => xs
  | pcons y ys' => papp_r (pcons_r xs y) ys'
  end.

Lemma papp_r_papp {A} (xs ys : plist A) : papp_r xs ys = papp xs ys.
Proof.
  revert xs; induction ys; intros.
  - symmetry. apply papp_nil.
  - simpl. rewrite IHys. apply pcons_r_app.
Qed.

(* FIXME: doesn't work!
Polymorphic Fixpoint pconcat@{u} {A : Type@{u}} (xss : plist (plist A)) : plist A :=
  match xss with
  | pnil => pnil
  | pcons xs xss' => papp xs (pconcat xss')
  end.
*)

Polymorphic Definition pconcat@{u} {A : Type@{u}} (xss : plist (plist A)) : plist A :=
  plist_rect@{u u} (plist A) (fun _ => plist A) pnil
    (fun xs _ yss => papp xs yss) xss.


(* A version of nth_default that does primary recursion on the list *)
Fixpoint nth_default' {A} (d : A) (l : plist A) n : A :=
  match l with
  | pnil => d
  | pcons x l' => match n with
                  | 0 => x
                  | S n' => nth_default' d l' n'
                  end
  end.

(* If an index n is at least as long as a list, nth_default' returns the default *)
Lemma nth_default'_default {A} (d:A) l n : plength l <= n -> nth_default' d l n = d.
Proof.
  revert n; induction l; intros; [ reflexivity | ].
  simpl. destruct n.
  - inversion H.
  - apply IHl. apply le_S_n. assumption.
Qed.

(* If an index n is less then the length of the first list of an append, then
the nth element of the append is the nth element of the first list *)
Lemma nth_default'_app_left {A} (d:A) l1 l2 n :
  n < plength l1 -> nth_default' d (papp l1 l2) n = nth_default' d l1 n.
Proof.
  revert n; induction l1; intros.
  - inversion H.
  - destruct n; [ reflexivity | ]. simpl.
    apply IHl1. simpl in H. apply Lt.lt_S_n. assumption.
Qed.

Lemma nth_default'_app_right {A} (d:A) l1 l2 n :
  nth_default' d (papp l1 l2) (plength l1 + n) = nth_default' d l2 n.
Proof.
  revert n; induction l1; intros.
  - reflexivity.
  - apply IHl1.
Qed.

(* Proof that an object equals the nth element of a list *)
Fixpoint isNth@{u} {A : Type@{u}} (xs : plist A) n (y : A) : Prop :=
  match xs with
  | pnil => False
  | pcons x xs' => match n with
                   | 0 => x = y
                   | S n' => isNth xs' n' y
                   end
  end.


(* Build the right-nested tuple type of a list of types formed by mapping a
function across a list *)
Polymorphic Fixpoint mapTuple@{u v} {T:Type@{v}} (f : T -> Type@{u}) (xs : plist T) : Type@{u} :=
  match xs with
  | pnil => unit
  | pcons x xs' => f x * mapTuple f xs'
  end.

(* Append two mapTuple tuples *)
Polymorphic Fixpoint appMapTuple@{u v} {T:Type@{v}} (f : T -> Type@{u}) (xs ys : plist T) :
  mapTuple f xs -> mapTuple f ys -> mapTuple f (papp xs ys) :=
  match xs return mapTuple f xs -> mapTuple f ys -> mapTuple f (papp xs ys) with
  | pnil => fun _ tup2 => tup2
  | pcons x xs' =>
      fun tup1 tup2 => (fst tup1, appMapTuple f xs' ys (snd tup1) tup2)
  end.

(* Project the nth element of a mapTuple *)
Polymorphic Fixpoint nthProjDefault@{u v} {T:Type@{v}} (f : T -> Type@{u}) (dT:T) (d:f dT) xs
  : forall n, mapTuple f xs -> f (nth_default' dT xs n) :=
  match xs return forall n, mapTuple f xs -> f (nth_default' dT xs n) with
  | pnil => fun _ _ => d
  | pcons x xs' =>
      fun n =>
        match n return mapTuple f (pcons x xs') -> f (nth_default' dT (pcons x xs') n) with
        | 0 => fun tup => fst tup
        | S n' => fun tup => nthProjDefault f dT d xs' n' (snd tup)
        end
  end.

(* Project the dependent pair of the nth element of a mapTuple with its index *)
Definition nthProjDefaultSig@{u v} {T:Type@{v}} (f : T -> Type@{u})
  (d : { x : T & f x }) xs n (tup : mapTuple f xs) : { x : T & f x } :=
  existT f
    (nth_default' (projT1 d) xs n)
    (nthProjDefault f (projT1 d) (projT2 d) xs n tup).

(* Projecting at a position less than the length of the first mapTuple of an
append will give you a projection at the same position in the first tuple *)
Lemma nthProjDefaultSig_app_l@{u v} {T:Type@{v}} (f : T -> Type@{u}) d
  xs (tup1 : mapTuple f xs) ys (tup2 : mapTuple f ys) n :
  n < plength xs ->
  nthProjDefaultSig f d (papp xs ys) n (appMapTuple f xs ys tup1 tup2) =
    nthProjDefaultSig f d xs n tup1.
Proof.
  revert tup1 ys tup2 n; induction xs; intros.
  - inversion H.
  - destruct n.
    + reflexivity.
    + apply IHxs. apply le_S_n. assumption.
Qed.

(* Projecting at a position greater than or equal to the length of the first
mapTuple of an append will give you a projection in the second tuple *)
Lemma nthProjDefaultSig_app_r@{u v} {T:Type@{v}} (f : T -> Type@{u}) d
  xs (tup1 : mapTuple f xs) ys (tup2 : mapTuple f ys) n :
  plength xs <= n ->
  nthProjDefaultSig f d (papp xs ys) n (appMapTuple f xs ys tup1 tup2) =
    nthProjDefaultSig f d ys (n - plength xs) tup2.
Proof.
  revert tup1 ys tup2 n; induction xs; intros.
  - simpl. rewrite <- Minus.minus_n_O. reflexivity.
  - destruct n.
    + inversion H.
    + apply IHxs. apply le_S_n. assumption.
Qed.
