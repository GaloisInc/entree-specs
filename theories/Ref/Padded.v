From Coq Require Import
     Program
     Setoid
     Morphisms
     Relations.



From ITree Require Import
     Basics.Basics
     Basics.Tacs
     Basics.HeterogeneousRelations
 .

From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Eq.Eqit
.

From Paco Require Import paco.

Local Open Scope entree_scope.

Section padded.
Context {E : Type} `{EncodingType E} {R : Type}.

Variant paddedF (F : entree E R -> Prop) : entree' E R -> Prop :=
  | paddedF_Ret r : paddedF F (RetF r)
  | paddedF_Tau t : F t -> paddedF F (TauF t)
  | paddedF_Vis (e : E) (k : encodes e -> entree E R) : 
    (forall a, exists t, observe (k a) = TauF t /\ F t ) -> paddedF F (VisF e k)
.
Hint Constructors paddedF : entree_spec.

Definition padded_ sim := fun t => paddedF sim (observe t).

Lemma padded_monotone_ : monotone1 padded_.
Proof with eauto with entree_spec. 
  red. unfold padded_. intros. 
  induction IN... econstructor. intros. specialize (H0 a). 
  destruct H0 as [? [? ?] ]. eauto.
Qed.

Hint Resolve padded_monotone_ : entree_spec.

Definition padded := paco1 padded_ bot1.

Lemma padded_VisF_inv e k F : paddedF F (VisF e k) -> (forall a : encodes e, exists t, observe (k a) = TauF t /\ F t).
Proof with eauto with entree_spec.
  intros. dependent destruction H0...
Qed.


CoFixpoint pad' (ot : entree' E R) : entree E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (pad' (observe t))
  | VisF e k => Vis e (fun x => Tau (pad' (observe (k x)))) 
  end.

Definition pad t := pad' (observe t).

Lemma pad_ret r : pad (Ret r) ≅ Ret r.
Proof.
  pstep. constructor. auto.
Qed.

Lemma pad_tau t : pad (Tau t) ≅ Tau (pad t).
Proof.
  pstep. red. cbn. constructor. left. enough (pad t ≅ pad t). auto.
  reflexivity.
Qed.

Lemma pad_vis e k : pad (Vis e k) ≅ Vis e (fun x => Tau (pad (k x))).
Proof.
  pstep. red. cbn. constructor. left.  pstep. constructor.
  left. enough (pad (k a) ≅ pad (k a)). auto. reflexivity.
Qed.

End padded.

Theorem pad_is_padded {E : Type} `{EncodingType E} {R : Type} : forall t : entree E R, padded (pad t).
Proof with eauto with entree_spec.
  pcofix CIH. intros. pstep. unfold pad.
  destruct (observe t); eauto. constructor. constructor. right. eauto.
  econstructor. intros. eexists. split; [reflexivity | ]. right. eauto.
Qed.

#[global] Hint Resolve pad_is_padded : entree_spec.

Theorem pad_eutt {E : Type} `{EncodingType E} {R : Type} : forall t : entree E R, t ≈ pad t.
Proof with eauto with entree_spec.
(*easier to do with gpaco*)
Admitted.

(* Lemma padded_bind *)
(* Lemma padded_iter*)
