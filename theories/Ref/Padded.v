From Coq Require Import
     Program
     Setoid
     Morphisms
     Relations.



From ITree Require Import
     Basics.Basics
     Basics.Utils
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
  | paddedF_Vis e (k : encodes e -> entree E R) :
    (forall a, F (k a)) -> paddedF F (VisF e (fun a => (Tau (k a))))
.
Hint Constructors paddedF : entree_spec.

Definition padded_ sim := fun t => paddedF sim (observe t).

Lemma padded_monotone_ : monotone1 padded_.
Proof with eauto with entree_spec. 
  red. unfold padded_. intros. 
  induction IN...
Qed.

Hint Resolve padded_monotone_ : entree_spec.

Definition padded := paco1 padded_ bot1.

Lemma padded_VisF_inv e k F : paddedF F (VisF e k) -> exists k', forall a, k a ≅ Tau (k' a).
Proof with eauto with entree_spec.
  intros. dependent destruction H0... eexists. reflexivity.
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
  econstructor. intros. eauto.
Qed.
#[global] Hint Resolve padded_monotone_ : paco.
#[global] Hint Resolve padded_monotone_ : entree_spec.
#[global] Hint Resolve pad_is_padded : entree_spec.

Theorem pad_eutt {E : Type} `{EncodingType E} {R : Type} : forall t : entree E R, t ≈ pad t.
Proof with eauto with entree_spec.
  ginit. gcofix CIH. intros.
  unfold pad.
  destruct (observe t) eqn : Ht; symmetry in Ht; apply simpobs in Ht.
  - rewrite <- Ht. gstep. constructor. auto.
  - rewrite <- Ht. gstep. red. cbn. constructor.
    gfinal. eauto.
  - rewrite <- Ht. gstep. red. cbn.
    constructor. intros. red.
    rewrite tau_euttge.
    gfinal. eauto.
Qed.

Global Instance pad_Proper {b1 b2 E R} `{EncodingType E} : Proper (eqit eq b1 b2 ==> eqit eq b1 b2) (@pad E _ R).
Proof.
  pcofix CIH.
  intros t1 t2 Ht12. pstep. red. unfold pad.
  punfold Ht12. red in Ht12. hinduction Ht12 before r;
    intros; cbn; eauto.
  - constructor. auto.
  - constructor. pclearbot. right. eapply CIH; eauto.
  - constructor. left. pstep. constructor. pclearbot. right.
    eapply CIH; eauto. apply REL.
  - constructor; auto.
  - constructor; auto.
Qed.

Theorem pad_bind {E : Type} `{EncodingType E} {R S: Type} : forall (t : entree E R) (k : R -> entree E S),
    pad (EnTree.bind t k) ≅ EnTree.bind (pad t) (fun x => pad (k x)).
Proof.
  ginit. gcofix CIH. intros t k.
  destruct (observe t) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite <- Heq. rewrite pad_ret. repeat rewrite bind_ret_l.
    apply Reflexive_eqit_gen. auto.
  - repeat rewrite <- Heq. rewrite pad_tau. repeat rewrite bind_tau. gstep. constructor.
    gfinal. eauto.
  - repeat rewrite <- Heq. rewrite pad_vis. repeat rewrite bind_vis. rewrite pad_vis.
    gstep. constructor. intros. unfold id. gstep. constructor. gfinal. left. eapply CIH.
Qed.

Theorem pad_iter E `{EncodingType E} R S (body : R -> entree E (R + S)):
  forall r, pad (EnTree.iter body r) ≅ EnTree.iter (fun r => pad (body r)) r.
Proof.
  ginit. gcofix CIH.
  intros. setoid_rewrite unfold_iter. rewrite pad_bind.
  guclo eqit_clo_bind. econstructor.
  reflexivity. intros. subst. destruct u2.
  - rewrite pad_tau. gstep. constructor. gfinal. left. eauto.
  - rewrite pad_ret. gstep. constructor. auto.
Qed.

