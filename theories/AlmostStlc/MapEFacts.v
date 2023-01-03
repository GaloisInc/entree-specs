From Coq Require Import
     Program
     Setoid
     Morphisms
     Relations
     Logic.FunctionalExtensionality
.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Monad
     Basics.Tacs
     Basics.HeterogeneousRelations
     Eq.Paco2.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Core.SubEvent
     Eq.Eqit
.

Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.

Require Import ITree.Basics.Basics.

Require Export TypedVar MrecMonad.

From Equations Require Import Equations Signature.

(* possibly should further generalize to having input and output rel *)
Definition handler_eq {D1 D2 : Type} `{EncodedType D1} `{EncodedType D2} (Rd : D1 -> D1 -> Prop) (h1 h2 : handler D1 D2) : Prop :=
  forall (d1 d1' : D1), Rd d1 d1' -> 
                   (projT1 (h1 d1)) = (projT1 (h2 d1')) /\
                     projT2 (h1 d1) ~= (@id (encodes d1)) /\
                     projT2 (h2 d1') ~= (@id (encodes d1')) /\ 
                     encodes d1 = encodes ((projT1 (h1 d1))) /\ 
                     encodes d1' = encodes (projT1 (h2 d1'))
.

Class valid_handler {D1 D2 : Type} `{EncodedType D1} `{EncodedType D2} (h : handler D1 D2) : Prop :=
   valid : forall d1, encodes d1 = encodes (projT1 (h d1)) /\ projT2 (h d1) ~= (@id (encodes d1)).

Lemma valid_handler_self_eq {D1 D2 : Type} `{EncodedType D1} `{EncodedType D2} (h : handler D1 D2) : 
  valid_handler h <-> handler_eq eq h h.
Proof.
  unfold valid_handler, handler_eq. split; intros; subst; eauto.
  - specialize (H1 d1'). destruct H1. repeat split; auto.
  - specialize (H1 d1 d1 eq_refl). tauto.
Qed.


Section mapE_match.
Context (D1 D2 : Type) `{EncodedType D1} `{EncodedType D2}.
Context (h : handler D1 D2).

Lemma mapE_ret R (r : R) : mapE h (ret r) ≅ ret r.
Proof.
  pstep. red. constructor. auto.
Qed.

Lemma mapE_tau R (t : entree D1 R) : mapE h (Tau t) ≅ Tau (mapE h t).
Proof.
  pstep. red. cbn. constructor. left. apply Reflexive_eqit. auto.
Qed.

Lemma mapE_vis R (d : D1) (k : encodes d -> entree D1 R) : 
  mapE h (Vis d k) ≅ 
       let '(d' && f) := h d in
       Vis d' (fun x => mapE h (k (f x))).
Proof.
  pstep. red.
  unfold mapE at 1. cbn. 
  destruct (h d) eqn : Hhd. cbn.
  unfold observe, _observe. cbn. rewrite Hhd. constructor. left.
  apply Reflexive_eqit. auto.
Qed.
End mapE_match.


Section mapE_proper.
Context (D1 D2 : Type) `{EncodedType D1} `{EncodedType D2}.
(* maybe can further generalize *)
Context (h1 h2 : handler D1 D2) (Hh : handler_eq eq h1 h2).

Lemma mapE_proper b1 b2 (R : Type) (t1 t2 : entree D1 R) : eqit eq b1 b2 t1 t2 -> eqit eq b1 b2 (mapE h1 t1) (mapE h2 t2).
Proof.
  ginit.
  revert t1 t2. gcofix CIH. intros t1 t2 Ht12.
  punfold Ht12. red in Ht12. unfold mapE.
  hinduction Ht12 before r; intros; subst; try inv CHECK.
  - gstep. red. cbn. constructor. auto.
  - gstep. red. cbn. constructor. gfinal. pclearbot. eauto.
  - setoid_rewrite mapE_vis. specialize (Hh e e eq_refl).
    destruct (h1 e). destruct (h2 e). cbn in Hh. decompose record Hh. subst.
    gstep. constructor. pclearbot. intros.
    remember (encodes e) as B. remember (encodes x0) as A. clear HeqB HeqA. subst.
    apply JMeq_eq in H2, H3. subst. gfinal. left. eapply CIH. apply REL.
  - setoid_rewrite mapE_tau. rewrite tau_euttge. eapply IHHt12. eauto.
  - setoid_rewrite mapE_tau. rewrite tau_euttge. eapply IHHt12. eauto.
Qed.

End mapE_proper.


#[global] Instance mapE_proper_inst {b1 b2} {D1 D2 : Type} `{EncodedType D1} `{EncodedType D2} {R}: 
  Proper (@handler_eq D1 D2 _ _ eq ==> eqit (@eq R) b1 b2 ==> eqit eq b1 b2) mapE.
Proof.
  repeat intro. apply mapE_proper; auto.
Qed.
Arguments valid_handler {_ _ _ _}.
Section test.
Context (D1 D2 : Type) `{enc1 : EncodedType D1} `{enc2 : EncodedType D2}.
Context (h : handler D1 D2) (H : valid_handler h).

End test.

#[global] Instance mapE_proper_inst_const_h {b1 b2} {D1 D2 : Type} `{enc1 : EncodedType D1} `{enc2 : EncodedType D2} {R} 
 (h : handler D1 D2) `{@valid_handler D1 D2 enc1 enc2 h} :
  Proper (eqit (@eq R) b1 b2 ==> eqit eq b1 b2) (mapE h).
Proof. 
  apply mapE_proper_inst.
  apply valid_handler_self_eq. auto.
Qed.
  
#[global] Instance mapE_proper_inst_const_h_eutt {D1 D2 : Type} `{enc1 : EncodedType D1} `{enc2 : EncodedType D2} {R} h
  `{@valid_handler D1 D2 enc1 enc2 h}: 
  Proper (eutt eq ==> eutt (@eq R)) (mapE h).
Proof. apply mapE_proper_inst_const_h. auto. Qed.

Section mapE_bind.
Context (D1 D2 : Type) `{EncodedType D1} `{EncodedType D2}.
(* maybe can further generalize *)
(* this validiity condition*)
Context (h : handler D1 D2) (Hvalid : valid_handler h).

Lemma mapE_bind R S (m : entree D1 R) (k : R -> entree D1 S) : 
  mapE h (bind m k) ≅ bind (mapE h m) (fun r => mapE h (k r)).
Proof.
  revert m. ginit. gcofix CIH. intros.
  destruct (observe m) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - setoid_rewrite <- Heq. setoid_rewrite mapE_ret. setoid_rewrite bind_ret_l.
    apply Reflexive_eqit_gen. auto.
  - setoid_rewrite <- Heq. setoid_rewrite mapE_tau. setoid_rewrite bind_tau.
    gstep. constructor. gfinal. left. eapply CIH.
  - setoid_rewrite <- Heq. setoid_rewrite mapE_vis. specialize (Hvalid e).
    destruct (h e). cbn in Hvalid. setoid_rewrite bind_vis. gstep. constructor.
    gfinal. left. eapply CIH.
Qed.

End mapE_bind.
