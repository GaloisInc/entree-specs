Require Export TypedVar.
Require Export SyntaxSeq.
Require Export SmallStepSeq.
Require Export DenotationFacts.
Require Export DenotationSeq.
Require Export TypesEquiv.
Require Export MapEFacts.
Import List.ListNotations.
Open Scope list_scope.
From Equations Require Import Equations Signature.
Require Import Coq.Program.Equality.
Require Import ExtLib.Structures.Monad.
Require Import Coq.Relations.Relation_Operators.
Import MonadNotation.
Local Open Scope monad_scope.
Require Export SemanticsFactsSeq.
Require Export CallMrecFacts.
Require Export SemanticsFactsSeq2.
Require Import Lia.
Require Import ITree.Basics.HeterogeneousRelations.

Require Import Coq.Classes.Morphisms.

Local Open Scope entree_scope.

From Paco Require Import paco.


Variant entree_step {E R} `{EncodedType E} (t1 t2 : entree E R) : Prop :=
  | step_intro : t1 ≅ Tau t2 -> entree_step t1 t2.


Inductive multi_step {E R} `{EncodedType E} : nat -> entree E R -> entree E R -> Prop :=
  | multi_step0 t1 t2 : t1 ≅ t2 -> multi_step 0 t1 t2
  | multi_stepS t1 t2 t3 n : multi_step n t2 t3 -> entree_step t1 t2 -> multi_step (S n) t1 t3.

Lemma entree_step_eutt {E R} `{EncodedType E} (t1 t2 : entree E R) : 
  entree_step t1 t2 -> t1 ≈ t2.
Proof.
  intros [Ht12]. rewrite Ht12, tau_eutt. reflexivity.
Qed.

#[global] Instance entree_step_proper {E R} `{EncodedType E} :
  Proper (eq_itree (E := E) (R1 := R) eq ==> eq_itree eq ==> Basics.flip Basics.impl) entree_step.
Proof.
  repeat intro. inversion H2. subst. constructor. rewrite H0, H3.
  pstep. constructor. left. symmetry in H1. auto.
Qed.

#[global] Instance multi_step_proper {E R} `{EncodedType E} :
  Proper (eq ==> eq_itree (E := E) (R1 := R) eq ==> eq_itree eq ==> Basics.flip Basics.impl) multi_step.
Proof.
  repeat intro. subst. generalize dependent x0. generalize dependent x1. induction H3; intros.
  - constructor. rewrite H1, H0, <- H2. reflexivity.
  - rewrite <- H1 in H0. destruct H0. rewrite H0 in H1.  econstructor. eapply IHmulti_step; eauto.
    reflexivity. constructor. auto.
Qed.

Lemma multi_step_eutt {E R} `{EncodedType E} n (t1 t2 : entree E R) :
  multi_step n t1 t2 -> t1 ≈ t2.
Proof.
  intros Hn. induction Hn. rewrite H0. reflexivity. 
  destruct H0. rewrite H0, tau_eutt. auto.
Qed.

Lemma eutt_ret_multi_step {E R} `{EncodedType E} (t : entree E R) (r : R) :
  t ≈ ret r -> exists n, multi_step n t (ret r).
Proof.
  cbn. intros Hret. punfold Hret. red in Hret.
  cbn in *. remember (observe t) as ot. generalize dependent t. remember (RetF r) as x.
  hinduction Hret before r; intros; try inversion Heqx.
  - subst. apply simpobs in Heqot.  exists 0. constructor.
    symmetry. auto.
  - specialize (IHHret H0 t1 eq_refl). destruct IHHret as [n Hn].
    exists (S n). apply simpobs in Heqot. rewrite <- Heqot. rewrite H0 in Hn. 
    econstructor; eauto. constructor. reflexivity.
Qed.

Lemma multi_step_add {E R} `{EncodedType E} (t1 t2 t3 : entree E R) n m : 
  multi_step n t1 t2 -> multi_step m t2 t3 -> multi_step (n + m) t1 t3.
Proof.
  intros Hn. revert m. generalize dependent t3. induction Hn.
  - simpl. setoid_rewrite H0. auto.
  - cbn. intros t4 m Ht4. apply IHHn in Ht4. econstructor; eauto.
Qed.

Ltac remember_eq_itree t1 n :=
  let H1 := fresh in
  let H2 := fresh "Heq" in
  remember t1 as n eqn : H1; assert (H2 : t1 ≅ n); try (subst; reflexivity); clear H1.

Lemma multi_step_ret_bind_inv E R1 R2 `{EncodedType E} (t : entree E R1) (k : R1 -> entree E R2) s n : 
      multi_step n (x <- t;; k x) (ret s) -> 
      exists m1 m2 r, m1 + m2 = n /\ multi_step m1 t (ret r) /\ multi_step m2 (k r) (ret s).
Proof.
  remember_eq_itree (x <- t;; k x) t0.
  intros Hn. dependent induction Hn.
  - rewrite H0 in Heq. exists 0, 0. destruct (eq_itree_case t) as [[r Hr] | [[t' Ht'] | [e [k' Hek]] ]].
    + setoid_rewrite Hr. exists r. split; auto. split.
      constructor. reflexivity.
      constructor. rewrite Hr in Heq. setoid_rewrite bind_ret_l in Heq. auto.
    + rewrite Ht' in Heq. setoid_rewrite bind_tau in Heq. pinversion Heq; inversion CHECK.
    + rewrite Hek in Heq. setoid_rewrite bind_vis in Heq. pinversion Heq.
  - destruct H0. rewrite H0 in Heq.
    destruct (eq_itree_case t) as [[r Hr] | [[t' Ht'] | [e [k' Hek]] ]].
    + exists 0, (S n), r. split; auto. split. constructor. auto.
      rewrite Hr in Heq. setoid_rewrite bind_ret_l in Heq. econstructor; eauto.
      constructor. auto.
    + rewrite Ht' in Heq. setoid_rewrite bind_tau in Heq.  apply eqit_inv_Tau in Heq.
      eapply IHHn in Heq; eauto. destruct Heq as [m1 [m2 [r [Hm [Hstep Hk]]]]].
      exists (S m1), m2, r. split. lia. split; auto. econstructor; eauto. constructor; auto.
    + rewrite Hek in Heq. clear - Heq. setoid_rewrite bind_vis in Heq. pinversion Heq.
      inversion CHECK.
Qed.

Lemma multi_step_vis_bind_inv E R1 R2 `{EncodedType E} (t : entree E R1) (k1 : R1 -> entree E R2)
      (e : E) (k2 : encodes e -> entree E R2) n :
  multi_step n (x <- t;; k1 x) (Vis e k2) ->
  (exists m1 m2 r, m1 + m2 = n /\ multi_step m1 t (ret r) /\ multi_step m2 (k1 r) (Vis e k2)) \/
  (exists k1', multi_step n t (Vis e k1') /\ forall x, y <- k1' x;; k1 y ≅ k2 x).
Proof.
  remember_eq_itree (x <- t;; k1 x) t0.
  intros Hn. dependent induction Hn.
  - rewrite H0 in Heq.
    destruct (eq_itree_case t) as [[r Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
    + rewrite Hr in Heq. setoid_rewrite bind_ret_l in Heq. left. exists 0, 0, r.
      split. auto. split; constructor; auto.
    + exfalso. rewrite Ht' in Heq. setoid_rewrite bind_tau in Heq. pinversion Heq; inversion CHECK.
    + rewrite Hek in Heq. setoid_rewrite bind_vis in Heq.
      assert (e = e'). pinversion Heq. subst. auto. subst.
      specialize (eqit_Vis_inv _ _ _ _ _ _ Heq) as Heqk. right.
      exists k'. split; auto. constructor. auto.
  - destruct H0. rewrite H0 in Heq.
    destruct (eq_itree_case t) as [[r Hr] | [[t' Ht'] | [e' [k' Hek]] ]].
    + rewrite Hr in Heq. setoid_rewrite bind_ret_l in Heq.
      left. exists 0, (S n), r. split. auto. split. constructor. auto.
      econstructor; eauto. constructor. auto.
    + rewrite Ht' in Heq. setoid_rewrite bind_tau in Heq.
      apply eqit_inv_Tau in Heq. eapply IHHn in Heq; eauto.
      destruct Heq as [ [m1 [m2 [r [Hm [Hstep1 Hstep2]]]] ] | [k1' [Hstep Heq] ]].
      * left. exists (S m1), m2, r. split. lia. split; auto.
        econstructor; eauto. constructor. auto.
      * right. exists k1'. split; auto.
        econstructor; eauto. constructor. auto.
    + rewrite Hek in Heq. setoid_rewrite bind_vis in Heq.
      pinversion Heq. inversion CHECK.
Qed.
