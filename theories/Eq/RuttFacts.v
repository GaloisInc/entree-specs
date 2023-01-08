From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Tacs
     Basics.HeterogeneousRelations
     Eq.Paco2.

From ExtLib Require Import
     Structures.Monad.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Core.SubEvent
     Eq.Eqit
     Eq.Rutt
.

Local Open Scope entree_scope.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Lemma rutt_trigger {E1 E2} `{EncodedType E1} `{EncodedType E2}
      (RPre : Rel E1 E2) (RPost : PostRel E1 E2) 
      (e1: E1) (e2: E2) (RR : Rel (encodes e1) (encodes e2) ):
  RPre e1 e2 ->
  (forall a b, RPost e1 e2 a b -> RR a b) ->
  rutt RPre RPost RR (EnTree.trigger e1) (EnTree.trigger e2).
Proof.
  intros. apply rutt_Vis; auto.
  intros. apply rutt_Ret; auto.
Qed.

Lemma rutt_flip {E1 E2 R1 R2} `{enc1 : EncodedType E1} `{enc2 : EncodedType E2} 
      RPre RPost RR (t1: entree E1 R1) (t2: entree E2 R2):
  rutt RPre RPost RR t1 t2 <-> rutt (flip RPre) (FlipPostRel RPost) (flip RR) t2 t1.
Proof.
  split; revert t1 t2; pcofix CIH; intros t1 t2 Hrutt;
  punfold Hrutt; red in Hrutt; pstep; red.
  - induction Hrutt; try now constructor.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis. auto. intros b a HAns. cbn in HAns. right.
      specialize (H0 a b HAns). apply CIH. now pclearbot.
  - induction Hrutt; try now constructor.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis. auto. intros b a HAns. cbn in HAns. right.
      specialize (H0 a b HAns). apply CIH. now pclearbot.
Qed.


(* Progressive [Proper] instances for [rutt] and congruence with eutt. *)

#[global] Instance rutt_Proper_R {E1 E2 R1 R2} `{enc1 : EncodedType E1} 
 `{enc2 : EncodedType E2} :
  Proper (eq_rel         (* REv *)
      ==> PostRelEq       (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq             (* t1 *)
      ==> eq             (* t2 *)
      ==> iff) (@rutt E1 E2 enc1 enc2 R1 R2).
Proof.
  intros REv1 REv2 HREv  RAns1 RAns2 HRAns RR1 RR2 HRR t1 _ <- t2 _ <-.
  split; intros Hrutt.

  - revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt.
    pstep. punfold Hrutt. red in Hrutt; red.
    hinduction Hrutt before CIH; intros; eauto with entree.
    * apply EqRet. now apply HRR.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis. now apply HREv. intros.
      assert (H2: RAns1 e1 e2 a b).
      { apply  HRAns. auto. }
      intros. specialize (H0 a b H2). red. right. apply CIH.
      red in H0. now pclearbot.
    * constructor. auto.
    * constructor. auto.
  - revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt.
    pstep. punfold Hrutt. red in Hrutt; red.
    hinduction Hrutt before CIH; intros; eauto.
    * apply EqRet. now apply HRR.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis. now apply HREv. intros.
      assert (H2: RAns2 e1 e2 a b).
      { apply HRAns. auto. }
      intros. specialize (H0 a b H2). red. right. apply CIH.
      red in H0. now pclearbot.
   * constructor. auto.
   * constructor. auto.
Qed.
(*
#[global] Instance rutt_Proper_R' {E1 E2 R1 R2} `{enc1 : EncodedType E1} 
 `{enc2 : EncodedType E2} :
  Proper (eq_rel         (* REv *)
      ==> PostRelEq       (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq             (* t1 *)
      ==> eq             (* t2 *)
      ==> flip impl) (@rutt E1 E2 enc1 enc2 R1 R2).
Proof.
*)
#[global] Instance rutt_Proper_R2 {E1 E2 R1 R2}  `{enc1 : EncodedType E1} 
 `{enc2 : EncodedType E2}:
  Proper (eq_rel         (* REv *)
      ==> PostRelEq        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq_itree eq    (* t1 *)
      ==> eq_itree eq    (* t2 *)
      ==> iff) (@rutt E1 E2 enc1 enc2 R1 R2).
Proof.
  clear. intros REv1 REv2 HREv RAns1 RAns2 HRAns RR1 RR2 HRR t1 t1' Ht1 t2 t2' Ht2.
  split; intros Hrutt.
  - rewrite  <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
    ginit. gclo. econstructor; eauto with paco.
    * symmetry in Ht1. apply eq_sub_euttge in Ht1. apply Ht1.
    * symmetry in Ht2. apply eq_sub_euttge in Ht2. apply Ht2.
    * intros; now subst.
    * intros; now subst.
  - rewrite HREv, HRAns, HRR; clear HREv REv1 HRAns RAns1 HRR RR1.
    ginit. gclo. econstructor; eauto with paco.
    * apply eq_sub_euttge in Ht1. apply Ht1.
    * apply eq_sub_euttge in Ht2. apply Ht2.
    * intros; now subst.
    * intros; now subst.
Qed.

(* this should be one of the main goals of today*)
Lemma rutt_cong_eutt {E1 E2 R1 R2} `{enc1 : EncodedType E1} `{enc2 : EncodedType E2} :
  forall RPre RPost RR (t1: entree E1 R1) t1' (t2: entree E2 R2),
  rutt RPre RPost RR t1 t2 ->
  t1 ≈ t1' ->
  rutt RPre RPost RR t1' t2.
Proof.
  (* First by coinduction; then do an induction on Hrutt to expose the ruttF
     linking t1 and t2; then an induction on Heutt to expose the relation
     between t1 and t1'. Finally, explore ruttF until landing on an rutt where
     the t1/t1' relation can be substituted by CIH, and conclude. *)
  intros * Hrutt Heutt; revert t1 t1' Heutt t2 Hrutt.
  ginit; gcofix CIH; intros t1 t1' Heutt t2 Hrutt.
  punfold Hrutt; red in Hrutt.
  rewrite (entree_eta t1) in Heutt.
  rewrite (entree_eta t2).

  move Hrutt before CIH; revert_until Hrutt.
  induction Hrutt as [r1 r2|m1 m2| |m1 ot2|]; clear t1 t2; intros t1' Heutt.

  (* EqRet: t1 = Ret r1 ≈ t1'; we can rewrite away the Taus with the euttge
     closure and finish immediately with EqRet. *)
  * apply eutt_inv_Ret_l in Heutt. rewrite Heutt.
    gfinal; right; pstep. now apply EqRet.

  (* EqTau: The hardest case. When Heutt is EqTauL then we lack information to
     proceed, which requires that [desobs m1]. We then have to restart
     analyzing based on m1; the Ret case repeats EqRet above, while the Vis
     case repeats EqVis below. *)
  * punfold Heutt; red in Heutt; cbn in Heutt.
    rewrite entree_eta. pclearbot. fold_ruttF H.
    remember (TauF m1) as ot1; revert m1 m2 H Heqot1.
    induction Heutt as [|m1_bis m1'| |m1_bis ot1' _|t1_bis m1'];
    intros * Hrutt Heqot1; clear t1'; try discriminate.
    + inv Heqot1. pclearbot. gfinal; right; pstep; red.
      apply EqTau. right. now apply (CIH m1).
    + inv Heqot1. rewrite (entree_eta m1) in Hrutt.
      desobs m1 Hm1; clear m1 Hm1.
      { fold_eqitF Heutt. apply eutt_inv_Ret_l in Heutt.
        rewrite Heutt, tau_euttge. gfinal; right. eapply paco2_mon_bot; eauto. }
      { apply rutt_inv_Tau_l in Hrutt. eapply IHHeutt; eauto. }
      { clear IHHeutt. remember (VisF e k) as m1; revert Heqm1.
        induction Heutt as [| | e1 k1 k1' Hk1k1'| |]; intros; try discriminate.
        - symmetry in Heqm1; dependent destruction Heqm1.
          rewrite tau_euttge, (entree_eta m2).
          punfold Hrutt; red in Hrutt; cbn in Hrutt.
          remember (VisF e1 k1) as m1; revert Heqm1.
          induction Hrutt; intros; try discriminate.
          * dependent destruction Heqm1.
            gfinal; right. pstep; red; cbn.
            apply EqVis; auto. intros v1 v2 HAns. specialize (H0 v1 v2 HAns).
            hnf in H0; hnf. pclearbot; right. apply (CIH (k1 v1)); auto.
            apply Hk1k1'.
          * idtac. rewrite tau_euttge, (entree_eta t2). now apply IHHrutt.
        - idtac. rewrite tau_euttge, entree_eta; now apply IHHeutt. }
    + inv Heqot1. gfinal; right. pstep; red. apply EqTau. right.
      fold_eqitF Heutt. rewrite tau_euttge in Heutt. now apply (CIH m1).

  (* EqVis: Similar to EqRet, but we don't have t1' ≳ Vis e1 k1 because the
     continuations are "only" ≈. The up-to-eutt principle that enforces Vis
     steps could work, but we don't have it for rutt. Instead we peel the Tau
     layers off t1' with a manual induction. *)
  * rewrite entree_eta. gfinal; right; pstep.
    rename H0 into HAns. punfold Heutt; red in Heutt; cbn in Heutt.
    remember (VisF e1 k1) as m1; revert Heqm1.
    induction Heutt; intros; try discriminate.
    + dependent destruction Heqm1.
      apply EqVis; auto. intros a b HAns'. specialize (HAns a b HAns').
      hnf in HAns; hnf. pclearbot; right. apply (CIH (k1 a)); auto. apply REL.
    + now apply EqTauL, IHHeutt.

  (* EqTauL: We get a very strong IHHrutt at the ruttF level, which we can
     apply immediately; then handle the added Tau in ≈, which is trivial. *)
  * apply IHHrutt. rewrite <- entree_eta. now rewrite <- tau_eutt.

  (* EqTauR: Adding a Tau on the side of t2 changes absolutely nothing to the
     way we rewrite t1, so we can follow down and recurse. *)
  * rewrite tau_euttge. rewrite (entree_eta t0). now apply IHHrutt.
Qed.

#[global] Instance rutt_Proper_R3 {E1 E2 R1 R2}
  `{enc1 : EncodedType E1} `{enc2 : EncodedType E2}:
  Proper (eq_rel         (* REv *)
      ==> PostRelEq        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eutt eq        (* t1 *)
      ==> eutt eq        (* t2 *)
      ==> iff) (@rutt E1 E2 _ _ R1 R2).
Proof.
  intros REv REv2 HREv RAns RAns2 HRAns RR RR2 HRR t1 t1' Ht1 t2 t2' Ht2.
  rewrite <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
  split; intros Hrutt.
  - eapply rutt_cong_eutt; eauto.
    rewrite rutt_flip in *. eapply rutt_cong_eutt; eauto.
  - symmetry in Ht1, Ht2.
    eapply rutt_cong_eutt; eauto.
    rewrite rutt_flip in *. eapply rutt_cong_eutt; eauto.
Qed.

(* Bind closure and bind lemmas. *)
Ltac auto_ctrans :=
  intros; repeat (match goal with [H: rcompose _ _ _ _ |- _] => destruct H end); subst; eauto.
Ltac auto_ctrans_eq := try instantiate (1:=eq); auto_ctrans.
Section RuttBind.
Context {E1 E2 : Type} `{enc1 : EncodedType E1} `{enc2 : EncodedType E2}.
Context {R1 R2 : Type}.
Context (RPre : Rel E1 E2).
Context (RPost : PostRel E1 E2).
Context (RR : Rel R1 R2).

Inductive rutt_bind_clo (r : entree E1 R1 -> entree E2 R2 -> Prop) :
  entree E1 R1 -> entree E2 R2 -> Prop :=
| rbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
      (EQV: rutt RPre RPost RU t1 t2)
      (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
  : rutt_bind_clo r (EnTree.bind t1 k1) (EnTree.bind t2 k2)
.
Hint Constructors rutt_bind_clo: core.

Lemma rutt_clo_bind :
  rutt_bind_clo <3= gupaco2 (rutt_ RPre RPost RR) (euttge_trans_clo RR).
Proof.
  intros rr. gcofix CIH. intros. destruct PR.
  gclo. econstructor; auto_ctrans_eq.
  1,2: rewrite unfold_bind; reflexivity.
  punfold EQV. unfold rutt_ in *.
  hinduction EQV before CIH; intros; pclearbot; cbn;
    repeat (change (EnTree.subst ?k ?m) with (EnTree.bind m k)).
  - gclo. econstructor; auto_ctrans_eq.
    1,2: reflexivity.
    eauto with paco.
  - gstep. econstructor. eauto 7 with paco.
  - gstep. econstructor; eauto 7 with paco.
    intros. specialize (H0 a b H1). pclearbot. eauto 7 with paco.
  - gclo. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
    rewrite tau_euttge.
    rewrite unfold_bind. reflexivity.
  - gclo. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
    rewrite tau_euttge. rewrite unfold_bind. reflexivity.
Qed.

End RuttBind.

Lemma rutt_bind {E1 E2 R1 R2 T1 T2} `{EncodedType E1} `{EncodedType E2}
      (RPre : Rel E1 E2)
      (RPost : PostRel E1 E2)
      (RR: R1 -> R2 -> Prop) (RT: T1 -> T2 -> Prop) t1 t2 k1 k2:
    rutt RPre RPost RR t1 t2 ->
    (forall r1 r2,
      RR r1 r2 ->
      rutt RPre RPost RT (k1 r1) (k2 r2)) ->
    rutt RPre RPost RT (EnTree.bind t1 k1) (EnTree.bind t2 k2).
Proof.
  intros. ginit.
  (* For some reason [guclo] fails, apparently trying to infer the type in a
     context with less information? *)
  eapply gpaco2_uclo; [|eapply rutt_clo_bind|]; eauto with paco.
  econstructor; eauto. intros; subst. gfinal. right. apply H2. eauto.
Qed.
