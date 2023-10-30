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
     Basics.Tactics
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Core.SubEvent
     Eq.Eqit
     Eq.Rutt
     Interp.Recursion
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

Lemma rutt_ret_eutt {E1 E2 R1 R2} `{enc1 : EncodedType E1} `{enc2 : EncodedType E2} 
      RPre RPost RR (t1: entree E1 R1) (r : R2) : 
  rutt RPre RPost RR t1 (Ret r) <-> eutt RR t1 (Ret r).
Proof.
  split.
  - intros Hrutt. punfold Hrutt. red in Hrutt.
    pstep. red. cbn in *. genobs_clear t1 ot1.
    remember (RetF r) as or. hinduction Hrutt before r; intros; try inv Heqor.
    constructor. auto.
    constructor; auto.
  - intros Heutt. punfold Heutt. red in Heutt.
    pstep. red. cbn in *. genobs_clear t1 ot1.
    remember (RetF r) as or. hinduction Heutt before r; intros; try inv Heqor.
    constructor. auto.
    constructor; auto.
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
might be useful to augment PostRelEq with coordinating pre relations
would also be good to sit down and develop a convincing story of 
what coordinating relations are

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

Lemma rutt_sym {E R} `{enc : EncodedType E} (RPre : Rel E E) (RPost : PostRel E E)
      (RR : Rel R R) :
  Symmetric RPre ->
  SymmetricPostRel RPost ->
  Symmetric RR ->
  forall t1 t2,
    rutt RPre RPost RR t1 t2 ->
    rutt RPre RPost RR t2 t1.
Proof.
  intros Hsym1 Hsym2 Hsym3 t1 t2 Ht12.
  apply rutt_flip. rewrite <- symmetric_postrel; auto.
  assert (H1 : eq_rel (flip RPre) RPre ). unfold flip.
  split; repeat intro; eauto.
  assert (H2 : eq_rel (flip RR) RR ). unfold flip.
  split; repeat intro; eauto.
  rewrite H1, H2. auto.
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

Section InterpMrecConstructors.
Context (D E : Type) `{encd : EncodedType D} `{ence : EncodedType E}.
Context (body : forall d : D, entree (D + E) (encodes d)).

Lemma interp_mrec_ret (R : Type) (r : R) : interp_mrec body (Ret r) ≅ Ret r.
Proof. pstep. constructor. auto. Qed.

Lemma interp_mrec_tau (R : Type) (t : entree (D + E) R) : interp_mrec body (Tau t) ≅ Tau (interp_mrec body t).
Proof. pstep. red. cbn. constructor. left. apply Reflexive_eqit. auto. Qed.

Lemma interp_mrec_vis_inl R (d : D) (k : encodes d -> entree (D + E) R) :
  interp_mrec body (Vis (inl d) k) ≅ Tau (interp_mrec body (bind (body d) k)).
Proof.
  pstep. red. cbn.
  constructor. left. apply Reflexive_eqit. auto.
Qed.

Lemma interp_mrec_vis_inr R (e : E) (k : encodes e -> entree (D + E) R) :
  interp_mrec body (Vis (inr e) k) ≅ Vis e (fun x => interp_mrec body (k x)).
Proof.
  pstep. red. cbn. constructor. left. apply Reflexive_eqit. auto.
Qed.

End InterpMrecConstructors.

Section InterpMrecProper.
Context (D E : Type) `{encd : EncodedType D} `{ence : EncodedType E}.
Context (bodies1 bodies2 : forall d : D, entree (D + E) (encodes d)).
Context (b1 b2 : bool).
Context (Hbodies : forall d, eqit eq b1 b2 (bodies1 d) (bodies2 d)).

Theorem interp_mrec_proper (R : Type) : forall (t1 t2 : entree (D + E) R),
    eqit eq b1 b2 t1 t2 -> eqit eq b1 b2 (interp_mrec bodies1 t1) (interp_mrec bodies2 t2).
Proof.
  ginit. gcofix CIH. intros.
  punfold H0. red in H0. unfold interp_mrec.
  genobs t1 ot1. genobs t2 ot2.
  hinduction H0 before r; intros.
  - setoid_rewrite interp_mrec_ret. gstep. constructor. auto.
  - setoid_rewrite interp_mrec_tau. gstep. constructor. gfinal. pclearbot. eauto.
  - destruct e.
    + gstep. red. cbn. constructor. 
      gfinal. left. eapply CIH. pclearbot. eapply eqit_bind; eauto. intros. subst. apply REL.
    + gstep. red. cbn. constructor. gfinal. pclearbot. left. eapply CIH. apply REL.
  - setoid_rewrite interp_mrec_tau. inversion CHECK.
    rewrite tau_euttge. subst. eauto.
  - setoid_rewrite interp_mrec_tau. inversion CHECK.
    subst. rewrite tau_euttge. eauto.
Qed.


End InterpMrecProper.

Definition ptwise {A : Type} {B : A -> Type} : (forall (a : A), relation (B a)) -> relation (forall (a : A), B a) :=
  fun R (f g : forall a, B a) => forall a, (R a (f a) (g a) ).

#[global] Instance interp_mrec_proper_inst R D E `{EncodedType D} `{EncodedType E} (b1 b2 : bool)  :
  Proper (ptwise (fun i => eqit (@eq (encodes i)) b1 b2 ) ==> eqit eq b1 b2 ==> eqit (@eq R) b1 b2 ) interp_mrec.
Proof.
  repeat intro. eapply interp_mrec_proper; eauto.
Qed.

#[global] Instance interp_mrec_proper_inst' R D E `{EncodedType D} `{EncodedType E} 
 (bodies : forall d : D, entree (D + E) (encodes d)) :
  Proper (eutt (@eq R) ==> eutt eq ) (interp_mrec bodies).
Proof.
  repeat intro.
  eapply interp_mrec_proper; eauto. intros. reflexivity.
Qed.

#[global] Instance interp_mrec_proper_inst'' R D E `{EncodedType D} `{EncodedType E} 
 (bodies : forall d : D, entree (D + E) (encodes d)) :
  Proper (eq_itree (@eq R) ==> eq_itree eq ) (interp_mrec bodies).
Proof.
  repeat intro. eapply interp_mrec_proper; eauto. intros. reflexivity.
Qed.

Section InterpMrecBind.
  Context (D E : Type) `{encd : EncodedType D} `{ence : EncodedType E}.
  Context (bodies : forall d : D, entree (D + E) (encodes d)).

  Theorem interp_mrec_bind (R S: Type) : forall (t : entree (D + E) R) (k : R -> entree (D + E) S),
      interp_mrec bodies (bind t k) ≅ bind (interp_mrec bodies t) (fun x => interp_mrec bodies (k x)).
  Proof.
    ginit. gcofix CIH. intros.
    destruct (observe t) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
    - setoid_rewrite <- Heq. setoid_rewrite bind_ret_l.
      gfinal. right. eapply paco2_mon with (r := bot2); intros; try contradiction.
      apply Reflexive_eqit. auto.
    - setoid_rewrite <- Heq. rewrite interp_mrec_tau. setoid_rewrite bind_tau.
      rewrite interp_mrec_tau. gstep. constructor. gfinal. left.
      eapply CIH.
    - setoid_rewrite <- Heq. destruct e as [d | e].
      + setoid_rewrite bind_vis. setoid_rewrite interp_mrec_vis_inl.
        setoid_rewrite bind_tau. gstep. constructor. setoid_rewrite <- bind_bind. 
        gfinal. left. eapply CIH.
      + rewrite interp_mrec_vis_inr. setoid_rewrite bind_vis. 
        rewrite interp_mrec_vis_inr. gstep. constructor. intros. red.
        gfinal. left. eapply CIH.
   Qed.
End InterpMrecBind.

Section RuttMrec.
Context (D1 D2 E1 E2 : Type).
Context `{encd1 : EncodedType D1} `{encd2 : EncodedType D2} `{ence1 : EncodedType E1} `{ence2 : EncodedType E2}.
Context (RPreInv : Rel D1 D2) (RPre : Rel E1 E2).
Context (RPostInv : PostRel D1 D2) (RPost : PostRel E1 E2).

Context (bodies1 : forall d1 : D1, entree (D1 + E1) (encodes d1)).
Context (bodies2 : forall d2 : D2, entree (D2 + E2) (encodes d2)).

Context (Hbodies : forall d1 d2, RPreInv d1 d2 -> 
                            rutt (sum_rel RPreInv RPre) (SumPostRel RPostInv RPost) (RPostInv d1 d2) (bodies1 d1) (bodies2 d2)).

Theorem interp_mrec_rutt R1 R2 RR : forall (t1 : entree (D1 + E1) R1) (t2 : entree (D2 + E2) R2),
    rutt (sum_rel RPreInv RPre) (SumPostRel RPostInv RPost) RR t1 t2 ->
    rutt RPre RPost RR (interp_mrec bodies1 t1) (interp_mrec bodies2 t2).
Proof.
  ginit. gcofix CIH. intros t1 t2 Ht12.
  punfold Ht12. red in Ht12. unfold interp_mrec. genobs t1 ot1. genobs t2 ot2.
  hinduction Ht12 before r; intros.
  - gstep. constructor. auto.
  - apply simpobs in Heqot1, Heqot2. setoid_rewrite interp_mrec_tau.
    gstep. constructor. pclearbot. gfinal. eauto.
  - inversion H; subst.
    + gstep. red. cbn. constructor. gfinal. left. eapply CIH. 
      eapply rutt_bind; eauto. intros.
      assert (SumPostRel RPostInv RPost (inl a1) (inl a2) r1 r2). constructor. auto.
      eapply H0 in H3. pclearbot. auto.
    + gstep. red. cbn. constructor. auto. intros.
      assert (SumPostRel RPostInv RPost (inr b1) (inr b2) a b). constructor. auto.
      eapply H0 in H3. pclearbot. gfinal. eauto.
  - setoid_rewrite interp_mrec_tau. rewrite tau_euttge. eauto.
  - setoid_rewrite interp_mrec_tau. rewrite tau_euttge. eauto.
Qed.

End RuttMrec.

Section RuttIter.
  Context (E1 E2 R1 R2 S1 S2 : Type).
  Context `{ence1 : EncodedType E1} `{ence2 : EncodedType E2}.
  Context (RPre : Rel E1 E2) (RPost : PostRel E1 E2) (RR : Rel R1 R2) (RS : Rel S1 S2).
  Context (body1 : R1 -> entree E1 (R1 + S1)) (body2 : R2 -> entree E2 (R2 + S2)).
  Context (Hbodies : forall r1 r2, RR r1 r2 -> rutt RPre RPost (sum_rel RR RS) (body1 r1) (body2 r2)).

  Lemma rutt_iter_aux:
    forall (r r' : Rel (entree E1 S1) (entree E2 S2)) (m1 : entree E1 (R1 + S1)) (m2 : entree E2 (R2 + S2)),
      r' <2= r ->
      paco2 (rutt_ RPre RPost (sum_rel RR RS)) bot2 m1 m2 ->
      (forall (r1 : R1) (r2 : R2), RR r1 r2 -> r (EnTree.iter body1 r1) (EnTree.iter body2 r2)) ->
      gpaco2 (rutt_ RPre RPost RS) (euttge_trans_clo RS) r' r
             (EnTree.bind m1 (fun rs : R1 + S1 => match rs with
                                               | inl r0 => Tau (EnTree.iter body1 r0)
                                               | inr s => Ret s
                                               end))
             (EnTree.bind m2 (fun rs : R2 + S2 => match rs with
                                               | inl r0 => Tau (EnTree.iter body2 r0)
                                               | inr s => Ret s
                                               end)).
  Proof.
    intros. generalize dependent m1. generalize dependent m2.
    gcofix CIH'. rename H1 into CIH. intros. punfold H2.
    red in H2. remember (observe m1) as om1. remember (observe m2) as om2.
    revert Heqom1 Heqom2. 
    hinduction H2 before r; intros; apply simpobs in Heqom1, Heqom2.
    - rewrite <- Heqom1, <- Heqom2. setoid_rewrite bind_ret_l.
      inv H.
      + gstep. constructor. gfinal. eauto.
      + gstep. constructor. auto.
    - rewrite <- Heqom1, <- Heqom2. setoid_rewrite bind_tau. gstep.
      constructor. gfinal. pclearbot. eauto.
    - rewrite <- Heqom1, <- Heqom2. setoid_rewrite bind_vis. gstep. constructor.
      auto. intros. gfinal. left. eapply CIH'. apply H0 in H2. pclearbot. auto.
    - rewrite <- Heqom1, <- Heqom2. rewrite bind_tau. rewrite tau_euttge. eapply IHruttF; auto.
    - rewrite <- Heqom1, <- Heqom2. rewrite bind_tau. rewrite tau_euttge. eapply IHruttF; auto.
  Qed.

  Theorem rutt_iter : forall r1 r2, RR r1 r2 -> rutt RPre RPost RS (EnTree.iter body1 r1) (EnTree.iter body2 r2).
  Proof.
    ginit. gcofix CIH. intros r1 r2 Hr.
    specialize (Hbodies r1 r2 Hr) as Hbodies'.
    punfold Hbodies'. red in Hbodies'.
    remember (observe (body1 r1)) as or1.
    remember (observe (body2 r2)) as or2.
    hinduction Hbodies' before r; intros;  apply simpobs in Heqor1, Heqor2.
    - setoid_rewrite unfold_iter. rewrite <- Heqor1. rewrite <- Heqor2.
      setoid_rewrite bind_ret_l.
      inv H.
      + gstep. constructor. gfinal. eauto.
      + gstep. constructor. auto.
    - setoid_rewrite unfold_iter.
      rewrite <- Heqor1. rewrite <- Heqor2. setoid_rewrite bind_tau.
      gstep. constructor. pclearbot. eapply rutt_iter_aux; auto.
    - setoid_rewrite unfold_iter.
      rewrite <- Heqor1. rewrite <- Heqor2. setoid_rewrite bind_vis.
      gstep. constructor. auto. intros. eapply rutt_iter_aux; auto.
      apply H0 in H1. pclearbot. auto.
    - setoid_rewrite unfold_iter. rewrite <- Heqor1.
      eapply rutt_iter_aux; auto. intros. inv PR.
      apply Hbodies in Hr. rewrite <- Heqor1 in Hr. auto.
    - setoid_rewrite unfold_iter. rewrite <- Heqor2.
      eapply rutt_iter_aux; auto. intros. inv PR.
      apply Hbodies in Hr. rewrite <- Heqor2 in Hr. auto.
  Qed.
End RuttIter.


Section RuttTrans.
Context (E1 E2 E3 : Type) `{enc1 : EncodedType E1} `{enc2 : EncodedType E2} `{enc3 : EncodedType E3}.
Context (R1 R2 R3 : Type).
Context (RPre1 : Rel E1 E2) (RPre2 : Rel E2 E3).
Context (RPost1 : PostRel E1 E2) (RPost2 : PostRel E2 E3).
Context (RR1 : Rel R1 R2) (RR2 : Rel R2 R3).

Theorem rutt_trans : forall t1 t2 t3,
    rutt RPre1 RPost1 RR1 t1 t2 ->
    rutt RPre2 RPost2 RR2 t2 t3 ->
    rutt (rcompose RPre1 RPre2) (RComposePostRel RPre1 RPre2 RPost1 RPost2) (rcompose RR1 RR2) t1 t3.
Proof.
  ginit. gcofix CIH. intros t1 t2 t3 Ht12 Ht23.
  punfold Ht12. red in Ht12. setoid_rewrite entree_eta.
  setoid_rewrite entree_eta in Ht23.
  hinduction Ht12 before r; intros.
  - punfold Ht23. red in Ht23. cbn in Ht23.
    remember (RetF r2) as x. hinduction Ht23 before r; intros; try inv Heqx; subst.
    + gstep. constructor. econstructor. split; eauto.
    + rewrite tau_euttge. rewrite (entree_eta t2). eauto.
  - pclearbot. rewrite tau_euttge in Ht23.
    punfold H. red in H. punfold Ht23. red in Ht23.
    cbn in Ht23. genobs m1 om1.
    genobs t3 ot3.
    hinduction Ht23 before r; intros.
    + rewrite tau_euttge. rewrite entree_eta. subst.
      remember (RetF r1) as x. hinduction H0 before r; intros; inv Heqx; subst.
      * gstep. constructor. econstructor; eauto.
      * rewrite tau_euttge. rewrite entree_eta. eauto.
    + gstep. constructor. pclearbot. fold_ruttF H0.
      rewrite tau_euttge in H0. gfinal. eauto.
    + rewrite tau_euttge. subst. rewrite entree_eta.
      clear Heqot3. remember (VisF e1 k1) as x.
      hinduction H1 before r; intros; inv Heqx; inj_existT; subst.
      * gstep. constructor. econstructor; eauto.
        intros. inv H3. inj_existT. subst.
        specialize (H8 e0 H H1) as [c [Hc1 Hc2] ].
        apply H0 in Hc1. apply H2 in Hc2. pclearbot.
        gfinal. eauto.
      * rewrite tau_euttge. rewrite entree_eta. eauto.
    + eapply IHHt23; eauto. fold_ruttF H. rewrite tau_euttge in H.
      subst. pstep_reverse.
    + rewrite tau_euttge with (t := t2). rewrite entree_eta with (t := t2).
      eauto.
  - punfold Ht23. red in Ht23. cbn in Ht23.
    remember (VisF e2 k2) as x. 
    hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst.
    + gstep. constructor. econstructor; eauto.
      intros. inv H3; inj_existT; subst.
      specialize (H8 e3 H1 H) as [d [Hd1 Hd2]].
      gfinal. left. eapply CIH.
      apply H2 in Hd1. pclearbot. eapply Hd1.
      eapply H0 in Hd2. pclearbot. eapply Hd2.
    + rewrite tau_euttge. rewrite (entree_eta t2). eauto.
  - rewrite tau_euttge. rewrite (entree_eta t0). eauto.
  - rewrite tau_euttge in Ht23. rewrite (entree_eta t0) in Ht23. eauto.
Qed.

End RuttTrans.

Theorem rutt_mon E1 E2 `{EncodedType E1} `{EncodedType E2} R1 R2
        (RPre1 RPre2 : Rel E1 E2) (RPost1 RPost2 : PostRel E1 E2)
        (RR1 RR2 : Rel R1 R2) :
  (forall e1 e2, RPre1 e1 e2 -> RPre2 e1 e2) ->
  (forall e1 e2 a b, RPost2 e1 e2 a b -> RPost1 e1 e2 a b) ->
  (forall r1 r2, RR1 r1 r2 -> RR2 r1 r2) ->
  forall t1 t2,
    rutt RPre1 RPost1 RR1 t1 t2 ->
    rutt RPre2 RPost2 RR2 t1 t2.
Proof.
  intros HPre HPost HRR. pcofix CIH.
  intros. punfold H2. red in H2. pstep. red.
  hinduction H2 before r; intros; pclearbot; constructor; eauto.
  intros.
  assert (RPost1 e1 e2 a b). auto. apply H2 in H4.
  pclearbot. auto.
Qed.

Theorem rutt_trans' E `{EncodedType E} R (RPre : Rel E E) (RPost : PostRel E E)
        (RR : Rel R R) :
  Transitive RPre ->
  TransitivePostRel RPre RPost ->
  Transitive RR ->
  forall t1 t2 t3,
    rutt RPre RPost RR t1 t2 ->
    rutt RPre RPost RR t2 t3 ->
    rutt RPre RPost RR t1 t3.
Proof.
  intros Htranspre Htranspost Htransr t1 t2 t3 Ht12 Ht23.
  assert (Ht13 :rutt (rcompose RPre RPre) (RComposePostRel RPre RPre RPost RPost) (rcompose RR RR) t1 t3).
  eapply rutt_trans; eauto.
  eapply rutt_mon; try apply Ht13; try (apply trans_rcompose; auto).
  intros. apply Htranspost in H0. constructor. auto.
Qed.

Section RuttProper.
Context (E : Type) `{enc : EncodedType E}.
Context (R : Type).
Context (RPre : Rel E E) (RPost : PostRel E E) (RR : Rel R R).
(* remember we are working with a partial equivalence relaation *)
Context (HPresym : Symmetric RPre) (HRsym : Symmetric RR).
Context (HPostsym : SymmetricPostRel RPost).
Context (HPretrans : Transitive RPre) (HRtrans : Transitive RR).
Context (HPosttrans : TransitivePostRel RPre RPost).

Theorem rutt_proper : Proper (rutt RPre RPost RR ==> rutt RPre RPost RR ==> flip impl) (rutt RPre RPost RR).
Proof.
  intros t1 t2 Ht12 t3 t4 Ht34 Ht24. 
  assert (Ht14 : rutt RPre RPost RR t1 t4).
  { 
    eapply rutt_trans'; eauto.
  }
  clear Ht24 Ht12.
  assert (Ht43 : rutt RPre RPost RR t4 t3).
  { apply rutt_sym; auto. }
  eapply rutt_trans'; eauto.
Qed.


End RuttProper.

(* write some general rewriting principles that can apply to types equiv 

RPre RPost RR

Transitive RPre

PostTransitive RPost

Transitive RR


Proper (rutt RPre RPost RR ==> rutt RPre RPost RR ==> flip impl) (rutt RPre RPost RR)


*)
