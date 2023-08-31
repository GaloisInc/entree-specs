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
Require Import Coq.Classes.Morphisms.
Require Export ClosingSubst.
Require Export EnTreeStep.
Definition valid_denote {t} (vv : denote_type t) : Prop :=
  types_equiv t vv vv.


Inductive approx_comp {t MR} (j : nat) (R : nat -> forall t, denote_type t -> closed_value t -> Prop) :
           forall (m : mtree (denote_mfix_ctx MR) (denote_type t)) (c : comp t [] MR), Prop := 
  approx_comp_intro m c : 
    (forall j', j' < j ->
          (forall vv : denote_type t, multi_step j' m (ret vv) -> exists v, eval_rel_stuck c (inl v) /\ R (j - j') t vv v) /\
          (forall (tin tout : type) Rcall (xR : var Rcall MR) (x : var (tin, tout) Rcall) (vvcall : denote_type tin) k,
             multi_step j' m (vv <- call_term x xR vvcall;; k vv) ->
             exists (vcall : closed_value tin) (E : eval_context t MR (inr (SmallStepSeq.callv xR x vcall) ) true) (c' : comp t [] MR),
               R (j - j') tin vvcall vcall /\
                 eval_rel_stuck c (inr c') /\ stuck_call c' (SmallStepSeq.callv xR x vcall) E /\
                   forall j'' (vvret : denote_type tout) (vret : closed_value tout), j'' < j - j' -> 
                       R j'' tout vvret vret ->
                       approx_comp j'' R (k vvret) (subst_eval_context E (comp_ret vret))))
            -> approx_comp j R m c.



Inductive log_rel_list {t} (R : Rel (denote_type t) (closed_value t) ) : 
   denote_type (List t) -> closed_value (List t)  -> Prop := 
 | log_rel_list_nil : log_rel_list R nil val_nil
 | log_rel_list_cons vvh vh vvt vt : R vvh vh -> log_rel_list R vvt vt ->
                                     log_rel_list R (cons vvh vvt) (val_cons vh vt) 
.

(* well founded relation over nat * type *)
(* Coq.Wellfounded.Union 
   

*)

(* need to make a step indexed version *)
Derive Subterm for type.

Definition log_rel_dec : Rel (nat * type) (nat * type) := slexprod nat type lt type_subterm.

Instance log_rel_dec_wf : WellFounded log_rel_dec.
Proof.
  apply Lexicographic_Product.wf_slexprod.
  - apply PeanoNat.Nat.lt_wf_0.
  - apply well_founded_type_subterm.
Qed.

Equations approx_val (n : nat) (t : type) (vv : denote_type t) (v : closed_value t) : Prop by wf (n,t) log_rel_dec := {
  approx_val 0 _ _ _ := True;
  approx_val (S m') Nat n (val_const m) := n = m;
  approx_val (S m) (Pair t1 t2) (vv1, vv2) (val_pair v1 v2)  := approx_val (S m) t1 vv1 v1 /\ approx_val (S m) t2 vv2 v2;
  approx_val (S m) (List t) l vl := log_rel_list (fun vv v => approx_val (S m) t vv v) l vl;
  approx_val (S m) (Arrow t1 MR t2) f (val_abs c) := 
    forall vv v m' (H : m' < S m), valid_denote vv -> approx_val m' t1 vv v -> 
                              approx_comp m' (fun n t v vv => forall (H : n < S m), 
                                                  approx_val n t v vv) (f vv) (subst_comp_cons c v) 
}.
Next Obligation. 
  right. constructor. constructor.
Qed.
Next Obligation.
  right. constructor. constructor.
Qed.
Next Obligation.
  right. constructor. constructor.
Qed.
Next Obligation.
  left. auto.
Qed.
Next Obligation.
  left. auto.
Qed.


Lemma lower_approx_comp_aux1 : forall (P : nat -> Prop) n t MR c m R1 R2,
    P n ->
    (forall n m, n <= m -> P m -> P n) ->
    (forall n' t vv v, P n' -> (R1 n' t vv v <-> R2 n' t vv v)) ->
    approx_comp (t := t) (MR := MR) n R1 m c -> 
    approx_comp n R2 m c.
Proof.
  intros P n.
  induction n as [ n IHn ] using (well_founded_induction lt_wf).
  (* - intros t MR c m R1 R2 Hn Hclosed HR Hcm.
    econstructor. intros. lia. *)
  intros t MR c m R1 R2 Hn Hclosed HR Hcm.
  dependent induction Hcm.
  econstructor; eauto. intros j' Hj'. specialize (H _ Hj').
  destruct H as [Hret Hstuck].
  split.
  - intros vv Hvv. apply Hret in Hvv. decompose record Hvv. eexists. split; eauto.
    apply HR; auto. eapply Hclosed with (m := n);  eauto. lia.
  - intros. apply Hstuck in H. destruct H as [vcall [E [c' [H1 [H2 [H3 H4]]]]]].
    exists vcall, E, c'.
    split; try split; try split; auto.
    + apply HR; auto. eapply Hclosed with (m := n);  eauto. lia. 
    + intros j'' vvret vret Hvret Hj''.
      eapply IHn; eauto. lia. eapply Hclosed with (m := n); auto. lia.
      eapply H4; eauto. eapply HR; eauto. eapply Hclosed with (m := n); auto. lia.
Qed.

Lemma lower_approx_val_aux : forall n t v vv, approx_val (S n) t vv v -> approx_val n t vv v.
Proof.
  intros n. induction n; intros.
  - simp approx_val. auto.
  - induction t.
    + red in v. dependent destruction v; try inversion x. simp approx_val in H.
      simp approx_val.
    + red in v. clear - H IHt. dependent induction v; try inversion x.
      * simp approx_val. simp approx_val in H.
        inversion H. subst. constructor.
      * simp approx_val. simp approx_val in H. inversion H. subst.
        inj_existT. subst.
        constructor. apply IHt. auto.
        specialize (IHv2 t v2 eq_refl eq_refl JMeq_refl vvt).
        simp approx_val in IHv2.
    + red in v. dependent destruction v; try inversion x.
      destruct vv as [vv1 vv2]. simp approx_val in H. simp approx_val.
      destruct H. split; auto.
    + red in v. dependent destruction v; try inversion x.
      rename vv into f. simp approx_val in H. simp approx_val.
      intros vv v m' Hm' Hvv Hv. eapply H in Hv; eauto.
      eapply lower_approx_comp_aux1 with (P := fun m' => m' < S n); intros; eauto.
      lia. simpl.
      split; intros; apply H1; lia.
Qed.

Lemma lower_approx_comp_aux2 : forall n t MR c m R,
    (forall n m t v vv, n < m -> (R m t v vv : Prop) -> R n t v vv) ->
    approx_comp (t := t) (MR := MR) (S n) R c m ->
    approx_comp n R c m.
Proof.
  intros n. induction n.
  { intros. constructor. intros. lia. }
  intros t MR c m R HR Hcm.
  dependent destruction Hcm. constructor. intros j' Hj'.
  assert (Hj'' : j' < S (S n) ). lia.
  specialize (H j' Hj''). destruct H as [Hret Hstuck].
  split.
  - intros vv Hvv. eapply Hret in Hvv as [v [Hv1 Hv2]].
    eexists. split; eauto. eapply HR; try apply Hv2. lia. 
  - intros tin tout Rcall xR x vvcall k Hca. apply Hstuck in Hca.
    destruct Hca as [vcall [E [c' [HE1 [HE2 [HE3 HE4]]]]]].
    exists vcall, E, c'. split.
    + eapply HR; try apply HE1. lia.
    + do 2 (split; auto). intros.
      eapply HE4; auto. lia.
Qed.


Lemma lower_approx_comp_aux3 n j t MR c m : 
  n < j->
  approx_comp n approx_val m c ->
  approx_comp (t := t) (MR := MR) n
              (fun n t vv v => forall (H : n < j), approx_val n t vv v) m c.
Proof.
  intros. eapply lower_approx_comp_aux1 with (P := fun n => n < j); eauto.
  lia. intros. simpl. split; intros; auto.
Qed.

Lemma lower_approx_val : forall n m, n < m -> forall t vv v, approx_val m t vv v -> approx_val n t vv v.
Proof.
  intros n m Hnm. red in Hnm. dependent induction Hnm.
  - intros. apply lower_approx_val_aux. auto.
  - intros. apply lower_approx_val_aux in H. auto.
Qed.

Lemma lower_approx_comp : forall n j, n < j -> forall t MR c m R,
    (forall n m t v vv, n < m -> (R m t v vv : Prop) -> R n t v vv) ->
    approx_comp (t := t) (MR := MR) j R c m ->
    approx_comp n R c m.
Proof.
  intros n j Hnj. red in Hnj. dependent induction Hnj.
  - intros. apply lower_approx_comp_aux2; auto.
  - intros. apply lower_approx_comp_aux2 in H0; auto.
Qed.

(* may also need that vv is valid *)
Inductive closing_subst_approx (n : nat) : forall Γ, denote_ctx Γ -> closing_subst Γ ->  Prop :=
  | closing_subst_approx_nil : closing_subst_approx n nil tt tt
  | closing_subst_approx_cons t Γ v ρ vv hyps : 
    approx_val n t v vv -> closing_subst_approx n Γ ρ hyps ->
    closing_subst_approx n (t :: Γ) (v, ρ) (vv, hyps)
.

Lemma lower_closing_subst_approx:
  forall (n m : nat) (Γ : ctx) (ρ : closing_subst Γ) (hyps : denote_ctx Γ),
    closing_subst_approx n Γ hyps ρ ->
    m < n -> closing_subst_approx m Γ hyps ρ.
Proof.
  intros n m Γ ρ hyps H Hm.
  generalize dependent Γ. intros Γ. induction Γ.
  intros. destruct ρ. destruct hyps. constructor.
  intros [v ρ] [vv hyps] H. dependent destruction H.
  constructor; auto. eapply lower_approx_val; eauto.
Qed.

(* notably properness is gone, that may make things more complicated

   could presumably use 
Lemma proper_approx_aux : forall n,
    (forall t v vv1 vv2, types_equiv t vv1 vv2 -> approx_val n t vv1 v -> approx_val n t vv2 v) /\
    (forall t MR c m1 m2, comp_equiv_rutt (t := t) (MR := MR) m1 m2 -> 
       approx_comp n approx_val m1 c -> approx_comp n approx_val m2 c).
Proof.
  intros n. induction n as [ n IHn ] using (well_founded_induction lt_wf).
  assert (IHv : forall y, y < n -> 
           (forall (t : vtype) (v : closed_value t) (vv1 vv2 : denote_type t),
         types_equiv t vv1 vv2 -> approx_val y t vv1 v -> approx_val y t vv2 v)).
  { intros. apply IHn in H. destruct H. eauto. }
  assert (IHc : forall y, y < n -> 
           (forall t MR c m1 m2, comp_equiv_rutt (t := t) (MR := MR) m1 m2 -> 
       approx_comp y approx_val m1 c -> approx_comp y approx_val m2 c)).
  { intros. apply IHn in H. destruct H. eauto. }
  clear IHn.
  split; intros.
  - destruct n. simp approx_val. auto.
    induction t.
    + red in v. dependent destruction v; try inversion x. simp approx_val in *.
      simp types_equiv in H. subst. auto.
    + simp approx_val. simp approx_val in H0. 
      red in v. clear - H H0 IHt. dependent induction v; try inversion x.
      * dependent destruction H0. simp types_equiv in H. dependent destruction H.
        constructor.
      * dependent destruction H0. simp types_equiv in H.
        dependent destruction H. rename b into vv1. rename l2 into vv2.
        constructor; eauto.
        eapply IHv2; eauto. simp types_equiv.
    + red in v. dependent destruction v; try inversion x.
      simp types_equiv in H. destruct vv1 as [vv11 vv12]. destruct vv2 as [vv21 vv22].
      dependent destruction H. cbn in *. simp approx_val in *.
      destruct H0. split; eauto.
    + red in v. dependent destruction v; try inversion x.
      rename vv1 into f1. rename vv2 into f2. simp types_equiv in H. simp approx_val.
      intros vv v m' Hm' Hvv Hv.
      apply H in Hvv as Hvv'.
      eapply lower_approx_comp_aux1 with (P := fun m' => m' < S n) (R1 := approx_val); eauto. intros. lia.
      intros. split; intros; auto.
      eapply IHc; eauto. simp approx_val in H0. 
      eapply lower_approx_comp_aux1 with (P := fun m' => m' < S n); eauto. lia.
      intros. simpl. split; intros; auto.
  - constructor. intros. inversion H0. subst. specialize (H2 H1) as [Hret Hstuck].
    split.
    + intros. rewrite <- H in H2. eapply Hret. auto.
    + intros. rewrite <- H in H2. apply Hstuck in H2. eauto.
Qed.

#[local] Instance proper_approx_val {n t} : Morphisms.Proper (types_equiv t ==> eq ==> Basics.flip Basics.impl) (approx_val n t).
Proof.
  repeat intro. subst. destruct (proper_approx_aux n). eapply H0; eauto. symmetry. auto.
Qed.

#[local] Instance proper_approx_comp {n t MR} : Morphisms.Proper (comp_equiv_rutt (t := t) (MR := MR)  ==> eq ==> Basics.flip Basics.impl) (approx_comp n approx_val).
Proof.
  repeat intro. subst. destruct (proper_approx_aux n). eapply H2; eauto. symmetry. auto.
Qed.
*)

(* needs to include this new bodies steps t *)
Equations log_rel_bodies_step {MR R1 R2} 
          (n : nat)
          (dbodies : forall arg : denote_call_frame R2, mtree (denote_mfix_ctx (R1 :: MR)) (encodes arg))
          (bodies : mfix_bodies [] MR R1 R2) : Prop :=
  log_rel_bodies_step _ f mfix_bodies_nil := True;
  log_rel_bodies_step n f (mfix_bodies_cons cbody bodies) :=
   approx_val n (Arrow t1 (R1 :: MR) t2) (fun vv => f (inl vv)) (val_abs cbody) /\
      log_rel_bodies_step n (fun vv => f (inr vv)) bodies.


Definition comp_rel {t Γ MR} 
           (m : denote_ctx Γ -> mtree (denote_mfix_ctx MR) (denote_type t))
           (c : comp t Γ MR) : Prop :=
  forall n (hyps : denote_ctx Γ) (ρ : closing_subst Γ), 
    closing_subst_approx n Γ hyps ρ -> approx_comp n approx_val (m hyps) (close_comp Γ ρ c).

Definition val_rel {t Γ MR}
           (vm : denote_ctx Γ -> mtree (denote_mfix_ctx MR) (denote_type t))
           (v : value t Γ) : Prop :=
  forall n (hyps : denote_ctx Γ) (ρ : closing_subst Γ), 
    closing_subst_approx n Γ hyps ρ -> 
    exists vv, vm hyps ≅ ret vv /\
            approx_val n t vv (close_value Γ ρ v).


Definition bodies_rel {Γ MR R1 R2}
           (dbodies : denote_ctx Γ -> forall arg : denote_call_frame R2, mtree (denote_mfix_ctx (R1 :: MR)) (encodes arg))
           (bodies : mfix_bodies Γ MR R1 R2) : Prop :=
  forall n (hyps : denote_ctx Γ) (ρ : closing_subst Γ), 
    closing_subst_approx n Γ hyps ρ -> 
     log_rel_bodies_step n (dbodies hyps) (close_bodies Γ ρ bodies).
