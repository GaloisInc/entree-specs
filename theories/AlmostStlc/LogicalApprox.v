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
From Paco Require Import paco.

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


(* should the function case assume types_equiv vv vv for argument?*)
Equations approx_val (n : nat) (t : type) (vv : denote_type t) (v : closed_value t) : Prop by wf (n,t) log_rel_dec := {
  approx_val 0 _ _ _ := True;
  approx_val (S m') Nat n (val_const m) := n = m;
  approx_val (S m) (Pair t1 t2) (vv1, vv2) (val_pair v1 v2)  := approx_val (S m) t1 vv1 v1 /\ approx_val (S m) t2 vv2 v2;
  approx_val (S m) (Sum t1 t2) vv (val_inl v1) := match vv with
                                                  | inl vv1 => approx_val (S m) t1 vv1 v1
                                                  | inr _ => False 
                                                  end;
  approx_val (S m) (Sum t1 t2) vv (val_inr v2) := match vv with
                                                  | inl _ => False
                                                  | inr vv2 => approx_val (S m) t2 vv2 v2
                                                  end;
  approx_val (S m) (List t) l vl := log_rel_list (fun vv v => approx_val (S m) t vv v) l vl;
  approx_val (S m) (Arrow t1 MR t2) f (val_abs c) := 
    forall vv v m' (H : m' < S m), approx_val m' t1 vv v -> 
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
      * simp approx_val. simp approx_val in H. destruct vv; try contradiction.
        auto.
      * simp approx_val. simp approx_val in H. destruct vv; try contradiction.
        auto.
    + red in v. dependent destruction v; try inversion x.
      rename vv into f. simp approx_val in H. simp approx_val.
      intros vv v m' Hm' Hv. eapply H in Hv; eauto.
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

Lemma lower_approx_val' : forall n m, n <= m -> forall t vv v, approx_val m t vv v -> approx_val n t vv v.
Proof.
  intros. inversion H; auto.
  eapply lower_approx_val; try eapply H0. lia.
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

Lemma lower_approx_comp' : forall n j, n <= j -> forall t MR c m R,
    (forall n m t v vv, n < m -> (R m t v vv : Prop) -> R n t v vv) ->
    approx_comp (t := t) (MR := MR) j R c m ->
    approx_comp n R c m.
Proof.
  intros. inversion H; auto.
  eapply lower_approx_comp; try apply H1. lia. eauto.
Qed.

(* 
   wait this seems weird,

   example j=0 e1 has a number of steps to eval to a value

   e1'<=0 e2 is just true, how can that be enough

   e1 = (1 + 2) e1' = 3

   e2 = 4

   (1 + 2) --> 3
   3 <=0 4
   ~(1 + 2 <=1 4) ?????

   lets bring this up to nick tomorrow
   Lemma that is typically true according to nick
   e1 --> e1' => e1' <=j e2 => e1 <=(j+1) e2

   think about if this makes sense, especially in light of
   whether you decrement steps in the ret case 

*)
(*
Lemma approx_comp_multi_step t MR c m1 m2 n :
  multi_step 1 m1 m2 ->
  approx_comp (t := t) (MR := MR) n approx_val m2 c ->
  approx_comp n approx_val m1 c.
Proof.
  intros. dependent destruction H. dependent destruction H. dependent destruction H0.
  constructor. intros. inversion H1. subst.
  split.
  - intros. rewrite H0 in H4.
  rewrite <- H in H1.
*)


(* could multi_step j t1 t2 supposed to be at most j steps not exactly j steps?, maybe discuss with nick *)
Lemma approx_comp_multi_step_1 t MR c m1 m2 j2 :
  multi_step 1 m1 m2 ->
  approx_comp (t := t) (MR := MR) j2 approx_val m2 c ->
  approx_comp (S j2) approx_val m1 c.
Proof.
  intros Hstep Happrox. constructor.
  intros. destruct j2 as [ | j2].
  { 
    assert (j' = 0). lia. subst.
    clear - Hstep. dependent destruction Hstep.
    dependent destruction Hstep. dependent destruction H0.
    split.
    intros. rewrite H0 in H1. dependent destruction H1.  pinversion H1. inversion CHECK.
    intros. dependent destruction H1. exfalso.
    rewrite H0 in H1. unfold call_term in H1. destruct (call_mrec x xR vvcall).
    setoid_rewrite bind_trigger in H1. setoid_rewrite bind_vis in H1. pinversion H1. inversion CHECK.
  }
  dependent destruction Happrox.
  destruct j' as [ | j''].
  { split.
    - intros. dependent destruction H1. rewrite H1 in Hstep. dependent destruction Hstep.
      dependent destruction H2. pinversion H1. inversion CHECK.
    - intros. dependent destruction H1. clear - H1 Hstep. exfalso.
      rewrite H1 in Hstep. dependent destruction Hstep. dependent destruction H0.
      unfold call_term in H. destruct (call_mrec x xR vvcall). setoid_rewrite bind_trigger in H.
      setoid_rewrite bind_vis in H. pinversion H. inversion CHECK.
  }
  remember (S j'') as j'.
  assert (Hj' : j' - 1 < S j2). lia.
  specialize (H _ Hj'). destruct H as [Hret Hstuck].
  split.
  - intros. clear Hstuck.
    assert (multi_step (j' - 1) m2 (ret vv)).
    dependent destruction Hstep. dependent destruction H. rewrite H in H1.
    dependent destruction Hstep. rewrite <- H. dependent destruction H2. pinversion H2. inversion CHECK.
    dependent destruction H4. cbn. assert (n - 0 = n). lia. rewrite H4. apply eqit_inv_Tau in H3.
    rewrite H3. auto.
    eapply Hret in H1. destruct H1 as [v [Hv1 Hv2]]. eexists. split; eauto.
    eapply lower_approx_val'; try apply Hv2. lia.
 - intros. clear Hret.
   assert (multi_step (j' - 1) m2 ((vv <- call_term x xR vvcall;; k vv))).
   dependent destruction Hstep. dependent destruction H. rewrite H in H1.
   dependent destruction Hstep. rewrite <- H. dependent destruction H2.
   unfold call_term in H2. destruct (call_mrec x xR vvcall). setoid_rewrite bind_trigger in H2.
   setoid_rewrite bind_vis in H2. pinversion H2. inversion CHECK.
   dependent destruction H4. cbn. assert (n - 0 = n). lia. rewrite H4.
   apply eqit_inv_Tau in H3. rewrite H3. auto.
   eapply Hstuck in H1. 
   destruct H1 as [vcall [E [c' [HE1 [HE2 [HE3 HE4]]]]]].
   exists vcall, E, c'. split; [ | split; [ | split] ]; auto.
   + eapply lower_approx_val'; try apply HE1. lia.
   + intros. eapply HE4; auto. lia.
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


#[global] Instance proper_approx_comp {n t MR} : 
  Proper (eq_itree (R1 := denote_type t) eq ==> eq ==> Basics.flip Basics.impl)
         (approx_comp (MR := MR) n approx_val).
Proof. 
  do 2 red. intros m1 m2 Hm12 c1 c2 Hc12 Happrox. subst.
  constructor. intros. inversion Happrox. subst. specialize (H0 j' H).
  destruct H0 as [Hret Hstuck].
  split. 
  - intros. setoid_rewrite Hm12 in H0. eauto.
  - intros. setoid_rewrite Hm12 in H0. eauto.
Qed.


Lemma approx_comp_multi_step t MR c m1 m2 j1 j2 :
  multi_step j1 m1 m2 ->
  approx_comp (t := t) (MR := MR) j2 approx_val m2 c ->
  approx_comp (j1 + j2) approx_val m1 c.
Proof.
  revert t MR c m1 m2 j2. induction j1.
  - cbn. intros. dependent destruction H. rewrite H. auto.
  - cbn. intros. dependent destruction H. eapply IHj1 in H; eauto.
    eapply approx_comp_multi_step_1; eauto. econstructor; eauto.
    constructor. reflexivity.
Qed.
    
#[global] Instance multi_step_approx_comp_proper t MR n m :
  Proper (multi_step n ==> eq ==> Basics.flip Basics.impl) (approx_comp (t := t) (MR := MR) m approx_val).
Proof.
  repeat intro. subst. eapply approx_comp_multi_step in H1; eauto.
  eapply lower_approx_comp'; try apply H1; auto. lia.
  intros. eapply lower_approx_val; try apply H2; auto.
Qed.


Lemma approx_comp_eval_rel_stuck1 t MR (c1 c2 : comp t [] MR) m n :
  eval_rel_stuck c1 (inr c2) ->
  approx_comp n approx_val m c1 -> approx_comp n approx_val m c2.
Proof.
  intros Heval. dependent induction Heval; auto.
  specialize (IHHeval c2 m eq_refl). intros. apply IHHeval.
  inversion H0. subst. constructor. intros j Hj.
  specialize (H1 j Hj) as [Hret Hstuck]. split.
  - clear Hstuck. intros. apply Hret in H1. destruct H1 as [v [Hv1 Hv2]].
    exists v. split; auto. clear - Hv1 H. dependent destruction Hv1. 
    + inversion H. subst. inversion H0. subst. rewrite H1 in H2. injection H2. intros. subst. auto.
    + inversion H. subst. rewrite H0 in H1. discriminate.
  -  clear Hret. intros. apply Hstuck in H1. 
     destruct H1 as [vcall [E [c' [HE1 [HE2 [HE3 HE4] ]]]]].
     exists vcall, E, c'. split; auto. split; auto.
     clear - HE2 H. dependent destruction HE2.
     + inversion H. subst. inversion H0. subst. rewrite H1 in H2. injection H2. intros.
       subst. auto.
     + inversion H. subst. assert (step c' = inl None). eapply stuck_call_stuck'. eauto.
       rewrite H1 in H2. discriminate.
Qed.

Lemma approx_comp_eval_rel_stuck2 t MR (c1 c2 : comp t [] MR) m n :
  eval_rel_stuck c1 (inr c2) ->
  approx_comp n approx_val m c2 -> approx_comp n approx_val m c1.
Proof.
  intros Heval. dependent induction Heval; auto. intros H0.
  specialize (IHHeval c2 m eq_refl H0). 
  clear H0. inversion IHHeval. subst. constructor.
  intros j Hj. specialize (H0 j Hj). destruct H0 as [Hret Hstuck]. split.
  - clear Hstuck. intros. eapply Hret in H0.
    destruct H0 as [v [Hv1 Hv2]]. exists v. split; auto.
    econstructor; eauto.
  - clear Hret. intros. eapply Hstuck in H0.
    destruct H0 as [vcall [E [c' [HE1 [HE2 [HE3 HE4] ]]]]].
    exists vcall, E, c'. split; auto. split; auto.
    econstructor; eauto.
Qed.
(*
Lemma approx_comp_multi_step' t MR c m1 m2 n j : 
  multi_step j m1 m2 ->
  approx_comp (t := t) (MR := MR) n approx_val m1 c ->
  approx_comp n approx_val m2 c.
Proof.
  intros Hstep Happrox.
  constructor. intros. inversion Happrox.
  subst. split.
  - intros vv Hstep'.
Abort. (* actually this is wrong, m1 <=n c might hold because n is not enough steps
          to distinguish m1 and c
        *)
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

Lemma lower_log_rel_bodies_step MR R1 R2
          (j1 j2: nat)
          (dbodies : forall arg : denote_call_frame R2, mtree (denote_mfix_ctx (R1 :: MR)) (encodes arg))
          (bodies : mfix_bodies [] MR R1 R2) : 
  j1 < j2 ->
  log_rel_bodies_step j2 dbodies bodies -> log_rel_bodies_step j1 dbodies bodies.
Proof.
  revert bodies dbodies. intros bodies. dependent induction bodies.
  - setoid_rewrite log_rel_bodies_step_equation_1. auto.
  - setoid_rewrite log_rel_bodies_step_equation_2. intros. destruct H0.
    split. eapply lower_approx_val; try apply H0; auto. eauto.
Qed.

Lemma lower_log_rel_bodies_step' MR R1 R2
          (j1 j2: nat)
          (dbodies : forall arg : denote_call_frame R2, mtree (denote_mfix_ctx (R1 :: MR)) (encodes arg))
          (bodies : mfix_bodies [] MR R1 R2) : 
  j1 <= j2 ->
  log_rel_bodies_step j2 dbodies bodies -> log_rel_bodies_step j1 dbodies bodies.
Proof.
  intros. destruct H. auto.
  eapply lower_log_rel_bodies_step; try apply H0. lia.
Qed.

Definition comp_rel {t Γ MR} 
           (m : denote_ctx Γ -> mtree (denote_mfix_ctx MR) (denote_type t))
           (c : comp t Γ MR) : Prop :=
  forall n (hyps : denote_ctx Γ) (ρ : closing_subst Γ), 
    closing_subst_approx n Γ hyps ρ -> approx_comp n approx_val (m hyps) (close_comp Γ ρ c).

Definition bounded_comp_rel {t Γ MR} n
           (m : denote_ctx Γ -> mtree (denote_mfix_ctx MR) (denote_type t))
           (c : comp t Γ MR) : Prop :=
  forall j (hyps : denote_ctx Γ) (ρ : closing_subst Γ), 
    j <= n ->
    closing_subst_approx j Γ hyps ρ -> approx_comp j approx_val (m hyps) (close_comp Γ ρ c).

Definition val_rel {t Γ MR}
           (vm : denote_ctx Γ -> mtree (denote_mfix_ctx MR) (denote_type t))
           (v : value t Γ) : Prop :=
  forall n (hyps : denote_ctx Γ) (ρ : closing_subst Γ), 
    closing_subst_approx n Γ hyps ρ -> 
    exists vv, vm hyps ≅ ret vv /\
            approx_val n t vv (close_value Γ ρ v).

Definition bounded_val_rel {t Γ MR} n
           (vm : denote_ctx Γ -> mtree (denote_mfix_ctx MR) (denote_type t))
           (v : value t Γ) : Prop :=
  forall j (hyps : denote_ctx Γ) (ρ : closing_subst Γ), 
    j <= n ->
    closing_subst_approx j Γ hyps ρ ->
    exists vv, vm hyps ≅ ret vv /\
            approx_val j t vv (close_value Γ ρ v).

Definition bodies_rel {Γ MR R1 R2}
           (dbodies : denote_ctx Γ -> forall arg : denote_call_frame R2, mtree (denote_mfix_ctx (R1 :: MR)) (encodes arg))
           (bodies : mfix_bodies Γ MR R1 R2) : Prop :=
  forall n (hyps : denote_ctx Γ) (ρ : closing_subst Γ), 
    closing_subst_approx n Γ hyps ρ -> 
     log_rel_bodies_step n (dbodies hyps) (close_bodies Γ ρ bodies).

Definition bounded_bodies_rel {Γ MR R1 R2} n
           (dbodies : denote_ctx Γ -> forall arg : denote_call_frame R2, mtree (denote_mfix_ctx (R1 :: MR)) (encodes arg))
           (bodies : mfix_bodies Γ MR R1 R2) : Prop :=
  forall j (hyps : denote_ctx Γ) (ρ : closing_subst Γ), 
    j <= n ->
    closing_subst_approx j Γ hyps ρ -> 
     log_rel_bodies_step j (dbodies hyps) (close_bodies Γ ρ bodies).
