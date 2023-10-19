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
Require Export SubstCommute.

(* I think what I need is a more general notion of substitution *)

(*
Fixpoint closing_subst (Γ : ctx) : Type :=
  match Γ with
  | [] => unit
  | t :: Γ => (closed_value t * closing_subst Γ)%type 
  end.
*)


Fixpoint open_subst (Γ1 Γ2 : ctx) : Type :=
  match Γ1 with
  | [] => unit
  | t :: Γ1 => (value t Γ2 * open_subst Γ1 Γ2)%type
  end.

Definition closing_subst (Γ : ctx) : Type := open_subst Γ [].

Equations extend_closing_subst {t} Γ (ρ : closing_subst Γ) (v : closed_value t) : closing_subst (Γ ++ [t]) :=
  extend_closing_subst [] tt v := (v, tt);
  extend_closing_subst (t0 :: Γ) (v0, ρ) v := (v0, extend_closing_subst Γ ρ v).

Equations weaken_subst Γ1 {Γ2} (ρ : closing_subst Γ1) : open_subst Γ1 Γ2 :=
  weaken_subst nil tt := tt;
  weaken_subst (t :: Γ1) (v, ρ) := (weaken_r_value _ v, weaken_subst Γ1 ρ).

Equations close_value_app {t Γ2} Γ1 (ρ : open_subst Γ1 Γ2) (v : value t (Γ1 ++ Γ2))  :
  value t Γ2 := 
  close_value_app [] _ v := v;
  close_value_app (t0 :: Γ) (v0, ρ) v := close_value_app Γ ρ (subst_value_cons v (weaken_l_value Γ v0) ).
Arguments close_value_app {_ _ _}.
(* need more ways to apply a substitution*)


(* Γ1 ++ [] = Γ1 *)

Definition comp_app_nil {t MR Γ} (c : comp t (Γ ++ []) MR) : comp t Γ MR.
  rewrite List.app_nil_r in c. exact c.
Defined.


Equations close_comp_app {t MR Γ1} Γ2 (ρ : closing_subst Γ2) (c : comp t (Γ1 ++ Γ2) MR) : comp t Γ1 MR :=
  close_comp_app [] _ c := comp_app_nil c;
  close_comp_app (t0 :: Γ) (v, ρ) c := close_comp_app Γ ρ (subst_comp c (weaken_r_value _ v)).
Arguments close_comp_app {_ _ _ _}.


Equations close_bodies_app {MR R1 R2 Γ2} Γ1 (ρ : open_subst Γ1 Γ2) 
          (bodies : mfix_bodies (Γ1 ++ Γ2) MR R1 R2) :
  mfix_bodies Γ2 MR R1 R2 :=
  close_bodies_app [] _ bodies := bodies;
  close_bodies_app (t :: Γ) (v,ρ) bodies := 
    close_bodies_app Γ ρ (subst_bodies_cons bodies (weaken_l_value _ v)).
Arguments close_bodies_app {_ _ _ _ _}.


Equations close_value {t} Γ (vs : closing_subst Γ) (v : value t Γ)  : value t [] := 
  close_value [] _ v := v;
  close_value (t0 :: Γ1) (v0, vs) v := close_value _ vs (subst_value_cons v (weaken_r_value _ v0) ).

Equations close_comp {t MR} Γ (vs : closing_subst Γ) (c : comp t Γ MR) : comp t [] MR :=
  close_comp [] _ c := c;
  close_comp (t0 :: Γ1) (v0, vs) c := close_comp Γ1 vs (subst_comp_cons c (weaken_r_value Γ1 v0)).

Equations close_bodies {MR R1 R2} Γ (ρ : closing_subst Γ) (bodies : mfix_bodies Γ MR R1 R2) :
  mfix_bodies [] MR R1 R2 :=
  close_bodies [] _ bodies := bodies;
  close_bodies (t :: Γ) (v,ρ) bodies := close_bodies Γ ρ (subst_bodies_cons bodies (weaken_r_value Γ v)).

(* define stuck call, relate stuck call with *)
Inductive stuck_call : forall {t1 t2 MR} (c : comp t1 [] MR) (ca : call_syn t2 MR), eval_context t1 MR (inr ca) true -> Prop := 
  | stuck_call_let t1 t2 t3 MR (ca : call_syn t3 MR)  (c1 : comp t1 [] MR) E1 (c2 : comp t2 [t1] MR) (S : stuck_call c1 ca E1) : 
    stuck_call (comp_let c1 c2) ca (ev_let E1 c2)
  | stuck_call_call t1 t2 MR  R (xR : var R MR) (x : var (t1,t2) R) (v : closed_value t1) : 
    stuck_call (comp_call xR x v) (SmallStepSeq.callv xR x v) ev_hole
.
(* covered_in  *)
Lemma mfix_step_context MR1 MR2 R t1 t2 (ca : call_syn t2 MR2) b (E : eval_context t1 (R :: MR1) (inr ca) b) bodies : 
  exists c, step_eval_context _ _ (ev_mfix b R bodies E) = Some c.
Proof.
  apply covered_in_step.
  apply covered_in_intro.
Qed.
  
Lemma lift_step_context MR1 MR3 MR2 t1 t2 (ca : call_syn t2 MR2) b (E : eval_context t1 MR3 (inr ca) b) : 
  exists c, step_eval_context _ _ (ev_lift (MR1 := MR1) _ E) = Some c.
Proof.
  apply covered_in_step.
  apply covered_in_intro.
Qed.
  
Lemma perm_step_context MR1 MR3 (Hperm : perm MR1 MR3) MR2 t1 t2 (ca : call_syn t2 MR2) b (E : eval_context t1 MR1 (inr ca) b) : 
  exists c, step_eval_context _ _ (ev_perm _ Hperm E) = Some c.
Proof.
  apply covered_in_step.
  apply covered_in_intro.
Qed.

Lemma step_mfix t MR R (c : comp t [] (R :: MR)) bodies : exists c', step (comp_mfix R bodies c) = inl (Some c').
Proof.
  unfold step. simp observe. destruct (SmallStepSeq.observe c); simpl; try destruct b; try destruct r.
  - simp step_eval_context. eexists. eauto.
  - specialize mfix_step_context with (E := E) (bodies := bodies) as [c' Hc']. rewrite Hc'. eexists. eauto.
  - simp step_eval_context. eexists. eauto.
Qed.

Lemma step_lift t MR1 MR2 (c : comp t [] MR2) : exists c', step (comp_lift (MR1 := MR1) c) = inl (Some c').
Proof.
  unfold step. simp observe. destruct (SmallStepSeq.observe c); simpl; try destruct b; try destruct r.
  - simp step_eval_context. eexists. eauto.
  - specialize lift_step_context with (MR1 := MR1) (E := E) as [c1 Hc1]. rewrite Hc1.
    eexists. eauto.
  - simp step_eval_context. eexists. eauto.
Qed.

Lemma step_perm t MR1 MR2 (Hperm : perm MR1 MR2) (c : comp t [] MR1) : exists c', step (comp_perm Hperm c) = inl (Some c').
Proof.
  unfold step. simp observe. destruct (SmallStepSeq.observe c); simpl; try destruct b; try destruct r.
  - simp step_eval_context. eexists. eauto.
  - specialize perm_step_context with (Hperm := Hperm) (E := E) as [c1 Hc1]. rewrite Hc1.
    eexists. eauto.
  - simp step_eval_context. eexists. eauto.
Qed.

Lemma stuck_call_stuck t1 MR (c : comp t1 [] MR)  :
  step c = inl None ->
  (exists t2 (ca : call_syn t2 MR) (E : eval_context t1 MR (inr ca) true), stuck_call c ca E).
Proof.
  - unfold step. dependent induction c.
    + simp observe. intros. discriminate.
    + simp observe. intros. clear IHc2. specialize (IHc1 c1 eq_refl JMeq_refl).
      destruct (SmallStepSeq.observe c1); try destruct b.
      * destruct r; simp step_eval_context in H; try discriminate.
        destruct (step_eval_context b (inr c) E); simpl in H; try discriminate.
        specialize (IHc1 eq_refl) as [t2' [ca [E1 HE1]]].
        exists t2'. exists ca. exists (ev_let E1 c2). constructor. auto.
      *  simpl in H. injection H. intros. simp step_eval_context in H0. discriminate.
    + intros. dependent destruction vn; try inversion x. simp observe in H.
      simpl in H. injection H. intros. simp step_eval_context in H0. discriminate.
    + dependent destruction vn; try inversion x. simp observe. cbn.
      simp step_eval_context. simpl. intros. discriminate.
    + simp observe. simpl. intros. discriminate.
    + simp observe. simpl. intros. discriminate.
    + simp observe. simpl. intros. simp step_eval_context in H.
      discriminate.
    + intros. dependent destruction vf; try inversion x. simp observe in H.
      simpl in H. injection H. intros. simp step_eval_context in H0. discriminate.
    + simp observe. simp step_eval_context. intros.
      exists t2.
      exists (SmallStepSeq.callv xR x v).
      eexists. econstructor.
    + intros. exfalso. specialize step_mfix with (c := c) (bodies := bodies) as [c' Hc']. 
      setoid_rewrite Hc' in H. discriminate.
    + intros. specialize step_lift with (MR1 := MR1) (c := c) as [c' Hc']. setoid_rewrite Hc' in H.
      discriminate.
    + intros. specialize step_perm with (Hperm := Hperm) (c := c) as [c' Hc']. setoid_rewrite Hc' in H.
      discriminate.
Qed.

Lemma stuck_call_stuck' t1 MR c t2 (ca : call_syn t2 MR) (E : eval_context t1 MR (inr ca) true) :
  stuck_call c ca E -> step c = inl None.
Proof.
  intros Hstuck. dependent induction Hstuck.
  - unfold step. simp observe. unfold step in IHHstuck.
    destruct (SmallStepSeq.observe c1); try destruct b; try discriminate.
    destruct r; simp step_eval_context. simp step_eval_context in IHHstuck. cbn in IHHstuck. discriminate.
    cbn. injection IHHstuck. intros H. rewrite H. auto. 
  - unfold step. simp observe. simp step_eval_context. auto.
Qed.

Lemma stuck_call_denote t1 t2 MR (c : comp t1 [] MR) (ca : call_syn t2 MR) E : 
  stuck_call c ca E -> (denote_comp c tt) ≈ (vv <- denote_call ca;; denote_eval_context_cont (inr ca) E vv).
Proof.
  intros H. dependent induction H.
  - simp denote_comp. rewrite IHstuck_call. setoid_rewrite bind_bind. 
    eapply eqit_bind. reflexivity. intros. subst.
    simp denote_eval_context_cont. reflexivity.
  - unfold denote_call. simp denote_comp.
    setoid_rewrite bind_bind. eapply eqit_bind. reflexivity.
    intros. subst. rewrite <- bind_ret_r at 1.
    eapply eqit_bind. reflexivity. intros. subst. simp denote_eval_context_cont. reflexivity.
Qed.



Inductive eval_rel_stuck {t MR} : Rel (comp t [] MR) (closed_value t + comp t [] MR) :=
  | eval_rel_stuck_step c1 c2 cv :
    step_rel c1 c2 -> eval_rel_stuck c2 cv -> eval_rel_stuck  c1 cv
  | eval_rel_stuck_val c v : 
    step c = inr v -> eval_rel_stuck c (inl v)
  | eval_rel_stuck_stuck t' c ca E :
    stuck_call (t2 := t') c ca E -> eval_rel_stuck c (inr c)
.

Lemma eval_rel_stuck_eval_rel t MR (c : comp t [] MR) (v : value t []) :
  eval_rel_stuck c (inl v) -> eval_rel c v.
Proof.
  intros H. dependent induction H.
  - eapply eval_rel_step; eauto.
  - constructor. auto.
Qed.

(*
Inductive eval_rel_stuck_n {t MR} : nat -> (comp t [] MR) -> (closed_value t + comp t [] MR) -> Prop :=
  | eval_rel_stuck_n_val c v : 
    step c = inr v -> eval_rel_stuck_n 0 c (inl v)
  | eval_rel_stuck_n_stuck t' c ca E :
    stuck_call (t2 := t') c ca E -> eval_rel_stuck_n 0 c (inr c)
  | eval_rel_stuck_n_step c1 c2 cv n :
    step_rel c1 c2 -> eval_rel_stuck_n n c2 cv -> eval_rel_stuck_n 
.
*)
Definition close_comp_binder {t1 t2 MR Γ} (ρ : closing_subst Γ) (c : comp t2 (t1 :: Γ) MR) :
  comp t2 [t1] MR := close_comp_app (Γ1 := [t1]) ρ c.

Lemma close_value_abs: forall (t1 t2 : vtype) (Γ : ctx) (MR : mfix_ctx) (cbody : comp t2 (t1 :: Γ) MR)
    (ρ : closing_subst Γ), 
    close_value Γ ρ (val_abs cbody) = val_abs (close_comp_binder ρ cbody).
Proof.
  intros t1 t2 Γ MR cbody ρ. revert ρ. 
  induction Γ.
  - intros. simp close_value. unfold close_comp_binder. simp close_comp_app. unfold comp_app_nil.
    simpl. cbn. cbv. remember (List.app_nil_r [t1]) as e. clear Heqe. 
    dependent destruction e. auto.
  - intros [v ρ]. simp close_value.
Qed.

Lemma close_value_const Γ (ρ : closing_subst Γ) (n : nat) :
  close_value Γ ρ (val_const n) = val_const n.
Proof.
  induction Γ; simp close_value; auto.
  destruct ρ; simp close_value; auto.
Qed.


Lemma close_comp_let : forall (t1 t2 : vtype) (Γ : ctx) (MR : mfix_ctx)
                       (c1 : comp t1 Γ MR) (c2 : comp t2 (t1 :: Γ) MR)
                       (ρ : closing_subst Γ),
      close_comp Γ ρ (comp_let c1 c2) = comp_let (close_comp Γ ρ c1) (close_comp_binder ρ c2).
Proof.
  intros t1 t2 Γ MR c1 c2.
  induction Γ.
  - intros []. simp close_comp. unfold close_comp_binder. simp close_comp_app. unfold comp_app_nil.
    simpl. cbn. cbv. remember (List.app_nil_r [t1]) as e. clear Heqe. dependent destruction e. auto.
  - intros [v ρ]. simp close_comp. unfold subst_comp_cons at 1. simp subst_comp.
Qed.

(* issue with associativity here, uggh *)
(*
Definition comp_assoc {Γ1 Γ2 Γ3 t MR} (c : comp t (Γ1 ++ Γ2 ++ Γ3) MR) : comp t ((Γ1 ++ Γ2) ++ Γ3) MR.
Admitted.
*)
(* example mutind subst_correct_aux_prod*)
(* can try to prove this with an excessive amount of JMeq, I think trying that seems more promising than fixing the issue I was looking at  *)

Lemma close_comp_mfix : forall Γ t R MR (bodies : mfix_bodies Γ MR R R) (c : comp t Γ (R :: MR))
                          (ρ : closing_subst Γ),
    close_comp Γ ρ (comp_mfix R bodies c) =  comp_mfix R (close_bodies Γ ρ bodies) (close_comp Γ ρ c).
Proof.
  intros Γ. induction Γ; intros.
  - destruct ρ. simp close_comp. simp close_bodies. auto.
  - destruct ρ as [v ρ]. simp close_comp. simp close_bodies.
    unfold subst_comp_cons at 1. simp subst_comp.
Qed.

  
Lemma close_comp_open : forall Γ t1 t2 MR (c : comp t2 (t1 :: Γ) MR) (v : value t1 []) (ρ : closing_subst Γ),
    close_comp (t1 :: Γ) (v, ρ) c = subst_comp_cons (close_comp_binder ρ c) v.
Proof.
  intros Γ. induction Γ.
  - intros. simp close_comp. destruct ρ. unfold close_comp_binder. simp close_comp_app.
    unfold comp_app_nil. simpl. remember ((List.app_nil_r [t1])) as e. dependent destruction e. simpl.
    unfold weaken_r_value. rewrite val_map_id; auto. cbn. intros. inversion x0.
  - intros t1 t2 MR c v [v0 ρ]. simp close_comp. unfold close_comp_binder. simp close_comp_app. 
    setoid_rewrite <- IHΓ.
    simp close_comp. f_equal. rewrite subst_comp_cons_comm. auto.
Qed.

Lemma close_comp_open2 : forall Γ t1 t2 t3 MR (c : comp t3 (t1 :: t2 :: Γ) MR)
                           (v1 : value t1 []) (v2 : value t2 []) (ρ : closing_subst Γ),
    subst_comp_cons (subst_comp_cons (close_comp_app (Γ1 := [t1;t2]) ρ c) (weaken_l_value_single v1)) v2 =
      close_comp (t1 :: t2 :: Γ) (v1, (v2, ρ)) c.
Proof.
  intros Γ. induction Γ.
  - intros t1 t2 t3 MR c v1  v2 []. simp close_comp. simp close_comp_app. 
    unfold comp_app_nil. cbn. simpl eq_rect. remember ((List.app_nil_r [t1; t2])) as e.
    dependent destruction e. cbn. f_equal.
    + unfold weaken_l_value_single, weaken_l_value, weaken_r_value.
      f_equal. eapply val_map_dep_f_equal. auto. red. intros. inversion b.
    + unfold weaken_r_value. rewrite val_map_id. auto. intros. inversion x0.
  - intros t1 t2 t3 MR c v1 v2 [v3 ρ]. simp close_comp_app. setoid_rewrite IHΓ.
    setoid_rewrite close_comp_open. f_equal.  unfold close_comp_binder.
    simp close_comp_app. f_equal.
    destruct subst_comp_comm_mut_ind as [H _]. red in H. setoid_rewrite H; eauto.
Qed.


Lemma subst_comp_const_close:
  forall (t1 t2 : vtype) (Γ : ctx) (MR : mfix_ctx)
    (cbody : comp t2 (t1 :: Γ) MR) (ρ : closing_subst Γ) 
    (v : closed_value t1),
    subst_comp_cons (close_comp_binder ρ cbody) v =
      close_comp Γ ρ (subst_comp_cons cbody (weaken_r_value Γ v)).
Proof.
  intros t1 t2 Γ. revert t1 t2. induction Γ.
  - intros. simp close_comp. unfold weaken_r_value. unfold weaken_var_r. 
    unfold close_comp_binder. simp close_comp_app.
    unfold comp_app_nil. cbn. generalize ((List.app_nil_r [t1])). intros. cbn in e.
    dependent destruction e. cbn. rewrite val_map_id.
    auto. intros t x. inversion x.
  - intros t1 t2 MR cbody [v1 ρ] v2. simp close_comp. unfold close_comp_binder. simp close_comp_app.
    setoid_rewrite IHΓ. f_equal. rewrite subst_comp_cons_comm. auto.
Qed.

Lemma close_comp_comp_app t1 t2 MR Γ (vf : value (Arrow t1 MR t2) Γ) (varg : value t1 Γ)
      (ρ : closing_subst Γ) :
  close_comp Γ ρ (comp_app vf varg) = comp_app (close_value Γ ρ vf) (close_value Γ ρ varg).
Proof.
  generalize dependent ρ. induction Γ.
  - intros []. simp close_comp. simp close_value. auto.
  - intros [v ρ]. simp close_comp. unfold subst_comp_cons. simp subst_comp.
Qed.

Lemma close_comp_call t1 t2 Γ R MR (xR : var R MR) (x : var (t1,t2) R) 
      (v : value t1 Γ) (ρ : closing_subst Γ) :
  close_comp Γ ρ (comp_call xR x v) = comp_call xR x (close_value Γ ρ v).
Proof.
  generalize dependent ρ. induction Γ.
  - intros []. simp close_comp. simp close_value. auto.
  - intros [v0 ρ]. simp close_comp. simp close_value. unfold subst_comp_cons, subst_value_cons.
    simp subst_comp.
Qed.

Lemma close_comp_ret t Γ MR (v : value t Γ) (ρ : closing_subst Γ) : 
  close_comp Γ ρ (comp_ret (MR := MR) v) = comp_ret (close_value Γ ρ v).
Proof.
  generalize dependent Γ. intros Γ. induction Γ.
  - intros v []. simp close_comp. simp close_value. auto.
  - intros v [v0 ρ]. simp close_comp. simp close_value.
    unfold subst_comp_cons. simp subst_comp.
Qed.

Lemma close_comp_perm t Γ MR1 MR2 (Hperm : perm MR1 MR2)
      (c : comp t Γ MR1) (ρ : closing_subst Γ) :
  close_comp Γ ρ (comp_perm Hperm c) = comp_perm Hperm (close_comp Γ ρ c).
Proof.
  generalize dependent Γ. intros Γ. induction Γ.
  - intros c []. simp close_comp. auto.
  - intros c [v ρ]. simp close_comp. unfold subst_comp_cons.
    simp subst_comp.
Qed.

Lemma close_comp_lift t Γ MR1 MR2
      (c : comp t Γ MR2) (ρ : closing_subst Γ) : 
  close_comp Γ ρ (comp_lift (MR1 := MR1) c) = comp_lift (close_comp Γ ρ c).
Proof.
  generalize dependent Γ. intros Γ. induction Γ.
  - intros c []. simp close_comp. auto.
  - intros c [v ρ]. simp close_comp. unfold subst_comp_cons.
    simp subst_comp.
Qed.

Lemma close_comp_match_nat t Γ MR 
      (vn : value Nat Γ) (cZ : comp t Γ MR) (cS : comp t (Nat :: Γ) MR) 
      (ρ : closing_subst Γ):
  close_comp Γ ρ (comp_match_nat vn cZ cS) =
    comp_match_nat (close_value Γ ρ vn) (close_comp Γ ρ cZ) (close_comp_binder ρ cS).
Proof.
  generalize dependent Γ. intros Γ. induction Γ.
  - intros vn cZ cS []. simp close_comp. simp close_value.
    f_equal. unfold close_comp_binder. simp close_comp_app.
    unfold comp_app_nil. cbn. cbv.
    remember (List.app_nil_r [Nat]) as e. dependent destruction e. auto.
  - intros vn cZ cS [v ρ]. simp close_comp.
    unfold subst_comp_cons. simp subst_comp.
Qed.

Lemma close_comp_succ  Γ MR 
      (vn : value Nat Γ) (ρ : closing_subst Γ) :
  close_comp Γ ρ (comp_succ (MR := MR) vn) = comp_succ (close_value Γ ρ vn).
Proof.
  generalize dependent Γ. intros Γ. induction Γ.
  - intros vn []. simp close_comp. simp close_value. auto.
  - intros vn [v ρ]. simp close_comp. simp close_value.
    unfold subst_comp_cons. unfold subst_value_cons. simp subst_comp.
Qed.

Lemma close_comp_match_list t1 t2 Γ MR
      (vl : value (List t1) Γ) 
      (cnil : comp t2 Γ MR) (ccons : comp t2 (t1 :: List t1 :: Γ) MR)
      (ρ : closing_subst Γ) :
  close_comp Γ ρ (comp_match_list vl cnil ccons) =
    comp_match_list (close_value Γ ρ vl) (close_comp Γ ρ cnil) (close_comp_app ρ (Γ1 := [t1; List t1]) ccons).
Proof.
  generalize dependent Γ. intros Γ. induction Γ.
  - intros vl cnil ccons []. simp close_comp. simp close_comp_app.
    unfold comp_app_nil. cbn. cbv. remember (List.app_nil_r [t1; List t1]) as e.
    dependent destruction e. simp close_value. auto.
  - intros vl cnil ccons [v ρ]. simp close_comp. simp close_value.
    simp close_comp_app. unfold subst_comp_cons. unfold subst_value_cons.
    simp subst_comp.
Qed.

Lemma close_comp_match_sum t1 t2 t3 Γ MR
      (vs : value (Sum t1 t2) Γ)
      (cinl : comp t3 (t1 :: Γ) MR) (cinr : comp t3 (t2 :: Γ) MR) 
      (ρ : closing_subst Γ) : 
  close_comp Γ ρ (comp_match_sum vs cinl cinr) =
    comp_match_sum (close_value Γ ρ vs)
                   (close_comp_app ρ (Γ1 := [t1]) cinl)
                   (close_comp_app ρ (Γ1 := [t2]) cinr).
Proof.
  generalize dependent Γ. intros Γ. induction Γ.
  - intros. simp close_comp.
    destruct ρ. simp close_value.
    simp close_comp_app. unfold comp_app_nil.
    cbn. remember (List.app_nil_r [t1]) as e1.
    remember (List.app_nil_r [t2]) as e2. dependent destruction e1.
    dependent destruction e2. cbn. auto.
  - intros vs cinl cinr [v ρ].  simp close_comp.
    simp close_value. unfold subst_comp_cons. simp subst_comp.
Qed.

Lemma close_comp_split t1 t2 t3 Γ MR
      (vp : value (Pair t1 t2) Γ) (cs : comp t3 (t1 :: t2 :: Γ) MR)
      (ρ : closing_subst Γ) :
  close_comp Γ ρ (comp_split vp cs) = 
    comp_split (close_value Γ ρ vp) (close_comp_app ρ (Γ1 := [t1; t2]) cs).
Proof.
  generalize dependent Γ. intros Γ. induction Γ.
  - intros vp cs []. simp close_comp. simp close_comp_app.
    unfold comp_app_nil. cbn. cbv. remember (List.app_nil_r [t1; t2]) as e.
    dependent destruction e. simp close_value. auto.
  - intros vp cs [v ρ]. simp close_comp. simp close_value.
    simp close_comp_app. unfold subst_comp_cons. unfold subst_value_cons.
    simp subst_comp.
Qed.

Lemma close_value_nil t Γ (ρ : closing_subst Γ) :
  close_value Γ ρ (val_nil (t := t)) = val_nil.
Proof.
  revert ρ. induction Γ.
  - intros []. simp close_value. auto.
  - intros [v ρ]. simp close_value.
Qed.

Lemma close_value_cons t Γ (vh : value t Γ) (vt : value (List t) Γ) 
      (ρ : closing_subst Γ) :
  close_value Γ ρ (val_cons vh vt) = val_cons (close_value Γ ρ vh) (close_value Γ ρ vt).
Proof.
  revert ρ. induction Γ.
  - intros []. simp close_value. auto.
  - intros [v ρ]. simp close_value.
Qed.

Lemma close_value_pair t1 t2 Γ (v1 : value t1 Γ) (v2 : value t2 Γ)
      (ρ : closing_subst Γ) :
  close_value Γ ρ (val_pair v1 v2) = val_pair (close_value Γ ρ v1) (close_value Γ ρ v2).
Proof.
  revert ρ. induction Γ.
  - intros []. simp close_value. auto.
  - intros [v ρ]. simp close_value.
Qed.

Lemma close_value_inl t1 t2 Γ (v1 : value t1 Γ)
      (ρ : closing_subst Γ) :
  close_value Γ ρ (val_inl v1) = val_inl (t2 := t2) (close_value Γ ρ v1).
Proof.
  revert ρ. induction Γ.
  - intros []. simp close_value. auto.
  - intros [v ρ]. simp close_value.
Qed.

Lemma close_value_inr t1 t2 Γ (v2 : value t2 Γ)
      (ρ : closing_subst Γ) :
  close_value Γ ρ (val_inr v2) = val_inr (t1 := t1) (close_value Γ ρ v2).
Proof.
  revert ρ. induction Γ.
  - intros []. simp close_value. auto.
  - intros [v ρ]. simp close_value.
Qed.

Lemma close_bodies_mfix_nil Γ R MR (ρ : closing_subst Γ) :
  close_bodies Γ ρ (mfix_bodies_nil (MR := MR) (R := R)) = mfix_bodies_nil.
Proof.
  revert ρ. induction Γ.
  - intros []. simp close_bodies. auto.
  - intros [v ρ]. simp close_bodies.
Qed.

Lemma close_bodies_mfix_bodies_cons Γ MR t1 t2 R1 R2
      (cbody : comp t2 (t1 :: Γ) (R1 :: MR)) (bodies : mfix_bodies Γ MR R1 R2)
      (ρ : closing_subst Γ) : 
  close_bodies Γ ρ (mfix_bodies_cons cbody bodies) = 
    mfix_bodies_cons (close_comp_binder ρ cbody) (close_bodies Γ ρ bodies).
Proof.
  revert ρ. induction Γ.
  - intros []. simp close_bodies. unfold close_comp_binder. simp close_comp_app.
    unfold comp_app_nil. remember (List.app_nil_r [t1]) as e.
    dependent destruction e. auto.
  - intros [v ρ]. simp close_bodies.
Qed.
