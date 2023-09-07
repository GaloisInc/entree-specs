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


(*
Equations close_value {t Γ2} Γ1(vs : open_subst Γ1 Γ2) (v : value t (Γ1 ++ Γ2))  : value t Γ2 := 
  close_value [] _ v := v;
  close_value (t0 :: Γ1) (v0, vs) v := close_value Γ1 vs (subst_value_cons v (weaken_l_value Γ1 v0) ).

Equations close_comp {t MR Γ2} Γ1 (vs : open_subst Γ1 Γ2) (c : comp t (Γ1 ++ Γ2) MR) : comp t Γ2 MR :=
  close_comp [] _ c := c;
  close_comp (t0 :: Γ1) (v0, vs) c := close_comp Γ1 vs (subst_comp_cons c (weaken_l_value Γ1 v0)).

Equations close_bodies {MR R1 R2 Γ2} Γ1 (ρ : open_subst Γ1 Γ2) (bodies : mfix_bodies (Γ1 ++ Γ2) MR R1 R2) :
  mfix_bodies Γ2 MR R1 R2 :=
  close_bodies [] _ bodies := bodies;
  close_bodies (t :: Γ1) (v,ρ) bodies := close_bodies Γ1 ρ (subst_bodies_cons bodies (weaken_l_value Γ1 v)).
*)
(*
Inductive closing_subst_equiv : forall Γ, closing_subst Γ -> denote_ctx Γ -> Prop :=
  | closing_subst_equiv_nil : closing_subst_equiv [] tt tt 
  | closing_subst_equiv_cons t Γ (v : closed_value t) (vs : closing_subst Γ)
                             (vv : denote_type t) (hyps : denote_ctx Γ) :
    (forall MR, comp_equiv_rutt (MR := MR) (denote_value v tt) (ret vv)) ->
    closing_subst_equiv Γ vs hyps ->
    closing_subst_equiv (t :: Γ) (v,vs) (vv,hyps)
.

Lemma closing_subst_equiv_ctx_equiv Γ vs hyps :
  closing_subst_equiv Γ vs hyps -> ctx_equiv Γ hyps hyps.
Proof.
  revert vs hyps. induction Γ.
  intros. destruct hyps. constructor.
  intros [v vs] [vv hyps] H. dependent destruction H.
  apply IHΓ in H0. constructor; auto.
  simpl. specialize (H []). 
  assert (comp_equiv_rutt (MR := []) (ret vv) (ret vv)).
  { etransitivity; eauto. symmetry. auto. }
  apply rutt_inv_Ret in H1. auto.
Qed.

(*do I need these *)
Theorem close_value_correct t Γ MR (vs : closing_subst Γ) (hyps : denote_ctx Γ) (v : value t Γ) :
  closing_subst_equiv Γ vs hyps ->
  comp_equiv_rutt (MR := MR) (denote_value v hyps) (denote_value (close_value Γ vs v) tt).
Proof.
  revert hyps v vs MR. generalize dependent t.
  induction Γ.
  - setoid_rewrite close_value_equation_1. intros. apply types_equiv_value_refl. destruct hyps. 
    constructor.
  - intros t [vv hyps] v [v0 vs] MR Hsubst. simp close_value.
    dependent destruction Hsubst.
    rewrite <- IHΓ; eauto. apply closing_subst_equiv_ctx_equiv in Hsubst as Hhyps.
    rewrite <- subst_value_cons_correct1 with (hyps1 := hyps) (v := (weaken_r_value Γ v0)); eauto.
    eapply types_equiv_value_refl; auto.
    unfold weaken_r_value. setoid_rewrite val_map_correct with (hyps2 := hyps); auto.
Qed.

Theorem close_comp_correct t Γ MR (vs : closing_subst Γ) (hyps : denote_ctx Γ) (c : comp t Γ MR) :
  closing_subst_equiv Γ vs hyps ->
  comp_equiv_rutt (MR := MR) (denote_comp c hyps) (denote_comp (close_comp Γ vs c) tt).
Proof.
  revert hyps c vs. generalize dependent t.
  induction Γ.
  - setoid_rewrite close_comp_equation_1. intros ? [] ? ? ?. apply types_equiv_comp_refl.
    constructor.
  - intros t [vv hyps] c [v0 vs] Hsubst.
    simp close_comp. dependent destruction Hsubst.
    rewrite <- IHΓ; eauto. apply closing_subst_equiv_ctx_equiv in Hsubst as Hhyps.
    rewrite <- subst_correct1 with (hyps1 := hyps) (v := (weaken_r_value Γ v0)); eauto.
    eapply types_equiv_comp_refl; auto.
    setoid_rewrite val_map_correct with (hyps2 := hyps); auto.
Qed.
*)
(*
  with comp : vtype -> ctx -> mfix_ctx -> Type :=
    comp_ret : forall (t : vtype) (Γ : ctx) (MR : mfix_ctx),
               value t Γ -> comp t Γ MR
  | comp_let : forall (t1 t2 : vtype) (Γ : ctx)
                 (MR : mfix_ctx),
               comp t1 Γ MR ->
               comp t2 (t1 :: Γ) MR -> comp t2 Γ MR
  | comp_match_nat : forall (t : vtype) 
                       (Γ : ctx) (MR : mfix_ctx),
                     value Nat Γ ->
                     comp t Γ MR ->
                     comp t (Nat :: Γ) MR -> comp t Γ MR
  | comp_match_list : forall (t1 t2 : vtype) 
                        (Γ : ctx) (MR : mfix_ctx),
                      value (List t1) Γ ->
                      comp t2 Γ MR ->
                      comp t2 (t1 :: List t1 :: Γ) MR ->
                      comp t2 Γ MR
  | comp_split : forall (t1 t2 t3 : vtype) 
                   (Γ : ctx) (MR : mfix_ctx),
                 value (Pair t1 t2) Γ ->
                 comp t3 (t1 :: t2 :: Γ) MR -> comp t3 Γ MR
  | comp_app : forall (t1 t2 : vtype) (Γ : ctx)
                 (MR : mfix_ctx),
               value (Arrow t1 MR t2) Γ ->
               value t1 Γ -> comp t2 Γ MR
  | comp_call : forall (t1 t2 : vtype) 
                  (Γ : ctx) (MR : mfix_ctx)
                  (R : call_frame),
                var R MR ->
                var (t1, t2) R ->
                value t1 Γ -> comp t2 Γ MR
  | comp_mfix : forall (t : vtype) (Γ : ctx)
                  (MR : mfix_ctx) (R : call_frame),
                mfix_bodies Γ MR R R ->
                comp t Γ (R :: MR) -> comp t Γ MR
  | comp_lift : forall (t : vtype) (Γ : ctx)
                  (MR1 MR2 : mfix_ctx),
                comp t Γ MR2 -> comp t Γ (MR1 ++ MR2)
  | comp_perm : forall (t : vtype) (Γ : ctx)
                  (MR1 MR2 : mfix_ctx),
                perm MR1 MR2 ->
                comp t Γ MR1 -> comp t Γ MR2
*)

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

Lemma close_value_abs: forall (t1 t2 : vtype) (Γ : ctx) (MR : mfix_ctx) (cbody : comp t2 (t1 :: Γ) MR)
    (ρ : closing_subst Γ), 
    close_value Γ ρ (val_abs cbody) = val_abs (close_comp_app (Γ1 := [t1]) ρ cbody).
Proof.
  intros t1 t2 Γ MR cbody ρ. revert ρ. 
  induction Γ.
  - intros. simp close_value. simp close_comp_app. unfold comp_app_nil.
    simpl. cbn. cbv. remember (List.app_nil_r [t1]) as e. clear Heqe. 
    dependent destruction e. auto.
  - intros [v ρ]. simp close_value.
Qed.

Lemma close_comp_let : forall (t1 t2 : vtype) (Γ : ctx) (MR : mfix_ctx)
                       (c1 : comp t1 Γ MR) (c2 : comp t2 (t1 :: Γ) MR)
                       (ρ : closing_subst Γ),
      close_comp Γ ρ (comp_let c1 c2) = comp_let (close_comp Γ ρ c1) (close_comp_app (Γ1 := [t1]) ρ c2).
Proof.
  intros t1 t2 Γ MR c1 c2.
  induction Γ.
  - intros []. simp close_comp. simp close_comp_app. unfold comp_app_nil.
    simpl. cbn. cbv. remember (List.app_nil_r [t1]) as e. clear Heqe. dependent destruction e. auto.
  - intros [v ρ]. simp close_comp. unfold subst_comp_cons at 1. simp subst_comp.
Qed.

Lemma var_map_skip_id Γ (t : type) (f : forall t', var t' Γ -> var t' Γ) :
  (forall t' (x : var t' Γ), f _ x = x) ->
  forall t' (x : var t' (t :: Γ)), var_map_skip f _ x = x.
Proof.
  intros. dependent destruction x;
  simp var_map_skip; auto. rewrite H. auto.
Qed.

Lemma var_map_id_mutind  :
  (forall t Γ MR (c : comp t Γ MR) (f : forall t', var t' Γ -> var t' Γ), 
      (forall t' (x : var t' Γ), f _ x = x) ->
      comp_map c f = c) /\
  (forall t Γ (v : value t Γ) (f : forall t', var t' Γ -> var t' Γ), 
      (forall t' (x : var t' Γ), f _ x = x) -> val_map v f = v) /\
  (forall Γ MR R1 R2 (bodies : mfix_bodies Γ MR R1 R2) (f : forall t', var t' Γ -> var t' Γ), 
      (forall t' (x : var t' Γ), f _ x = x) -> 
      bodies_map bodies f = bodies

).
Proof.
  apply comp_value_mutind; intros; try simp comp_map; auto;
    try (rewrite H, H0; auto; fail);
    try (rewrite H; auto; fail).
  - rewrite H; auto. apply var_map_skip_id; auto.
  - rewrite H0, H; auto. apply var_map_skip_id; auto.
  - rewrite H, H0, H1; auto. apply var_map_skip_id; auto.
  - rewrite H, H0, H1; auto. repeat apply var_map_skip_id; auto.
  - rewrite H, H0; auto. repeat apply var_map_skip_id; auto.
  - rewrite H, H0; auto. apply var_map_skip_id; auto.
Qed.

Lemma val_map_id:  forall t Γ (v : value t Γ) (f : forall t', var t' Γ -> var t' Γ), 
      (forall t' (x : var t' Γ), f _ x = x) -> val_map v f = v.
Proof.
  specialize var_map_id_mutind. tauto.
Qed.

(* issue with associativity here, uggh *)
(*
Definition comp_assoc {Γ1 Γ2 Γ3 t MR} (c : comp t (Γ1 ++ Γ2 ++ Γ3) MR) : comp t ((Γ1 ++ Γ2) ++ Γ3) MR.
Admitted.

Lemma subst_comp_comm Γ1 Γ2 t1 t2 t3 MR (cbody : comp t3 (Γ1 ++ [t1] ++ [t2] ++ Γ2) MR)
      (v1 : closed_value t1) (v2 : closed_value t2) : 
  subst_comp (subst_comp cbody (weaken_r_value _ v1)) (weaken_r_value _ v2) =
    subst_comp (subst_comp (comp_assoc (Γ1 := Γ1) (Γ2 := [t1]) (Γ3 := [t2] ++ Γ2) cbody) (weaken_r_value _ v2)) (weaken_r_value _ v1).
*)
Lemma close_comp_open : forall Γ t1 t2 MR (c : comp t2 (t1 :: Γ) MR) (v : value t1 []) (ρ : closing_subst Γ),
    close_comp (t1 :: Γ) (v, ρ) c = subst_comp_cons (close_comp_app (Γ1 := [t1]) ρ c) v.
Proof.
  intros Γ. induction Γ.
  - intros. simp close_comp. destruct ρ. simp close_comp_app.
    unfold comp_app_nil. simpl. remember ((List.app_nil_r [t1])) as e. dependent destruction e. simpl.
    unfold weaken_r_value. rewrite val_map_id; auto. cbn. intros. inversion x0.
  - intros t1 t2 MR c v [v0 ρ]. simp close_comp. simp close_comp_app. rewrite <- IHΓ.
    simp close_comp. f_equal.
    (* the remaining goal is commutativity for subst_comp, probably need *)
Admitted.

(* ideally would have close_comp ρ c = subst_comp_con (close_comp_app ρ c)  but proving that may be difficult *)

(*
Lemma subst_comp_comm:
  forall (a : vtype) (Γ : ctx) (t1 t2 : vtype) (MR : mfix_ctx) (cbody : comp t2 (t1 :: a :: Γ) MR) (v1 : value a [])
    (v2 : closed_value t1),
    subst_comp (subst_comp cbody (weaken_r_value Γ v1)) (weaken_r_value Γ v2) =
      subst_comp (subst_comp cbody (weaken_r_value (a :: Γ) v2)) (weaken_r_value Γ v1).
Proof.
  intros a Γ t1 t2 MR cbody v1 v2.
*)
(* TODO: finish proof *)

(*
Lemma var_map_id (f : forall t', var )
comp_value_mutind
*)


(*
Lemma subst_comp_const_close:
  forall (t1 t2 : vtype) (Γ : ctx) (MR : mfix_ctx)
    (cbody : comp t2 (t1 :: Γ) MR) (ρ : closing_subst Γ) 
    (v : closed_value t1),
    subst_comp_cons (close_comp_app (Γ1 := [t1]) ρ cbody) v =
      close_comp Γ ρ (subst_comp_cons cbody (weaken_r_value Γ v)).
Proof.
  intros t1 t2 Γ. revert t1 t2. induction Γ.
  - intros. simp close_comp. unfold weaken_r_value. unfold weaken_var_r. simp close_comp_app.
    unfold comp_app_nil. cbn. generalize ((List.app_nil_r [t1])). intros. cbn in e.
    dependent destruction e. cbn. destruct var_map_id as [ _ [Hv _] ].
    rewrite Hv; auto. intros t x. inversion x.
Admitted.
*)


(*
Lemma subst_comm : 
  () /\
  () /\
  ()
*)



(*
  maybe useful to have a relational def of substitution,
  use that as an intermediate 

*)

Lemma subst_comp_cons_comm:
  forall (a : vtype) (Γ : ctx) (t1 t2 : vtype) (MR : mfix_ctx) (cbody : comp t2 (t1 :: a :: Γ) MR) (v1 : value a [])
    (v2 : closed_value t1),
    subst_comp_cons (subst_comp (Γ1 := [t1]) cbody (weaken_r_value Γ v1)) (weaken_r_value Γ v2) =
      subst_comp_cons (subst_comp_cons cbody (weaken_r_value (a :: Γ) v2)) (weaken_r_value Γ v1).
Proof.
  unfold subst_comp_cons.
  intros a Γ t1 t2 MR cbody v1 v2.
Admitted.

Lemma subst_comp_const_close:
  forall (t1 t2 : vtype) (Γ : ctx) (MR : mfix_ctx)
    (cbody : comp t2 (t1 :: Γ) MR) (ρ : closing_subst Γ) 
    (v : closed_value t1),
    subst_comp_cons (close_comp_app (Γ1 := [t1]) ρ cbody) v =
      close_comp Γ ρ (subst_comp_cons cbody (weaken_r_value Γ v)).
Proof.
  intros t1 t2 Γ. revert t1 t2. induction Γ.
  - intros. simp close_comp. unfold weaken_r_value. unfold weaken_var_r. simp close_comp_app.
    unfold comp_app_nil. cbn. generalize ((List.app_nil_r [t1])). intros. cbn in e.
    dependent destruction e. cbn. destruct var_map_id as [ _ [Hv _] ].
    rewrite Hv; auto. intros t x. inversion x.
  - intros t1 t2 MR cbody [v1 ρ] v2. simp close_comp. simp close_comp_app.
    rewrite IHΓ. f_equal. f_equal. rewrite subst_comp_cons_comm. auto.
Qed.
