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


Fixpoint closing_subst (Γ : ctx) : Type :=
  match Γ with
  | [] => unit
  | t :: Γ => (closed_value t * closing_subst Γ)%type 
  end.

Fixpoint open_subst (Γ1 Γ2 : ctx) : Type :=
  match Γ1 with
  | [] => unit
  | t :: Γ1 => (value t Γ2 * open_subst Γ1 Γ2)%type
  end.

Equations weaken_subst Γ1 {Γ2} (ρ : closing_subst Γ1) : open_subst Γ1 Γ2 :=
  weaken_subst nil tt := tt;
  weaken_subst (t :: Γ1) (v, ρ) := (weaken_r_value _ v, weaken_subst Γ1 ρ).

Equations close_value_app {t Γ2} Γ1 (ρ : open_subst Γ1 Γ2) (v : value t (Γ1 ++ Γ2))  :
  value t Γ2 := 
  close_value_app [] _ v := v;
  close_value_app (t0 :: Γ) (v0, ρ) v := close_value_app Γ ρ (subst_value_cons v (weaken_l_value _ v0) ).
Arguments close_value_app {_ _ _}.

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


Equations close_value {t} Γ (vs : closing_subst Γ) (v : value t Γ)  : closed_value t := 
  close_value [] _ v := v;
  close_value (t0 :: Γ) (v0, vs) v := close_value Γ vs (subst_value_cons v (weaken_r_value Γ v0) ).

Equations close_comp {t MR} Γ (vs : closing_subst Γ) (c : comp t Γ MR) : comp t [] MR :=
  close_comp [] _ c := c;
  close_comp (t0 :: Γ) (v0, vs) c := close_comp Γ vs (subst_comp_cons c (weaken_r_value Γ v0)).

Equations close_bodies {MR R1 R2} Γ (ρ : closing_subst Γ) (bodies : mfix_bodies Γ MR R1 R2) :
  mfix_bodies [] MR R1 R2 :=
  close_bodies [] _ bodies := bodies;
  close_bodies (t :: Γ) (v,ρ) bodies := close_bodies Γ ρ (subst_bodies_cons bodies (weaken_r_value Γ v)).

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




(*
Theorem adequacy_aux 
*)
Section hole.
Context (hole : forall A, A).
Arguments hole {A}.

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

(* tomorrow write the logical relation, and the fundamental theorem type,
   start proving the fundamental theorem and maybe prove the fundamental theorem implies adequacy
   also maybe rename this to adequacy logical relation or something like that 

   exactly what to induct on in what order I am not quite sure yet

   also write more in terms of inductives makes easier to read big complicated defs
 *)
(*
Inductive lift_rel  {t MR} (R : denote_type t -> closed_value t -> Prop) :
  mtree (denote_mfix_ctx MR) (denote_type t) -> (comp t [] MR) -> Prop := 
 | lift_rel_ret (vv : denote_type t)
 | lift_rel_stuck
.

do I need a logical relation for call events?
lets leave it out for now, introduce it if necessary,
the lift for this logical relation is quite complicated and I am not sure I need it
*)
(*
Definition lift_rel_ret {t MR} (R : denote_type t -> closed_value t -> Prop)
           (m : mtree (denote_mfix_ctx MR) (denote_type t)) (c : comp t [] MR) : Prop :=
  forall (vv : denote_type t), comp_equiv_rutt m (ret vv) -> exists v, eval_rel_stuck c (inl v) /\ R vv v.

Definition lift_rel_stuck {t MR} (R : denote_type t -> closed_value t -> Prop)
           (m : mtree (denote_mfix_ctx MR) (denote_type t)) (c : comp t [] MR) : Prop :=
  forall (tc : type) (ca : call_syn tc MR) k , 
      comp_equiv_rutt m (vv <- denote_call ca;; k vv) -> 
      exists (E : eval_context t MR (inr ca) true) (c' : comp t [] MR), 
        eval_rel_stuck c (inr c') /\ stuck_call c ca E.
*)
(*
Definition lift_rel {t MR} (R : forall t, denote_type t -> closed_value t -> Prop)
           (m : mtree (denote_mfix_ctx MR) (denote_type t)) (c : comp t [] MR) : Prop :=
    (forall (vv : denote_type t), comp_equiv_rutt m (ret vv) -> exists v, eval_rel_stuck c (inl v) /\ R t vv v ) /\
      (forall (tc : type) (ca : call_syn tc MR) k , 
          comp_equiv_rutt m (vv <- denote_call ca;; k vv) -> 
          exists (E : eval_context t MR (inr ca) true) (c' : comp t [] MR), 
            eval_rel_stuck c (inr c') /\ stuck_call c ca E /\
              (forall (vv : denote_type tc) (vc : closed_value tc), R tc vv vc ->
                 lift_rel R (k vv) (subst_eval_context E (comp_ret vc)))). 
*)
(*
Definition ctx_to_val {t1 t2 MR1 MR2 r b} (E : @eval_context t1 MR1 t2 MR2 r b) :
  closed_value (Arrow t2 MR1 t1) :=
   val_abs (subst_eval_context_ctx E (comp_ret (val_var VarZ))).
(* TODO show that this function preserves the denotational meaning of E*)

Definition lift_rel' {t MR} (R : forall t, denote_type t -> closed_value t -> Prop)
           (m : mtree (denote_mfix_ctx MR) (denote_type t)) (c : comp t [] MR) : Prop :=
    (forall (vv : denote_type t), comp_equiv_rutt m (ret vv) -> exists v, eval_rel_stuck c (inl v) /\ R t vv v ) /\
      (forall (tc : type) (ca : call_syn tc MR) k , 
          comp_equiv_rutt m (vv <- denote_call ca;; k vv) -> 
          exists (E : eval_context t MR (inr ca) true) (c' : comp t [] MR), 
            eval_rel_stuck c (inr c') /\ stuck_call c ca E /\
              R (Arrow tc MR t) (denote_eval_context_cont _ E) (ctx_to_val E)).
*)

(* get it well typed and then swap order
   could it possibly be 
 *)


Definition valid_denote {t} (vv : denote_type t) : Prop :=
  types_equiv t vv vv.

Inductive approx_comp {t MR} (j : nat) (R : nat -> forall t, denote_type t -> closed_value t -> Prop) :
           forall (m : mtree (denote_mfix_ctx MR) (denote_type t)) (c : comp t [] MR), Prop := 
  approx_comp_intro m c : (j > 0 ->
                                (forall (vv : denote_type t), comp_equiv_rutt m (ret vv) -> exists v, eval_rel_stuck c (inl v) /\ R (j - 1) t vv v) /\
                                (forall (tin tout : type) Rcall (xR : var Rcall MR) (x : var (tin, tout) Rcall) (vvcall : denote_type tin) k,
                                    comp_equiv_rutt m (vv <- call_term x xR vvcall;; k vv) ->
                                    exists (vcall : closed_value tin) (E : eval_context t MR (inr (SmallStepSeq.callv xR x vcall) ) true) (c' : comp t [] MR),
                                      R (j - 1) tin vvcall vcall /\ 
                                      eval_rel_stuck c (inr c') /\ stuck_call c' ((SmallStepSeq.callv xR x vcall)) E /\
                                        (forall j' (vvret : denote_type tout) (vret : closed_value tout), j' < j -> 
                                          R j' tout vvret vret ->
                                          approx_comp j' R (k vvret) (subst_eval_context E (comp_ret vret)))))

                                -> approx_comp j R m c.

(*
(* needs to be changed to exists some j' ... *)
Inductive approx_comp {t MR} (j : nat) (R : nat -> forall t, closed_value t -> denote_type t -> Prop) :
           forall (c : comp t [] MR) (m : mtree (denote_mfix_ctx MR) (denote_type t)), Prop := 
  approx_comp_intro c m : (forall j', 0 < j' < j ->
                                (* think carefully about forall vs exists here *)
                                (forall (vv : denote_type t), comp_equiv_rutt m (ret vv) -> exists v, eval_rel_stuck j' c (inl v) /\ R (j - j') t v vv) /\

                                (forall (tc : type) (ca : call_syn tc MR) k,
                                    comp_equiv_rutt m (vv <- denote_call ca;; k vv) ->
                                    exists (E : eval_context t MR (inr ca) true) (c' : comp t [] MR),
                                      eval_rel_stuck j' c (inr c') /\ stuck_call c' ca E /\
                                        (forall (vv : denote_type tc) (vc : closed_value tc), 
                                            forall j'', 0 < j'' < j - j' ->
                                          R (j - j' - j'') tc vc vv ->
                                          approx_comp (j - j' - j'') R (subst_eval_context E (comp_ret vc)) (k vv))))

                                -> approx_comp j R c m . *)
(*
(* consider making this more like the logical relations nick mentioned *)
Inductive approx_comp {t MR} : forall (n : nat) (R : forall t, closed_value t -> denote_type t -> Prop)
           (c : comp t [] MR) (m : mtree (denote_mfix_ctx MR) (denote_type t)), Prop :=
  | approx_comp_0 R m c : approx_comp 0 R c m
  | approx_comp_intro n R m c : n > 0 ->
    (forall (vv : denote_type t), comp_equiv_rutt m (ret vv) -> exists v, eval_rel_stuck c (inl v) /\ R t v vv) /\
      (forall (tc : type) (ca : call_syn tc MR) k , 
          comp_equiv_rutt m (vv <- denote_call ca;; k vv) -> 
          exists (E : eval_context t MR (inr ca) true) (c' : comp t [] MR), 
            eval_rel_stuck c (inr c') /\ stuck_call c ca E /\
              (* I wonder if we should be feeding smaller steps in these steps,
                 keep it this way for now and edit if necessary *)
              (forall (vv : denote_type tc) (vc : closed_value tc), R tc vc vv ->
                 approx_comp n R (subst_eval_context E (comp_ret vc)) (k vv))) 
    -> approx_comp n R c m.
*)
(* maybe a bit more complicated *)

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
  constructor. intros Hn'. specialize (H Hn').
  destruct H as [Hret Hstuck].
  split.
  - intros vv Hvv. apply Hret in Hvv. decompose record Hvv. eexists. split; eauto.
    apply HR; auto. eapply Hclosed. 2 : apply Hn. lia.
  - intros. apply Hstuck in H. destruct H as [vcall [E [c' [H1 [H2 [H3 H4]]]]]].
    exists vcall, E, c'.
    split; try split; try split; auto.
    + apply HR; auto. apply Hclosed with (n := n-1) (m := n); auto. lia.
    + intros j' vvret vret Hvret Hj'. destruct n; cbn. constructor. intros. lia.
      eapply IHn; eauto. 
      eapply H4. lia. eapply HR. eapply Hclosed; try apply Hn. lia. auto.
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
  dependent destruction Hcm. constructor. intros Hn.
  assert (Hn' : S (S n) > 0). lia.
  specialize (H Hn'). destruct H as [Hret Hstuck].
  split.
  - intros vv Hvv. eapply Hret in Hvv as [v [Hv1 Hv2]].
    eexists. split; eauto. eapply HR; try apply Hv2. lia.
  - intros tin tout Rcall xR x vvcall k Hca. apply Hstuck in Hca.
    destruct Hca as [vcall [E [c' [HE1 [HE2 [HE3 HE4]]]]]].
    exists vcall, E, c'. repeat (split; auto).
    eapply HR; try apply HE1. lia.
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

(*
Lemma lower_approx_comp_aux : forall n t MR c mc, 
                                approx_comp (t := t) (MR := MR) (S n) (approx_val (S n)) c mc ->
                                approx_comp n (approx_val n) c mc.
Proof.
  intros n. induction n; intros.
  - constructor.
  - inversion H. subst. destruct H1 as [Hret Hstuck]. constructor.
    admit. (* simpl arith *)
    split.
    + intros vv Hvv. apply Hret in Hvv as [v [Hv1 Hv2]]. eexists. split; eauto.
      apply lower_approx_val_aux. auto.
    + intros. apply Hstuck in H1.
      destruct H1 as [E [c' [Hc'1 [Hc'2 Hc'3] ] ]].
      eexists. eexists. split; eauto. split; eauto. intros. 
      apply IHn.
      apply Hc'3.
      apply
*)
(* may also need that vv is valid *)
Inductive closing_subst_approx (n : nat) : forall Γ, closing_subst Γ -> denote_ctx Γ -> Prop :=
  | closing_subst_approx_nil : closing_subst_approx n nil tt tt
  | closing_subst_approx_cons t Γ v ρ vv hyps : 
    approx_val n t v vv -> closing_subst_approx n Γ ρ hyps ->
    closing_subst_approx n (t :: Γ) (v, ρ) (vv, hyps)
.

Lemma lower_closing_subst_approx:
  forall (n m : nat) (Γ : ctx) (ρ : closing_subst Γ) (hyps : denote_ctx Γ),
    closing_subst_approx n Γ ρ hyps ->
    m < n -> closing_subst_approx m Γ ρ hyps.
Proof.
  intros n m Γ ρ hyps H Hm.
  generalize dependent Γ. intros Γ. induction Γ.
  intros. destruct ρ. destruct hyps. constructor.
  intros [v ρ] [vv hyps] H. dependent destruction H.
  constructor; auto. eapply lower_approx_val; eauto.
Qed.


Lemma proper_approx_aux : forall n,
    (forall t v vv1 vv2, types_equiv t vv1 vv2 -> approx_val n t v vv1 -> approx_val n t v vv2) /\
    (forall t MR c m1 m2, comp_equiv_rutt (t := t) (MR := MR) m1 m2 -> 
       approx_comp n approx_val c m1 -> approx_comp n approx_val c m2).
Proof.
  intros n. induction n as [ n IHn ] using (well_founded_induction lt_wf).
  assert (IHv : forall y, y < n -> 
           (forall (t : vtype) (v : closed_value t) (vv1 vv2 : denote_type t),
         types_equiv t vv1 vv2 -> approx_val y t v vv1 -> approx_val y t v vv2)).
  { intros. apply IHn in H. destruct H. eauto. }
  assert (IHc : forall y, y < n -> 
           (forall t MR c m1 m2, comp_equiv_rutt (t := t) (MR := MR) m1 m2 -> 
       approx_comp y approx_val c m1 -> approx_comp y approx_val c m2)).
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
  - destruct n. constructor. intros. lia. constructor. inversion H0. subst. intros j' Hj'. specialize (H1 j' Hj'). destruct H1 as [Hret Hstuck].
    split.
    + intros. rewrite <- H in H1. apply Hret in H1. auto.
    + intros. rewrite <- H in H1. apply Hstuck in H1. eauto.
Qed.

#[local] Instance proper_approx_val {n t} : Morphisms.Proper (eq ==> types_equiv t ==> Basics.flip Basics.impl) (approx_val n t).
Proof.
  repeat intro. subst. destruct (proper_approx_aux n). eapply H; eauto. symmetry. auto.
Qed.

#[local] Instance proper_approx_comp {n t MR} : Morphisms.Proper (eq ==> comp_equiv_rutt (t := t) (MR := MR)  ==> Basics.flip Basics.impl) (approx_comp n approx_val).
Proof.
  repeat intro. subst. destruct (proper_approx_aux n). eapply H2; eauto. symmetry. auto.
Qed.

(*
Definition log_rel t vv v : Prop := forall n, log_rel_step n t vv v.
*)




(* needs to include this new bodies steps t *)
Equations log_rel_bodies_step {MR R1 R2} 
          (n : nat)
          (dbodies : forall arg : denote_call_frame R2, mtree (denote_mfix_ctx (R1 :: MR)) (encodes arg))
          (bodies : mfix_bodies [] MR R1 R2) : Prop :=
  log_rel_bodies_step _ f mfix_bodies_nil := True;
  log_rel_bodies_step n f (mfix_bodies_cons cbody bodies) :=
   approx_val n (Arrow t1 (R1 :: MR) t2) (val_abs cbody) (fun vv => f (inl vv)) /\
      log_rel_bodies_step n (fun vv => f (inr vv)) bodies.

(*
comp_value_mutind:
  forall
    (P : forall (t : vtype) (l : ctx),
         value t l -> Prop)
    (P0 : forall (t : vtype) (l : ctx)
            (l0 : mfix_ctx), comp t l l0 -> Prop)
    (P1 : forall (l : ctx) (l0 : mfix_ctx)
            (l1 l2 : call_frame),
          mfix_bodies l l0 l1 l2 -> Prop)
*)
(* starting to think I should have given a stronger type to denote_value just returning a denotation not *)
(*
Equations weaken_subst_l {Γ2 : ctx} (Γ1 : ctx) (ρ : closing_subst Γ2) : 
  closing_subst (Γ1 ++ Γ2) :=
  weaken_subst_l [] ρ := ρ;
  weaken_subst_l
*)

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

(* TODO: finish proof *)
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
    dependent destruction e. cbn. admit. (* lemma about val_map of id *)
  - intros t1 t2 MR cbody [v1 ρ] v2. simp close_comp. simp close_comp_app.
    rewrite IHΓ. f_equal. f_equal. unfold subst_comp_cons.
    (* substitutions can happen in different orders, this could be annoying to prove  *)
    admit.
Admitted.

Theorem fundamental_theorem_adequacy :
  forall n,
  (forall (t : vtype) (Γ : ctx) (MR : mfix_ctx) (c : comp t Γ MR) (ρ : closing_subst Γ) (hyps : denote_ctx Γ), 
      closing_subst_approx n Γ ρ hyps -> approx_comp n approx_val (close_comp Γ ρ c) (denote_comp c hyps) 
  ) /\
  (forall (t : vtype) (Γ : ctx) (v : value t Γ) (ρ : closing_subst Γ) (hyps : denote_ctx Γ), 
      closing_subst_approx n Γ ρ hyps -> forall vv MR, comp_equiv_rutt (denote_value (MR := MR) v hyps) (ret vv) -> approx_val n t (close_value Γ ρ v) vv) /\
  (forall (Γ : ctx) (MR : mfix_ctx) (R1 R2 : call_frame) (bodies : mfix_bodies Γ MR R1 R2) (ρ : closing_subst Γ) (hyps : denote_ctx Γ), 
      closing_subst_approx n Γ ρ hyps -> 
      log_rel_bodies_step n (denote_bodies bodies hyps) (close_bodies Γ ρ bodies)).
Proof.
  intros n. induction n as [ n IHn ] using (well_founded_induction lt_wf).
  destruct n.
  {
    split. 2 : split.
    all : intros.
    - constructor. intros. lia.
    - simp approx_val. auto.
    - admit. (* this should hold, but the relation is in a very sketchy state right now,
                so don't bother*)
  }
  assert (IHnc : forall y, y < S n -> 
          (forall (t : vtype) (Γ : ctx) (MR : mfix_ctx) (c : comp t Γ MR) (ρ : closing_subst Γ)
           (hyps : denote_ctx Γ),
         closing_subst_approx y Γ ρ hyps ->
         approx_comp y approx_val (close_comp Γ ρ c) (denote_comp c hyps))).
  { intros m Hm. apply IHn in Hm. tauto. }
  assert (IHnv : forall y, y < S n -> 
         (forall (t : vtype) (Γ : ctx) (v : value t Γ) (ρ : closing_subst Γ) (hyps : denote_ctx Γ),
          closing_subst_approx y Γ ρ hyps ->
         forall (vv : denote_type t) (MR : mfix_ctx),
         comp_equiv_rutt (MR := MR) (denote_value v hyps) (ret vv) -> approx_val y t (close_value Γ ρ v) vv)).
  { intros m Hm. apply IHn in Hm. tauto. }
  assert (IHnbodies : forall y, y < S n -> 
         (forall (Γ : ctx) (MR : mfix_ctx) (R1 R2 : call_frame) (bodies : mfix_bodies Γ MR R1 R2)
           (ρ : closing_subst Γ) (hyps : denote_ctx Γ),
         closing_subst_approx y Γ ρ hyps ->
         log_rel_bodies_step y (denote_bodies bodies hyps) (close_bodies Γ ρ bodies))).
  { intros m Hm. apply IHn in Hm. tauto. }
  clear IHn.
  apply comp_value_mutind; intros; auto.
  - rewrite denote_value_equation_1 in H0. apply rutt_inv_Ret in H0.
    simp types_equiv in H0. subst.
    (* show that close_value (val_const) is val_const *) admit.
 - rewrite denote_value_equation_2 in H0. apply rutt_inv_Ret in H0.
   inversion H0. subst.
   (*show close_value val_nil is val_nil *) admit.
 - rewrite denote_value_equation_3 in H2. 
   admit.
 - rewrite denote_value_equation_4 in H2. destruct vv as [vv1 vv2].
   (* wts close_value commutes with val_pair *) admit.
 - rewrite denote_value_equation_5 in H1. apply rutt_inv_Ret in H1.
   rename vv into f.
   rewrite close_value_abs.
   (* there is another reasoning principle I need here *)
   simp approx_val. intros vv v m' Hm' Hvv Hv.
   apply lower_approx_comp_aux3; auto.  
   specialize (IHnc m' Hm').
   assert (subst_comp_cons (close_comp_app (Γ1 := [t1]) ρ cbody) v = close_comp (t1 :: Γ) (v,ρ) cbody ).
   rewrite subst_comp_const_close. simp close_comp. auto.
   rewrite H2.
   simp types_equiv in H1.   
   specialize (H1 vv vv Hvv).
   rewrite <- H1.
   eapply IHnc. constructor; auto.
   eapply lower_closing_subst_approx; eauto.
 - rewrite denote_value_equation_6 in H0.
   apply rutt_inv_Ret in H0.
   clear - H H0. dependent induction x.
   admit. admit.
   (* now this is starting to make sense, we can change H
      to direcly say that ρ approximates hyps at level S n,
      which along with the rewriting principle, will be enough 
    *)
 - rewrite denote_comp_equation_1. constructor.
   (*
   admit. (* simple arithmetic *)
   split.
   + intros. exists (close_value Γ ρ v). split.
     admit. (* reason about close comp and close_value *)
     eapply H; eauto.
   + intros. (* contradiction based on H1*) *) admit.
 - rewrite denote_comp_equation_2. apply H in H1 as Hc1.
   rename H0 into Hc2. inversion Hc1. subst. (* destruct H2 as [Hc11 Hc12].
   constructor. admit. split.
   + intros.
     assert (Hvv1 : exists vv1, comp_equiv_rutt (denote_comp c1 hyps) (ret vv1) ).
     admit.
     destruct Hvv1 as [vv1 Hvv1]. apply Hc11 in Hvv1 as Hvv1'.
     destruct Hvv1' as [v1 [Hv11 Hv12]]. clear Hc12.
     assert (Hρ :  closing_subst_approx (S n) (t1 :: Γ) (v1, ρ) (vv1, hyps)).
     constructor; auto.
     specialize (Hc2 (v1, ρ) (vv1, hyps) Hρ). inversion Hc2.
     subst. destruct H4 as [Hc21 Hc22]. clear Hc22.
     assert (Hvv2 : exists vv2, comp_equiv_rutt (denote_comp c2 (vv1,hyps)) (ret vv2)).
     admit.
     destruct Hvv2 as [vv2 Hvv2].
     apply Hc21 in Hvv2 as Hvv2'. destruct Hvv2' as [v2 [Hv21 Hv22] ].
     assert (types_equiv _ vv2 vv).
     (* from H2 and the equivalence to rets *) admit.
     exists v2.
     split.
     (* congruence rules I will need to make + Hvv1 and Hv11 Hv21 *)
     admit.
     (* rewrite acording to the types_equiv in H4 *)
     admit.
   + intros.
     (* will need itree rule that either denote_comp c1 as a vis, or 
        denote_comp c1 is a ret and denote_comp c2 is a vis
      *) admit.
 - rewrite denote_comp_equation_3. (*comp_match_nat and bind *)
   admit.
 - rewrite denote_comp_equation_4. (* comp_match_list and bind *)
   admit.
 - rewrite denote_comp_equation_5. (* comp_split and bind *)
   admit.
 - rewrite denote_comp_equation_6. constructor. admit. split.
   + intros.
     assert (Hf : exists f, comp_equiv_rutt (MR := MR) (denote_value vf hyps) (ret f)).
     admit.
     destruct Hf as [f Hf]. specialize (H _ _ H1 _ _ Hf).
     assert (Harg : exists arg, comp_equiv_rutt (MR := MR) (denote_value varg hyps) (ret arg)).
     admit.
     destruct Harg as [arg Harg].
     specialize (H0 _ _ H1 _ _ Harg).
     (* here is a situation where the amount of steps needs to decrease,
        rewrite the approx_comp
      *)
     simp approx_val in H.

   (* comp_app and bind *)
   admit.
 - rewrite denote_comp_equation_7. (* comp_call and bind *)
   admit.
 - rewrite denote_comp_equation_8. (* comp_mfix and interp_mrec *)
   apply H0 in H1 as Hc. inversion Hc. subst. destruct H3 as [Hc1 Hc2].
   apply H in H1 as Hbodies. 
   (* I think this is showing I have the wrong bodies logical relation,
      that idea I had that had something to do with bodies steps c
      either to a ret or to an inr, then we need extra reasoning to 
      bring the small step up to speed and the denotation
    *) admit.
 - rewrite denote_comp_equation_9. apply H in H0 as Hc.
   inversion Hc. subst. destruct H2 as [Hc1 Hc2].
   constructor. admit.
   split.
   + intros. 
     (* H1 can tell us everything about denote_comp c then we apply Hc1 to that info
        then we know how c steps
      *) admit.
   + intros.
     (* similar thing going on *) admit.
 - rewrite denote_comp_equation_10. apply H in H0 as Hc.
   inversion Hc. subst. destruct H2 as [Hc1 Hc2].
   (* morally similar to the previous *)
   admit.
 - (* these cases are too broken to bother with right now *) admit.
 - admit. *)
Admitted.

Lemma adequacy_aux : forall (c : comp Nat [] []) (n : nat),
    comp_equiv (denote_comp c) (denote_value (val_const n)) ->
    exists m, eval_rel c (val_const m).
Proof.
  destruct (fundamental_theorem_adequacy 2) as [Had _].
  intros c n Hc.
  specialize (Had Nat [] [] c tt tt (closing_subst_approx_nil 2)).
  inversion Had. clear Had. assert (Hj' : 0 < 1 < 2). lia.
  specialize (H 1 Hj'). destruct H as [Hret _]. subst.  
  red in Hc.
  specialize (Hc tt tt I). apply Hret in Hc as [v [Hv _]]. simp close_comp in Hv. 
  inversion Hv. subst.
  - inversion H1. subst.
    red in v. dependent destruction v; try inversion x.
    exists n0. eapply eval_rel_step; eauto. constructor. auto.
  - subst. red in v. dependent destruction v; try inversion x.
    exists n0. constructor. auto.
Qed.
(* this looks really weird, I proved that c must step in 1 step to n which is clearly wrong,
   which suggests that my logical relation is wrong, need to talk
 *)


Theorem adequacy : forall (c : comp Nat [] []) (n : nat),
    comp_equiv (denote_comp c) (denote_value (val_const n)) ->
    eval_rel c (val_const n).
Proof.
  intros c n Hcn. apply adequacy_aux in Hcn as Hm. destruct Hm as [m Hm].
  apply eval_stable in Hm as Hm'. specialize (Hcn tt tt I).
  rewrite Hcn in Hm'. setoid_rewrite denote_value_equation_1 in Hm'.
  apply rutt_inv_Ret in Hm'. simp types_equiv in Hm'. subst. auto.
Qed.


(*
Variant log_rel' : forall (t : type), denote_type t -> closed_value t -> Prop :=
  | log_rel_nat n m : n = m -> log_rel' Nat n (val_const m)
  | log_rel_pair t1 t2 vv1 vv2 v1 v2 : log_rel t1 vv1 v1 -> log_rel t2 vv2 v2 -> 
                                       log_rel' (Pair t1 t2) (vv1,vv2) (val_pair v1 v2)
  | log_rel_list' t l vl : log_rel_list (log_rel t) l vl ->
                          log_rel' (List t) l vl
  | log_rel_fun t1 MR t2 f c :
    (forall vv v, log_rel t1 vv v -> lift_rel log_rel (f vv) (subst_comp_cons c v)) ->
    log_rel' (Arrow t1 MR t2) f (val_abs c)
.

Lemma log_rel'_correct (t : type) (vv : denote_type t) (v : closed_value t) :
  log_rel t vv v <-> log_rel' t vv v.
Proof.
  split.
  - unfold log_rel. intros [n Ht]. revert Ht. generalize dependent t.
    induction n. intros; simp log_rel_gas in Ht; contradiction.
    (* might want strong induction *)
    intros t vv v. destruct t.
    + red in v. dependent destruction v; try inversion x. cbn in vv. simp log_rel_gas.
      intros. subst. constructor. auto.
    + simp log_rel_gas. intros Hlist. constructor. dependent induction Hlist.
      constructor; auto. constructor. exists n; auto. auto.
    + cbn in vv. destruct vv as [vv1 vv2]. red in v. dependent destruction v;
        try inversion x. simp log_rel_gas. intros [? ?]. constructor; eexists; eauto.
    + simpl in vv. rename vv into f. red in v.
      dependent destruction v; try inversion x. simp log_rel_gas.
      intros H. constructor.
      intros vv v Hvv. constructor. assert (Hn : log_rel_gas n t1 vv v). admit.
      apply H in Hn. inversion Hn. destruct H0.
      split.
      * intros. 
        apply H0 in H2.
        destruct H2 as [v0 [? ?]]. exists v0. split; eauto. exists n. auto.
      * intros. apply H1 in H2 as [E [c' [? [? ?]]]]. exists E. exists c'.
        repeat split; auto. 
        (* these flips in the order make this frustrating to deal with and I have not figured it
           out yet

might be wrong think about log_rel 1 (Arrow Nat Nat) (fun x => x + 1) (\ x. x)
         *)
        
        split; auto.
        red in Hn.
        (*here I need to show log_rel_gas*) admit.
      * admit.
 - *)
(* I feel like what I need to do now *)
(* does this deal properly will calls and handlers? 
   maybe the lift_rel needs another case? or some kind of post_condition 

rutt (called on things in the logical relation) (returns things in the logical relation )
  (types_equiv /\ (= vv) ) problem is that this does not force termination 


maybe something like equivalent to or steps to
( call i j v;; f) \/ ret 
because in the mfix case

I think every term either steps to a value or 
to an 


or maybe not?

*)


End hole.
