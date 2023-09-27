
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
Import MonadNotation.
Local Open Scope monad_scope.
Require Export SemanticsFactsSeq.
Require Export CallMrecFacts.

(*
Inductive bredex : vtype -> mfix_ctx -> Type :=
    bredex_let : forall (t1 t2 : vtype) (MR : mfix_ctx),
                 closed_value t1 -> comp t2 [t1] MR -> bredex t2 MR
  | bredex_app : forall (t1 t2 : vtype) (MR : mfix_ctx),
                 comp t2 [t1] MR -> closed_value t1 -> bredex t2 MR
  | bredex_match_nat : forall (t : vtype) (MR : mfix_ctx),
                       nat -> comp t [] MR -> comp t [Nat] MR -> bredex t MR
  | bredex_match_list : forall (t1 t2 : vtype) (MR : mfix_ctx),
                        closed_value (List t1) ->
                        comp t2 [] MR -> comp t2 [t1; List t1] MR -> bredex t2 MR
  | bredex_split : forall (t1 t2 t3 : vtype) (MR : mfix_ctx),
                   closed_value (Pair t1 t2) -> comp t3 [t1; t2] MR -> bredex t3 MR
  | bredex_mfix : forall (t : vtype) (MR : mfix_ctx) (R : call_frame),
                  mfix_bodies [] MR R R -> closed_value t -> bredex t MR
  | bredex_perm : forall (t : vtype) (MR1 MR2 : mfix_ctx),
                  perm MR1 MR2 -> closed_value t -> bredex t MR2
  | bredex_lift : forall (t : vtype) (MR1 MR2 : mfix_ctx), closed_value t -> bredex t (MR1 ++ MR2).
*)


Equations denote_bredex {t MR} (br : bredex t MR) : mtree (denote_mfix_ctx MR) (denote_type t) :=
  denote_bredex (bredex_let v c) := vv <- denote_value v tt;;
                                    denote_comp c (vv,tt);
  denote_bredex (bredex_app cbody v) := vv <- denote_value v tt;;
                                        denote_comp cbody (vv, tt);
  denote_bredex (bredex_match_nat n cZ cS) := match n with
                                              | 0 => denote_comp cZ tt
                                              | S m => denote_comp cS (m, tt) end;
  denote_bredex (bredex_succ n) := ret (S n);
  denote_bredex (bredex_match_list val_nil cnil _) := denote_comp cnil tt;
  denote_bredex (bredex_match_list (val_cons vh vt) _ ccons) :=
    vvh <- denote_value vh tt;;
    vvt <- denote_value vt tt;;
    denote_comp ccons (vvh, (vvt, tt) );
  denote_bredex (bredex_split (val_pair v1 v2) cs) :=
    vv1 <- denote_value v1 tt;;
    vv2 <- denote_value v2 tt;;
    denote_comp cs (vv1, (vv2, tt));
  denote_bredex (bredex_mfix R bodies v) :=
    interp_mrec (denote_bodies bodies tt) (denote_value (MR := R :: MR) v tt);
  denote_bredex (bredex_lift v) :=
    mapE (lift_handler _) (denote_value v tt);
  denote_bredex (bredex_perm Hperm v) :=
    map_perm _ _ (perm_denote Hperm) (denote_value v tt).

Lemma denote_value_eutt_rutt:
        forall (t1 : vtype) Γ (MR : mfix_ctx) (vl1 : value t1 Γ) (vvh : denote_type t1)
          (hyps1 hyps2 : denote_ctx Γ),
          ctx_equiv Γ hyps1 hyps2 ->
          (forall MR : mfix_ctx, denote_value (MR := MR) vl1 hyps1 ≈ ret vvh) ->
          comp_equiv_rutt (MR := MR) (denote_value vl1 hyps2) (ret vvh).
Proof.
  intros.
  red. rewrite <- H0. apply types_equiv_value_refl. symmetry. auto.
Qed.
  
Lemma comp_equiv_rutt_ret_types_equiv:
  forall (t1 : vtype) (MR : mfix_ctx) (vl1 : value t1 []) (vvh : denote_type t1),
    comp_equiv_rutt (MR := MR) (denote_value vl1 tt) (ret vvh) -> types_equiv t1 vvh vvh.
Proof.
  intros t1 MR vl1 vvh Hvvh.
  specialize (types_equiv_value_refl _ _ MR vl1) as Hvl1.
  specialize (Hvl1 tt tt I).
  assert (comp_equiv_rutt (MR := MR) (ret vvh) (ret vvh) ).
  rewrite <- Hvvh. auto.
  apply rutt_inv_Ret in H. auto.
Qed.

Theorem step_bredex_correct t MR (br : bredex t MR) :
  comp_equiv_rutt (denote_bredex br) (denote_comp (step_bredex br) tt).
Proof.
  dependent induction br; simp denote_bredex; simp step_bredex.
  - symmetry. apply subst_correct. constructor.
  - symmetry. apply subst_correct. constructor.
  - destruct n.
    + apply types_equiv_comp_refl. constructor.
    + symmetry. apply subst_correct0. constructor.
      intros. rewrite denote_value_equation_1. reflexivity.
  - simp denote_comp. apply rutt_Ret. simp types_equiv. auto.
  - red in vl. dependent destruction vl.
    + simp denote_bredex. simp step_bredex.
      apply types_equiv_comp_refl. constructor.
    + simp denote_bredex. simp step_bredex.
      specialize (denote_value_terminates _ _ vl1 tt) as [vvh Hvvh].
      red. rewrite Hvvh. setoid_rewrite bind_ret_l.
      specialize (denote_value_terminates _ _ vl2 tt) as [vvt Hvvt].
      rewrite Hvvt. setoid_rewrite bind_ret_l.
      eapply denote_value_eutt_rutt with (MR := MR) (hyps2 := tt) in Hvvh.
      2 : constructor.
      eapply denote_value_eutt_rutt with (MR := MR) (hyps2 := tt) in Hvvt.
      2 : constructor.
      erewrite subst_correct1 with (Γ := []) (hyps2 := tt); eauto. 2 :constructor.
      assert (types_equiv _ vvh vvh). eapply comp_equiv_rutt_ret_types_equiv; eauto.
      assert (types_equiv _ vvt vvt). eapply comp_equiv_rutt_ret_types_equiv; eauto.
      erewrite subst_correct1 with (Γ := [List t1]) (hyps2 := (vvt, tt) ) (vv := vvh).
      2 : repeat constructor; auto.
      eapply types_equiv_comp_refl. repeat constructor; auto.
      setoid_rewrite val_map_correct with (Γ2 := [List t1]) (hyps2 := (vvt, tt) ).
      simp var_map_weaken. repeat constructor; auto.
    + inversion x.
  - red in vp. dependent destruction vp.
    + simp denote_bredex. simp step_bredex.
      specialize (denote_value_terminates _ _ vp1 tt) as [vv1 Hvv1].
      red. rewrite Hvv1. setoid_rewrite bind_ret_l.
      specialize (denote_value_terminates _ _ vp2 tt) as [vv2 Hvv2].
      rewrite Hvv2. setoid_rewrite bind_ret_l.
      eapply denote_value_eutt_rutt with (MR := MR) (hyps2 := tt) in Hvv1.
      2 : constructor.
      eapply denote_value_eutt_rutt with (MR := MR) (hyps2 := tt) in Hvv2.
      2 : constructor.
      erewrite subst_correct1 with (Γ := []) (hyps2 := tt); eauto. 2 :constructor.
      assert (types_equiv _ vv1 vv1). eapply comp_equiv_rutt_ret_types_equiv; eauto.
      assert (types_equiv _ vv2 vv2). eapply comp_equiv_rutt_ret_types_equiv; eauto.
      erewrite subst_correct1 with (Γ := [t2]) (hyps2 := (vv2, tt) ) (vv := vv1).
      2 : repeat constructor; auto.
      eapply types_equiv_comp_refl. repeat constructor; auto.
      setoid_rewrite val_map_correct with (Γ2 := [t2]) (hyps2 := (vv2, tt) ).
      simp var_map_weaken. repeat constructor; auto.
    + inversion x.
  - simp denote_comp.
    specialize (denote_value_terminates _ _ v tt) as [vv Hvv].
    red. repeat rewrite Hvv.
    setoid_rewrite interp_mrec_ret.
    apply rutt_Ret. 
    eapply comp_equiv_rutt_ret_types_equiv; eapply denote_value_eutt_rutt; eauto.
    constructor.
  - simp denote_comp.
    specialize (denote_value_terminates _ _ v tt) as [vv Hvv].
    red. setoid_rewrite Hvv. setoid_rewrite mapE_ret.
    apply rutt_Ret. eapply comp_equiv_rutt_ret_types_equiv; eapply denote_value_eutt_rutt; eauto.
    constructor.
  - simp denote_comp.
    specialize (denote_value_terminates _ _ v tt) as [vv Hvv].
    red. setoid_rewrite Hvv. setoid_rewrite mapE_ret.
    apply rutt_Ret. eapply comp_equiv_rutt_ret_types_equiv; eapply denote_value_eutt_rutt; eauto.
    constructor.
    (* maybe find where these extra evars are coming from *)
    Unshelve. all : eauto.
Qed.

Definition denote_call {t MR} (ca : call_syn t MR) : mtree (denote_mfix_ctx MR) (denote_type t) :=
  let '(SmallStepSeq.callv xR x v) := ca in
  vv <- denote_value v tt;;
  call_term x xR vv.

Definition denote_bredex_call {t MR} (r : bredex t MR + call_syn t MR) :=
  match r with
  | inl br => denote_bredex br
  | inr ca => denote_call ca
  end.

Equations denote_eval_context {t1 t2 MR1 MR2 b} (r : bredex t2 MR2 + call_syn t2 MR2)
  (E : eval_context t1 MR1 r b) : mtree (denote_mfix_ctx MR1) (denote_type t1) :=
  denote_eval_context (inl br) (ev_hole) := denote_bredex br;
  denote_eval_context (inr ca) (ev_hole) := denote_call ca;
  denote_eval_context r (ev_let E cc) := 
    vv <- denote_eval_context r E;;
    denote_comp cc (vv,tt);
  denote_eval_context r (ev_mfix _ _ bodies E) :=
    interp_mrec (denote_bodies bodies tt) (denote_eval_context r E);
  denote_eval_context r (ev_perm _ Hperm E) :=
    map_perm _ _ (perm_denote Hperm) (denote_eval_context r E);
  denote_eval_context r (ev_lift _ E) :=
    mapE (lift_handler _) (denote_eval_context r E).

(* probably need more lemmas specifically about handlers lemma *)
Lemma denote_eval_context_subst_correct t1 t2 MR1 MR2 b (r : bredex t2 MR2 + call_syn t2 MR2)
      (E : eval_context t1 MR1 r b) (c : comp t2 [] MR2) :
  comp_equiv_rutt (denote_bredex_call r) (denote_comp c tt) ->
  comp_equiv_rutt (denote_eval_context r E) 
                  (denote_comp (subst_eval_context E c) tt).
Proof.
  revert c. dependent induction E.
  - destruct r as [br | ca].
    + simpl. simp denote_bredex.
    + simpl. simp denote_eval_context.
  - intros c' Hc'. simp subst_eval_context. simp denote_comp.
    destruct r; simp denote_eval_context;
    eapply rutt_bind; eauto; try eapply IHE; eauto.
    all : intros; eapply types_equiv_comp_refl; repeat constructor; auto.
  - intros c Hc. simp subst_eval_context; simp denote_comp;
      destruct r; simp denote_eval_context.
    + eapply interp_mrec_rutt with 
        (RPreInv := call_frame_pre_equiv R)
        (RPostInv := call_frame_post_equiv R); intros. eauto.
      eapply types_equiv_mfix_bodies_refl; auto.
      constructor.
      eapply rutt_mon; try apply IHE; eauto.
    + eapply interp_mrec_rutt with 
        (RPreInv := call_frame_pre_equiv R)
        (RPostInv := call_frame_post_equiv R); intros. eauto.
      eapply types_equiv_mfix_bodies_refl; auto.
      constructor.
      eapply rutt_mon; try apply IHE; eauto.
  - intros c Hc. simp subst_eval_context. simp denote_comp.
    destruct r; simp denote_eval_context; eapply mapE_rutt.
    + eapply rutt_mon. eapply mfix_pre_equiv_perm_handler.
      apply mfix_post_equiv_perm_handler. 2 : apply IHE; auto.
      intros. auto.
    + eapply rutt_mon. eapply mfix_pre_equiv_perm_handler.
      apply mfix_post_equiv_perm_handler. 2 : apply IHE; auto.
      intros. auto.
  - intros c Hc. simp subst_eval_context. simp denote_comp.
    destruct r; simp denote_eval_context; eapply mapE_rutt.
    + eapply rutt_mon. apply mfix_pre_equiv_lift_handler.
      apply mfix_post_equiv_lift_handler.
      2 : apply IHE; auto.
      intros; auto.
    + eapply rutt_mon. apply mfix_pre_equiv_lift_handler.
      apply mfix_post_equiv_lift_handler.
      2 : apply IHE; auto.
      intros; auto.
Qed.

Lemma normalize_eval_context_correct t1 t2 MR1 MR2 (ca : call_syn t2 MR2)
      (E : eval_context t1 MR1 (inr ca) true) :
  let '(ca' && E') := normalize_eval_context ca E in
  (denote_eval_context _ E) ≈ (denote_eval_context _ E').
Proof.
  dependent induction E.
  - simp normalize_eval_context. simp denote_eval_context. reflexivity.
  - simp normalize_eval_context. specialize (IHE ca E eq_refl eq_refl JMeq_refl).
    destruct (normalize_eval_context ca E).
    simp denote_eval_context. rewrite IHE. reflexivity.
Qed.

Equations denote_eval_context_cont {t1 t2 MR1 MR2} (r : bredex t2 MR2 + call_syn t2 MR2)
  (E : eval_context t1 MR1 r true) (vv : denote_type t2) : 
  mtree (denote_mfix_ctx MR1) (denote_type t1) :=
  denote_eval_context_cont _ ev_hole vv := ret vv;
  denote_eval_context_cont _ (ev_let E c) vv := 
    vv' <- denote_eval_context_cont _ E vv;;
    denote_comp c (vv', tt).

Lemma exposed_eval_context t1 t2 MR (ca : call_syn t2 MR)
      (E : eval_context t1  MR (inr ca) true) : 
  denote_eval_context _ E ≈ vv <- denote_call ca;; denote_eval_context_cont _ E vv.
Proof.
  dependent induction E.
  - simp denote_eval_context. simp denote_eval_context_cont.
    setoid_rewrite <- (bind_ret_r (denote_call ca)).
    setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
    eapply eqit_bind. reflexivity.
    intros. subst. simp denote_eval_context_cont. reflexivity.
  - simp denote_eval_context. setoid_rewrite IHE; eauto.
    setoid_rewrite bind_bind. eapply eqit_bind. reflexivity.
    intros. subst. simp denote_eval_context_cont.
    eapply eqit_bind. reflexivity. intros. subst. reflexivity.
Qed.
(*
Lemma exposed_eval_context_type_eq MR t1 t2 (r : bredex t2 MR + call_syn t2 MR)
      (E : eval_context t1 MR r true) : t1 = t2.
Proof.
  dependent induction E; auto.
  eapply IHE.
*)
Lemma subst_eval_context_denote MR t1 t2 (r : bredex t2 MR + call_syn t2 MR)
      (E : eval_context t1 MR r true) (c : comp t2 [] MR) :
  denote_comp (subst_eval_context E c) tt ≈ bind (denote_comp c tt) (denote_eval_context_cont r E).
Proof.
  revert c. dependent induction E.
  - intros. simp subst_eval_context. 
    rewrite <- bind_ret_r at 1. eapply eqit_bind. reflexivity.
    intros. subst. simp denote_eval_context_cont. reflexivity.
  - intros. simp subst_eval_context. simp denote_comp.
    setoid_rewrite IHE; eauto. setoid_rewrite bind_bind.
    eapply eqit_bind with (UU := eq). reflexivity. intros. subst.
    simp denote_eval_context_cont. reflexivity.
Qed.


Lemma interp_mrec_call_frame MR R1 R2 t1 t2
      (bodies : mfix_bodies [] MR R1 R2) (x : var (t1,t2) R2) (v : denote_type t1) :
  let '(d && g) := call_mrec_call_frame x v in
  Functor.fmap g (denote_bodies bodies tt d) ≈ (denote_comp (nth_body bodies x) (v, tt)).
Proof.
  dependent induction x.
  - simp call_mrec_call_frame. dependent destruction bodies.
    simp nth_body. simp denote_bodies. cbn. unfold id.
    unfold inout_encoded.
    eapply eqit_mon; try eapply bind_ret_r. all : intros H; intros; try inversion H; auto.
  - dependent destruction bodies.
    specialize (IHx t1 t2 bodies x eq_refl JMeq_refl v).
    simp call_mrec_call_frame.
    simp nth_body. destruct (call_mrec_call_frame x v).
    rewrite <- IHx. eapply eqit_bind with (UU := eq).
    setoid_rewrite denote_bodies_equation_3.
    reflexivity. intros. subst. reflexivity.
Qed.

Lemma interp_mrec_call_term:
    forall (MR : mfix_ctx) (R: call_frame) (t1 t2 : vtype)
           (bodies : mfix_bodies [] MR R R) (x : var (t1, t2) R)
           (u2 : denote_type t1),
      eqit eq true true
           (interp_mrec (denote_bodies bodies tt) (call_term x VarZ u2))
           (interp_mrec (denote_bodies bodies tt)
                        (denote_comp (nth_body bodies x) (u2, tt))).
Proof.
  intros MR R t1 t2 bodies x u2.
  unfold call_term. simp call_mrec.
  specialize interp_mrec_call_frame with (bodies := bodies) as Hbodies.
  specialize (Hbodies t1 t2 x u2). destruct (call_mrec_call_frame x u2).
  rewrite <- Hbodies. simpl Functor.fmap.
  setoid_rewrite interp_mrec_bind. setoid_rewrite interp_mrec_ret.
  eapply eqit_bind with (UU := eq).
  2 : intros; subst; reflexivity.
  setoid_rewrite interp_mrec_vis_inl. rewrite tau_eutt.
  setoid_rewrite bind_ret_r. reflexivity.
Qed.

Lemma interp_mrec_denote_call MR R S t1 t2 (bodies : mfix_bodies [] MR R R)
      (x : var (t1,t2) R) (v : closed_value t1) (k : denote_type t2 -> entree _ S) :
  interp_mrec (denote_bodies bodies tt)
              (vc <- denote_call (SmallStepSeq.callv VarZ x v);; k vc) ≈
  interp_mrec (denote_bodies bodies tt)
              (vv <- denote_value v tt;;
               vc <- denote_comp (nth_body bodies x) (vv,tt);;
               k vc).
Proof.
  setoid_rewrite interp_mrec_bind. simpl denote_call.
  setoid_rewrite interp_mrec_bind. setoid_rewrite bind_bind.
  eapply eqit_bind. reflexivity. intros. subst. 
  eapply eqit_bind with (UU := eq).
  2 : intros; subst; reflexivity.
  apply interp_mrec_call_term.
Qed.

Lemma types_equiv_denote_eval_context_cont_refl t1 t2 MR1 MR2 (r : bredex t2 MR2 + call_syn t2 MR2)
      (E : eval_context t1 MR1 r true) : 
  forall (vv1 vv2 : denote_type t2), types_equiv t2 vv1 vv2 ->
                                comp_equiv_rutt (denote_eval_context_cont r E vv1) 
                                                (denote_eval_context_cont r E vv2).
Proof.
  dependent induction E.
  - intros. simp denote_eval_context_cont. apply rutt_Ret. auto.
  - intros vv1 vv2 Hvv. specialize (IHE E eq_refl JMeq_refl vv1 vv2 Hvv).
    simp denote_eval_context_cont. eapply rutt_bind; eauto.
    intros. apply types_equiv_comp_refl. repeat constructor; auto.
Qed.

(*
push_eval_context :
forall {t1 t2 : vtype} {MR1 MR2 : mfix_ctx}
  (r : bredex t2 MR1 + call_syn t2 MR1),
eval_context t1 MR1 r true ->
(forall (t : vtype) (Γ : ctx), comp t Γ MR1 -> comp t Γ MR2) ->
comp t2 [] MR2 -> comp t1 [] MR2
*)

Equations eval_context_comp_cont {t1 t2 MR1} (r : bredex t2 MR1 + call_syn t2 MR1)
      (E : eval_context t1 MR1 r true) : comp t1 [t2] MR1 :=
  eval_context_comp_cont r ev_hole := comp_ret (val_var VarZ);
  eval_context_comp_cont r (ev_let E c) := 
    comp_let (eval_context_comp_cont r E) (weaken_r_comp [t3] c).

Definition fcomp_hom {MR1 MR2} (f : forall t Γ, comp t Γ MR1 -> comp t Γ MR2) : Prop :=
  (forall t Γ (v : value t Γ) (hyps : denote_ctx Γ), 
      denote_comp (f _ _ (comp_ret v)) hyps ≈ denote_value v hyps) /\
  (forall t1 t2 Γ (c1 : comp t1 Γ MR1) (c2 : comp t2 (t1 :: Γ) MR1 ) (hyps : denote_ctx Γ),
      denote_comp (f _ _ (comp_let c1 c2) ) hyps ≈ 
                  vc1 <- denote_comp (f _ _ c1) hyps;; denote_comp (f _ _ c2) (vc1, hyps)
 ).

Lemma push_eval_context_perm_correct t1 t2 MR1 MR2 
      (r : bredex t2 MR1 + call_syn t2 MR1)
      (E : eval_context t1 MR1 r true)
      (Hperm : perm MR1 MR2) (c : comp t2 [] MR2) :
  comp_equiv_rutt
     (denote_comp 
       (push_eval_context r E (comp_perm_map Hperm) c) tt) 
     (vc <- denote_comp c tt;; 
     map_perm _ _ (perm_denote Hperm)  (denote_eval_context_cont _ E vc)) .
Proof.
  generalize dependent MR2. dependent induction E.
  - intros. simp push_eval_context. red.
    setoid_rewrite <- bind_ret_r at 1.
    eapply rutt_bind. eapply types_equiv_comp_refl. constructor.
    intros. simp denote_eval_context_cont. setoid_rewrite mapE_ret.
    apply rutt_Ret; auto.
  - intros. simp push_eval_context. red.
    simp denote_comp. specialize (IHE r E eq_refl JMeq_refl eq_refl JMeq_refl MR2 Hperm c0).
    etransitivity. eapply rutt_bind with
      (k2 := fun v => denote_comp (comp_perm_map Hperm _ _ c) (v, tt) ); try eapply IHE.
    intros.
    apply types_equiv_comp_refl. repeat constructor; auto.
    setoid_rewrite bind_bind. eapply rutt_bind.
    apply types_equiv_comp_refl. repeat constructor; auto.
    intros. simp denote_eval_context_cont.
    setoid_rewrite mapE_bind; auto.
    2 : apply valid_perm_handler.
    eapply rutt_bind with (RR := types_equiv t1).
    eapply mapE_rutt. eapply rutt_mon; try apply mfix_pre_equiv_perm_handler;
      try apply mfix_post_equiv_perm_handler; eauto.
    apply types_equiv_denote_eval_context_cont_refl. auto.
    intros.
    unfold comp_perm_map. simp denote_comp.
    eapply mapE_rutt. eapply rutt_mon; try apply mfix_pre_equiv_perm_handler;
      try apply mfix_post_equiv_perm_handler; eauto.
    apply types_equiv_comp_refl. repeat constructor; auto.
Qed.

Lemma push_eval_context_lift_correct t1 t2 MR1 MR2 
      (r : bredex t2 MR2 + call_syn t2 MR2)
      (E : eval_context t1 MR2 r true)
      (c : comp t2 [] (MR1 ++ MR2)) :
  comp_equiv_rutt
     (denote_comp 
       (push_eval_context r E comp_lift_map c) tt) 
     (vc <- denote_comp c tt;; 
     mapE (lift_handler MR1)  (denote_eval_context_cont _ E vc)) .
Proof.
  generalize dependent MR1. dependent induction E.
  - intros. simp push_eval_context. red.
    setoid_rewrite <- bind_ret_r at 1. eapply rutt_bind.
    apply types_equiv_comp_refl. constructor.
    intros. simp denote_eval_context_cont. rewrite mapE_ret.
    apply rutt_Ret. auto.
  - intros. simp push_eval_context. red.
    simp denote_comp. specialize (IHE _ E eq_refl JMeq_refl eq_refl JMeq_refl _ c0).
    etransitivity. eapply rutt_bind with
      (k2 := fun v => denote_comp (comp_lift_map _ _ c) (v, tt) ); try eapply IHE.
    intros. apply types_equiv_comp_refl. repeat constructor; auto.
    setoid_rewrite bind_bind. eapply rutt_bind.
    eapply types_equiv_comp_refl. constructor. intros.
    simp denote_eval_context_cont. setoid_rewrite mapE_bind.
    2 : apply valid_lift_handler.
    eapply rutt_bind with (RR := types_equiv t1).
    eapply mapE_rutt. eapply rutt_mon; try apply mfix_pre_equiv_lift_handler;
      try apply mfix_post_equiv_lift_handler; eauto.
    apply types_equiv_denote_eval_context_cont_refl. auto.
    intros. unfold comp_lift_map. simp denote_comp.
    apply mapE_rutt. eapply rutt_mon;  try apply mfix_pre_equiv_lift_handler;
      try apply mfix_post_equiv_lift_handler; eauto.
    apply types_equiv_comp_refl. repeat constructor; auto.
Qed.

Lemma push_eval_context_mfix_correct t1 t2 R MR 
      (r : bredex t2 (R :: MR) + call_syn t2 (R :: MR))
      (E : eval_context t1 (R :: MR) r true)
      (bodies : mfix_bodies [] MR R R) (c : comp t2 [] (MR)) :
  comp_equiv_rutt
     (denote_comp 
       (push_eval_context r E (comp_mfix_map bodies) c) tt) 
     (vc <- denote_comp c tt;; 
     interp_mrec (denote_bodies bodies tt) (denote_eval_context_cont _ E vc)) .
Proof.
  revert c bodies. dependent induction E.
  - intros. simp push_eval_context. red.
    setoid_rewrite <- bind_ret_r at 1.
    eapply rutt_bind. apply types_equiv_comp_refl. constructor.
    intros.
    simp denote_eval_context_cont.
    setoid_rewrite interp_mrec_ret. apply rutt_Ret. auto.
  - specialize (IHE R MR r E eq_refl eq_refl JMeq_refl eq_refl JMeq_refl).
    intros c1 bodies. specialize (IHE c1 bodies).
    simp push_eval_context. simp denote_comp. red.
    etransitivity. 
    eapply rutt_bind with (k2 := fun v => denote_comp (comp_mfix_map bodies t2 [t1] c) (v, tt) ). eapply IHE.
    intros. apply types_equiv_comp_refl. repeat constructor; auto.
    setoid_rewrite bind_bind. eapply rutt_bind.
    eapply types_equiv_comp_refl. constructor.
    intros. simp denote_eval_context_cont.
    setoid_rewrite interp_mrec_bind.
    eapply rutt_bind with (RR := types_equiv t1).
    eapply interp_mrec_rutt with 
      (RPreInv := call_frame_pre_equiv _)
      (RPostInv := call_frame_post_equiv _); intros.
    eapply types_equiv_mfix_bodies_refl; auto. constructor.
    match goal with |- rutt _ _ _ ?t1 ?t2 =>
                      enough (comp_equiv_rutt t1 t2); auto end.
    eapply types_equiv_denote_eval_context_cont_refl; auto.
    intros r3 r4 ?. unfold comp_mfix_map.
    simp denote_comp.
    eapply interp_mrec_rutt with 
      (RPreInv := call_frame_pre_equiv _)
      (RPostInv := call_frame_post_equiv _); intros.
    + setoid_rewrite <- mfix_post_equiv_equation_2.
      unfold weaken_r_bodies. setoid_rewrite <- mfix_pre_equiv_equation_2.
      set (fun (t' : vtype) (c' : var t' []) => weaken_var_r [] [t1] t' c') as f.
      assert (tt = var_map_weaken _ f (r3,tt) ).
      simp var_map_weaken. auto.
      rewrite H2. eapply bodies_map_correct; auto.
      simp var_map_weaken. repeat constructor; auto.
      simpl. etransitivity; eauto. symmetry. auto.
    + match goal with |- rutt _ _ _ ?t1 ?t2 =>
                        enough (comp_equiv_rutt t1 t2); auto end.
      eapply types_equiv_comp_refl. repeat constructor; auto.
Qed.

Lemma comp_equiv_rutt_interp_mrec_value:
  forall (R : call_frame) (MR1 : mfix_ctx) (bodies : mfix_bodies [] MR1 R R) 
    (t0 : vtype) (v : closed_value t0),
    rutt (mfix_pre_equiv MR1) (mfix_post_equiv MR1) (types_equiv t0)
         (interp_mrec (denote_bodies bodies tt) (denote_value (MR := R :: MR1) v tt)) 
         (denote_value v tt).
Proof.
  intros R MR1 bodies t0 v.
  specialize denote_value_terminates with (v := v) (hyps := tt) as [vv Hvv].
  setoid_rewrite Hvv. setoid_rewrite interp_mrec_ret.
  apply rutt_Ret. eapply denote_value_ret_equiv; eauto.
  constructor.
  Unshelve. eauto.
Qed.

Lemma comp_equiv_rutt_mapE:
  forall MR1 MR2 h
    (t : vtype) (v : closed_value t),
    valid_handler h ->
    rutt (mfix_pre_equiv MR2) (mfix_post_equiv MR2) (types_equiv t)
         (mapE h (denote_value (MR := MR1) v tt)) (denote_value (MR := MR2) v tt).
Proof.
  intros. specialize denote_value_terminates with (v := v) (hyps := tt) as [vv Hvv].
  setoid_rewrite Hvv. setoid_rewrite mapE_ret.
  apply rutt_Ret. eapply denote_value_ret_equiv; eauto.
  constructor.
  Unshelve. eauto.
Qed.

Lemma interp_mrec_call_term_neq:
  forall (t2 : vtype) (R : call_frame) (MR1 : mfix_ctx) (bodies : mfix_bodies [] MR1 R R)
    (t0 : vtype) (R0 : call_frame) (xR : var R0 (R :: MR1)) (x : var (t0, t2) R0)
    (v0 : var_neq VarZ xR) (r1 r2 : denote_type t0),
    types_equiv t0 r1 r2 ->
    rutt (mfix_pre_equiv MR1) (mfix_post_equiv MR1) (types_equiv t2)
    (interp_mrec (denote_bodies bodies tt) (call_term x xR r1))
         (call_term x (remove_var R R0 (R :: MR1) VarZ xR v0) r2).
Proof.
  intros t2 R MR1 bodies t0 R0 xR x. intros Hneq.
  dependent induction Hneq. intros r1 r2 Hr12.
  unfold call_term. simp call_mrec. Transparent remove_var.
  simpl remove_var. Opaque remove_var.
  destruct (call_mrec x x0 r1) eqn: Heq1.
  match goal with |- rutt _ _ _ _ (let '(d0 && f) := ?x in _) => destruct x eqn : Heq2 end.
  simpl. 
  Transparent remove. simpl remove in *. cbn in x2. Opaque remove.
  setoid_rewrite interp_mrec_bind. setoid_rewrite interp_mrec_ret.
  eapply rutt_bind with (RR := mfix_post_equiv MR1 x1 x2).
  + setoid_rewrite interp_mrec_vis_inr. eapply rutt_Vis.
    * eapply mfix_pre_call_mrec; eauto.
    * intros. setoid_rewrite interp_mrec_ret. apply rutt_Ret. auto.
  + intros. apply rutt_Ret. eapply mfix_post_equiv_types_equiv; eauto.
Qed.

Lemma step_eval_context_correct_mfix_aux:
  forall (b : bool) (t1 t2 : vtype) (R : call_frame) 
    (MR1 MR2 : mfix_ctx) (c : call_syn t2 MR2)
    (bodies : mfix_bodies [] MR1 R R)
    (E : eval_context t1 (R :: MR1) (inr c) b) (c' : comp t1 [] MR1),
    (forall c0 : comp t1 [] (R :: MR1),
        step_eval_context b (inr c) E = Some c0 ->
        comp_equiv_rutt (denote_eval_context (inr c) E) (denote_comp c0 tt)) ->
    step_eval_context false (inr c) (ev_mfix b R bodies E) = Some c' ->
    comp_equiv_rutt (denote_eval_context (inr c) (ev_mfix b R bodies E))
                    (denote_comp c' tt).
Proof.
  intros b t1 t2 R MR1 MR2 c bodies E c' IHE Hc'.
  destruct b; simp step_eval_context in Hc'.
  - specialize normalize_eval_context_correct with (E := E) as Hnorm.
    destruct (normalize_eval_context c E) as [ca' E'].
    destruct ca'. injection Hc'. intros. subst. clear Hc'.
    destruct (var_eq_neq R R0 (R :: MR1) VarZ xR).
    + specialize exposed_eval_context with (E := E') as HE'.
      rewrite HE' in Hnorm. simp denote_eval_context.
      red. rewrite Hnorm. simp denote_comp.
      apply var_eq_surj in v0 as Heq. subst.
      apply var_eq_eq in v0 as Heq. subst.
      dependent destruction v0. simp var_eq_elim.
      rewrite interp_mrec_denote_call.
      setoid_rewrite subst_eval_context_denote.
      eapply interp_mrec_rutt with 
        (RPreInv := call_frame_pre_equiv _)
        (RPostInv := call_frame_post_equiv _); intros. eauto.
      eapply types_equiv_mfix_bodies_refl; auto. constructor.
      setoid_rewrite <- bind_bind. eapply rutt_bind with (RR := types_equiv t2).
      * match goal with |- rutt _ _ _ ?t1 ?t2 => enough (comp_equiv_rutt t1 t2) end; auto.
        setoid_rewrite subst_correct with (Γ := []) (hyps2 := tt).
        2 : constructor. eapply rutt_bind. apply types_equiv_value_refl. constructor.
        intros. apply types_equiv_comp_refl. repeat constructor; auto.
      * intros. 
        eapply rutt_mon with (RPre1 := mfix_pre_equiv (R0 :: MR1) ) (RPost1 := mfix_post_equiv (R0 :: MR1)); intros; eauto.
        apply types_equiv_denote_eval_context_cont_refl; auto.
    + simp denote_eval_context. rewrite push_eval_context_mfix_correct.
      red. setoid_rewrite Hnorm. setoid_rewrite exposed_eval_context.
      setoid_rewrite interp_mrec_bind. eapply rutt_bind with (RR := types_equiv t2).
      * unfold denote_call. simp denote_comp. 
        eapply rutt_Proper_R2; try rewrite interp_mrec_bind; try reflexivity.
        (* not sure why rewrite failed here *)
        eapply rutt_bind with (RR := types_equiv t0).
        apply comp_equiv_rutt_interp_mrec_value.
        eapply interp_mrec_call_term_neq; eauto.
      * intros. eapply interp_mrec_rutt with 
          (RPreInv := call_frame_pre_equiv _)
          (RPostInv := call_frame_post_equiv _); intros.
        eapply types_equiv_mfix_bodies_refl. constructor. auto.
        setoid_rewrite <- mfix_post_equiv_equation_2.
        setoid_rewrite <- mfix_pre_equiv_equation_2.
        apply types_equiv_denote_eval_context_cont_refl with (E := E') (vv1 := r1) (vv2 := r2).
        auto.
  - simpl in Hc'. simp step_eval_context in Hc'.
    destruct (step_eval_context false (inr c) E) eqn : Heq1; try discriminate.
    injection Hc'. intros. subst. clear Hc'.
    specialize (IHE c0 eq_refl).
    simp denote_eval_context. simp denote_comp.
    eapply interp_mrec_rutt with 
      (RPreInv := call_frame_pre_equiv R)
      (RPostInv := call_frame_post_equiv R); intros. eauto.
    eapply types_equiv_mfix_bodies_refl; auto. constructor.
    eapply rutt_mon; eauto.
Qed.


Lemma step_eval_context_correct t1 t2 MR1 MR2 b (r : bredex t2 MR2 + call_syn t2 MR2) (E : eval_context t1 MR1 r b) :
  forall c, step_eval_context b r E = Some c ->
       comp_equiv_rutt (denote_eval_context r E) (denote_comp c tt).
Proof.
  dependent induction E; intros c'.
  - destruct r; simp step_eval_context; intros; try discriminate.
    injection H. intros. subst. simp denote_eval_context.
    simp subst_eval_context. apply step_bredex_correct.
  - destruct r; simp step_eval_context.
    + intros Hc'. injection Hc'. intros. subst.
      simp denote_eval_context. simp subst_eval_context.
      simp denote_comp. eapply rutt_bind.
      eapply denote_eval_context_subst_correct.
      simpl. apply step_bredex_correct.
      intros vv1 vv2 Hvv.
      apply types_equiv_comp_refl. repeat constructor; auto.
    + intros Hc'.
      destruct (step_eval_context b (inr c0) E) eqn : Heq; try discriminate.
      simpl in Hc'. injection Hc'. intros. subst.
      specialize (IHE c1 eq_refl).
      simp denote_eval_context. simp denote_comp.
      eapply rutt_bind; eauto. intros.
      eapply types_equiv_comp_refl. repeat constructor; auto.
  - destruct r; simp step_eval_context.
    + intros Hc'. injection Hc'. intros. subst. simp denote_eval_context.
      simp subst_eval_context. simp denote_comp.
      eapply interp_mrec_rutt with 
        (RPreInv := call_frame_pre_equiv R)
        (RPostInv := call_frame_post_equiv R); intros. eauto.
      * eapply types_equiv_mfix_bodies_refl; auto. constructor.
      * specialize (IHE ((subst_eval_context E (step_bredex b0)))).
        simp step_eval_context in IHE. specialize (IHE eq_refl).
        eapply rutt_mon; eauto.
    + eapply step_eval_context_correct_mfix_aux; eauto.
  - destruct r; simp step_eval_context.
    + intros Hc'. injection Hc'. intros. subst. simp denote_eval_context.
      simp subst_eval_context.
      simp denote_comp. eapply mapE_rutt.
      eapply rutt_mon; try eapply IHE; eauto.
      apply mfix_pre_equiv_perm_handler.
      apply mfix_post_equiv_perm_handler.
      simp step_eval_context. auto.
    + destruct b; simp step_eval_context.
      * intros Hc'.
        destruct ( normalize_eval_context c E) eqn : Heq1. destruct x.
        injection Hc'. intros. subst. clear Hc'.
        simp push_eval_context. simp denote_eval_context.
        rewrite push_eval_context_perm_correct.
        rename e into E'. red.
        specialize  normalize_eval_context_correct with (E := E) as HE'.
        rewrite Heq1 in HE'. rewrite HE'.
        rewrite exposed_eval_context. setoid_rewrite mapE_bind.
        2 : apply valid_perm_handler. eapply rutt_bind with (RR := types_equiv t2).
        -- unfold denote_call. simp denote_comp. setoid_rewrite mapE_bind;
             try apply valid_perm_handler.
           eapply rutt_bind with (RR := types_equiv _).
           eapply comp_equiv_rutt_mapE; try apply valid_perm_handler.
           apply mapE_perm_handler_call_term.
        -- intros. eapply mapE_rutt.
           eapply rutt_mon; try eapply types_equiv_denote_eval_context_cont_refl; eauto.
           apply mfix_pre_equiv_perm_handler. apply mfix_post_equiv_perm_handler.
      * intros Hc'. destruct (step_eval_context false (inr c) E) eqn : Heq1; try discriminate.
        specialize (IHE c0 eq_refl). simp denote_eval_context.
        simpl in Hc'. injection Hc'. intros. subst. simp denote_comp.
        eapply mapE_rutt. eapply rutt_mon; try eapply IHE; auto.
        apply mfix_pre_equiv_perm_handler.
        apply mfix_post_equiv_perm_handler.
  - destruct r; simp step_eval_context.
    + intros Hc'. injection Hc'; intros; subst. simp denote_eval_context.
      simp subst_eval_context. simp denote_comp.
      eapply mapE_rutt. eapply rutt_mon; try eapply IHE; eauto.
      apply mfix_pre_equiv_lift_handler.
      apply mfix_post_equiv_lift_handler.
      simp step_eval_context. auto.
    + destruct b; simp step_eval_context.
      * intros Hc'.
        destruct ( normalize_eval_context c E) eqn : Heq1. destruct x.
        injection Hc'. intros. subst. clear Hc'.
        simp push_eval_context. simp denote_eval_context.
        rewrite push_eval_context_lift_correct.
        rename e into E'. red.
        specialize  normalize_eval_context_correct with (E := E) as HE'.
        rewrite Heq1 in HE'. rewrite HE'.
        rewrite exposed_eval_context. setoid_rewrite mapE_bind.
        2 : apply valid_lift_handler. eapply rutt_bind with (RR := types_equiv t2).
        -- unfold denote_call. simp denote_comp. setoid_rewrite mapE_bind;
             try apply valid_lift_handler.
           eapply rutt_bind with (RR := types_equiv _).
           eapply comp_equiv_rutt_mapE. apply valid_lift_handler.
           apply mapE_lift_handler_call_term.
        -- intros. eapply mapE_rutt.
           eapply rutt_mon; try eapply types_equiv_denote_eval_context_cont_refl; eauto.
           apply mfix_pre_equiv_lift_handler. apply mfix_post_equiv_lift_handler.
      * intros Hc'. destruct (step_eval_context false (inr c) E) eqn : Heq1; try discriminate.
        specialize (IHE c0 eq_refl). simp denote_eval_context.
        simpl in Hc'. injection Hc'. intros. subst. simp denote_comp.
        eapply mapE_rutt. eapply rutt_mon; try eapply IHE; auto.
        apply mfix_pre_equiv_lift_handler.
        apply mfix_post_equiv_lift_handler.
Qed.

Definition denote_bec {t MR} (bec : boxed_eval_context t MR) : 
  mtree (denote_mfix_ctx MR) (denote_type t) :=
  let '(bec r E) := bec in
  denote_eval_context r E.

Definition denote_observed {t MR} (o : boxed_eval_context t MR + closed_value t) 
  : mtree (denote_mfix_ctx MR) (denote_type t) :=
  match o with
  | inl b => denote_bec b
  | inr v => denote_value v tt 
  end.


Lemma denote_observe_correct t MR (c : comp t [] MR) :
  comp_equiv_rutt (denote_comp c tt) (denote_observed (SmallStepSeq.observe c)).
Proof.
  dependent induction c.
  - simp denote_comp. simp observe. simpl.
    apply types_equiv_value_refl. constructor.
  - simp denote_comp. simp observe.
    specialize (IHc1 c1 eq_refl JMeq_refl).
    destruct (SmallStepSeq.observe c1) eqn : Hc1.
    + destruct b.
      destruct r; simpl in *; simp denote_eval_context;
      eapply rutt_bind; eauto; intros; eapply types_equiv_comp_refl; repeat constructor; auto.
    + simpl in *. simp denote_eval_context. simp denote_bredex.
      eapply rutt_bind; eauto; intros; eapply types_equiv_comp_refl; repeat constructor; auto.
  - (* expect to break if/when add succ *)
    dependent destruction vn; try inversion x. 
    simp denote_comp. simp observe. simpl denote_observed.
    simp denote_eval_context. simp denote_bredex. 
    red. setoid_rewrite bind_ret_l. 
    destruct n; try eapply types_equiv_comp_refl; repeat constructor; auto.
  - simp denote_comp. dependent destruction vn; try inversion x.
    simp observe. simpl. simp denote_eval_context. simp denote_bredex. red. rewrite bind_ret_l.
    simp types_equiv. apply rutt_Ret. auto.
  - dependent destruction vl; try inversion x.
    + simp denote_comp. simp observe. simpl denote_observed.
      simp denote_eval_context. simp denote_bredex. red.
      setoid_rewrite bind_ret_l. eapply types_equiv_comp_refl; constructor.
    + simp denote_comp. simp observe. simpl denote_observed.
      simp denote_eval_context. simp denote_bredex. red.
      setoid_rewrite bind_bind. 
      eapply rutt_bind. eapply types_equiv_value_refl. constructor.
      intros. simpl. setoid_rewrite bind_bind. 
      eapply rutt_bind with (RR := types_equiv (List t1)). 
      eapply types_equiv_value_refl. constructor.
      intros. setoid_rewrite bind_ret_l.
      eapply types_equiv_comp_refl; repeat constructor; auto.
  - simp denote_comp. simp observe. simpl denote_observed.
    simp denote_eval_context.
    dependent destruction vp; try inversion x.
    simp denote_bredex. setoid_rewrite denote_value_equation_4.
    red. setoid_rewrite bind_bind.
    eapply rutt_bind. eapply types_equiv_value_refl. constructor.
    intros. setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
    eapply rutt_bind. eapply types_equiv_value_refl. constructor.
    intros. eapply types_equiv_comp_refl. repeat constructor; auto.
  - simp denote_comp. dependent destruction vf; try inversion x.
    simp observe. simpl denote_observed. simp denote_eval_context.
    simp denote_bredex. setoid_rewrite denote_value_equation_5.
    red. setoid_rewrite bind_ret_l. eapply rutt_bind.
    eapply types_equiv_value_refl. constructor.
    intros. eapply types_equiv_comp_refl. repeat constructor; auto.
  - simp denote_comp. simp observe.
    simpl denote_observed. simp denote_eval_context.
    simpl denote_call. eapply rutt_bind.
    eapply types_equiv_value_refl. constructor.
    intros. unfold call_term.
    destruct (call_mrec x xR r1) eqn : Heq1.
    destruct (call_mrec x xR r2) eqn : Heq2. setoid_rewrite bind_trigger.
    eapply rutt_Vis. eapply mfix_pre_call_mrec; eauto.
    intros. apply rutt_Ret. eapply mfix_post_equiv_types_equiv; eauto.
  - specialize (IHc c eq_refl JMeq_refl).
    simp denote_comp. simp observe.
    destruct (SmallStepSeq.observe c); try destruct b.
    + simpl denote_observed. destruct r; simp denote_eval_context;
        eapply interp_mrec_rutt with 
        (RPreInv := call_frame_pre_equiv _)
        (RPostInv := call_frame_post_equiv _); intros; eauto;
        eapply types_equiv_mfix_bodies_refl; eauto; constructor.
    + simpl denote_observed in *. simp denote_eval_context. simp denote_bredex.
      eapply interp_mrec_rutt with 
        (RPreInv := call_frame_pre_equiv _)
        (RPostInv := call_frame_post_equiv _); intros; eauto;
        eapply types_equiv_mfix_bodies_refl; eauto; constructor.
  - specialize (IHc c eq_refl JMeq_refl). simp denote_comp.
    simp observe. destruct (SmallStepSeq.observe c); try destruct b.
    + simpl denote_observed in *. destruct r; simp denote_eval_context;
        eapply mapE_rutt; eapply rutt_mon; try eapply IHc; eauto;
        try apply mfix_pre_equiv_lift_handler; apply mfix_post_equiv_lift_handler.
    + simpl denote_observed in *. simp denote_eval_context.
      simp denote_bredex.
      eapply mapE_rutt; eapply rutt_mon; try eapply IHc; eauto;
        try apply mfix_pre_equiv_lift_handler; apply mfix_post_equiv_lift_handler.
  - specialize (IHc c eq_refl JMeq_refl). simp denote_comp.
    simp observe. destruct (SmallStepSeq.observe c); try destruct b.
    + simpl denote_observed in *. destruct r; simp denote_eval_context;
        eapply mapE_rutt; eapply rutt_mon; try eapply IHc; eauto;
        try apply mfix_pre_equiv_perm_handler; apply mfix_post_equiv_perm_handler.
    + simpl denote_observed in *. simp denote_eval_context.
      simp denote_bredex.
      eapply mapE_rutt; eapply rutt_mon; try eapply IHc; eauto;
        try apply mfix_pre_equiv_perm_handler; apply mfix_post_equiv_perm_handler.
Qed.



Lemma step_stable1 t MR (c : comp t [] MR) c' :
  step c = inl (Some c') ->
  comp_equiv_rutt (denote_comp c tt) (denote_comp c' tt).
Proof.
  unfold step. intros.
  destruct (SmallStepSeq.observe c) eqn : Heq; try discriminate.
  destruct b. injection H. intros. subst.
  rewrite denote_observe_correct. 
  rewrite Heq. simpl denote_observed. 
  apply step_eval_context_correct; auto.
Qed.

Lemma observe_inr_comp_ret t MR (c : comp t [] MR) v :
  step c = inr v <->
  c = comp_ret v.
Proof.
  split.
  - unfold step.
    destruct (SmallStepSeq.observe c) eqn : Heq; try destruct b; try discriminate.
    intros. injection H. intros. subst c0.
    dependent induction c; simp observe in Heq; 
      try (destruct (SmallStepSeq.observe c1)); 
      try (destruct (SmallStepSeq.observe c));
      try destruct b; try discriminate; eauto.
    + injection Heq. intros. subst. auto.
    + dependent destruction vn; simp observe in Heq; try discriminate.
      inversion x.
    + dependent destruction vn; simp observe in Heq; try discriminate.
      inversion x.
    + dependent destruction vn; try discriminate. inversion x.
    + dependent destruction vf; simp observe in Heq; try discriminate.
      inversion x.
  - unfold step. intros Hc. subst. simp observe. auto.
Qed.

Lemma step_stable2 t MR (c : comp t [] MR) v :
  step c = inr v ->
  comp_equiv_rutt (denote_comp c tt) (denote_value v tt).
Proof.
  intros H. apply observe_inr_comp_ret in H. subst.
  simp denote_comp.
  apply types_equiv_value_refl. constructor.
Qed.

Theorem step_stable t (c1 c2 : comp t [] []) :
  step_rel c1 c2 -> comp_equiv_rutt (denote_comp c1 tt) (denote_comp c2 tt).
Proof.
  intros. inversion H. subst.
  apply step_stable1; auto.
Qed.

Theorem eval_stable t (c : comp t [] []) (v : closed_value t) :
  eval_rel c v -> comp_equiv_rutt (denote_comp c tt) (denote_value v tt).
Proof.
  intros Hcv.
  induction Hcv.
  eapply step_stable in H. etransitivity; eauto.
  apply step_stable2; auto.
Qed.
