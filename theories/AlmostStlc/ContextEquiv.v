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
Require Export SemanticsFactsSeq2.

(* not sure exactly how to define the contexts for contextual equivalence,
   will need to keep track of variable context 
   do I need stratification across

*)
(* seems like I might need 2 variable contexts one for  *)
Inductive comp_context : vtype -> ctx -> mfix_ctx -> vtype -> ctx -> mfix_ctx -> Type :=
  | ctx_hole {t Γ MR} : comp_context t Γ MR t Γ MR
  | ctx_ret {t1 Γ1 MR1 t2 Γ2 MR2} (V : value_context t1 Γ1 t2 Γ2 MR2) : 
    comp_context t1 Γ1 MR1 t2 Γ2 MR2
  | ctx_let1 {Γ1 MR1 t1 t2 t3 Γ2 MR2} 
             (C1 : comp_context t1 Γ1 MR1 t3 Γ2 MR2) (c2 : comp t2 (t1 :: Γ1) MR1) :
    comp_context t2 Γ1 MR1 t3 Γ2 MR2
  | ctx_let2 {Γ1 MR1 t1 t2 t3 Γ2 MR2} 
             (c1 : comp t1 Γ1 MR1) (C2 : comp_context t2 (t1 :: Γ1) MR1 t3 Γ2 MR2) :
    comp_context t2 Γ1 MR1 t3 Γ2 MR2
  | ctx_match_nat1 {Γ1 MR1 t2 t3 Γ2 MR2} (Vn : value_context Nat Γ1 t3 Γ2 MR2)
                   (cZ : comp t2 Γ1 MR1) (cS : comp t2 (Nat :: Γ1) MR1) : 
    comp_context t2 Γ1 MR1 t3 Γ2 MR2
  | ctx_match_nat2 {Γ1 MR1 t2 t3 Γ2 MR2} (vn : value Nat Γ1)
                   (CZ : comp_context t2 Γ1 MR1 t3 Γ2 MR2) (cS : comp t2 (Nat :: Γ1) MR1) :
    comp_context t2 Γ1 MR1 t3 Γ2 MR2
  | ctx_match_nat3 {Γ1 MR1 t2 t3 Γ2 MR2} (vn : value Nat Γ1)
                   (cZ : comp t2 Γ1 MR1) (CS : comp_context t2 (Nat :: Γ1) MR1 t3 Γ2 MR2) :
    comp_context t2 Γ1 MR1 t3 Γ2 MR2
  | ctx_succ {Γ1 MR1 t3 Γ2 MR2} (Vn : value_context Nat Γ1 t3 Γ2 MR2) : 
    comp_context Nat Γ1 MR1 t3 Γ2 MR2
  | ctx_match_list1 {t1 Γ1 MR1 t2 t3 Γ2 MR2} (VL : value_context (List t1) Γ1 t3 Γ2 MR2)
                    (cnil : comp t2 Γ1 MR1) (ccons : comp t2 (t1 :: List t1 :: Γ1) MR1) : 
    comp_context t2 Γ1 MR1 t3 Γ2 MR2
  | ctx_match_list2 {t1 Γ1 MR1 t2 t3 Γ2 MR2} (vl : value (List t1) Γ1) 
                    (Cnil : comp_context t2 Γ1 MR1 t3 Γ2 MR2) 
                    (ccons : comp t2 (t1 :: List t1 :: Γ1) MR1) : 
    comp_context t2 Γ1 MR1 t3 Γ2 MR2
  | ctx_match_list3 {t1 Γ1 MR1 t2 t3 Γ2 MR2} (vl : value (List t1) Γ1)
                    (cnil : comp t2 Γ1 MR1)
                    (Ccons : comp_context t2 (t1 :: List t1 :: Γ1) MR1 t3 Γ2 MR2) :
    comp_context t2 Γ1 MR1 t3 Γ2 MR2
  | ctx_split1 {t1 t2 Γ1 MR1 t3 t4 Γ2 MR2} (Vp : value_context (Pair t1 t2) Γ1 t4 Γ2 MR2)
               (cs : comp t3 (t1 :: t2 :: Γ1) MR1) : 
    comp_context t3 Γ1 MR1 t4 Γ2 MR2
  | ctx_split2 {t1 t2 Γ1 MR1 t3 t4 Γ2 MR2} (vp : value (Pair t1 t2) Γ1)
               (Cs : comp_context t3 (t1 :: t2 :: Γ1) MR1 t4 Γ2 MR2) :
    comp_context t3 Γ1 MR1 t4 Γ2 MR2
  | ctx_match_sum1 {t1 t2 t3 Γ1 MR1 t4 Γ2 MR2} 
                   (Vl : value_context (Sum t1 t2) Γ1 t4 Γ2 MR2)
                   (cinl : comp t3 (t1 :: Γ1) MR1)
                   (cinr : comp t3 (t2 :: Γ1) MR1) :
    comp_context t3 Γ1 MR1 t4 Γ2 MR2
  | ctx_match_sum2 {t1 t2 t3 Γ1 MR1 t4 Γ2 MR2}
                   (vl : value (Sum t1 t2) Γ1)
                   (Cinl : comp_context t3 (t1 :: Γ1) MR1 t4 Γ2 MR2)
                   (cinr : comp t3 (t2 :: Γ1) MR1) :
    comp_context t3 Γ1 MR1 t4 Γ2 MR2
  | ctx_match_sum3 {t1 t2 t3 Γ1 MR1 t4 Γ2 MR2}
                   (vl : value (Sum t1 t2) Γ1)
                   (Cinl : comp t3 (t1 :: Γ1) MR1)
                   (cinr : comp_context t3 (t2 :: Γ1) MR1 t4 Γ2 MR2) :
    comp_context t3 Γ1 MR1 t4 Γ2 MR2
  | ctx_app1 {t1 t2 Γ1 MR1 t3 Γ2 MR2} (Vf : value_context (Arrow t1 MR1 t2) Γ1 t3 Γ2 MR2)
            (varg : value t1 Γ1) :
    comp_context t2 Γ1 MR1 t3 Γ2 MR2
  | ctx_app2 {t1 t2 Γ1 MR1 t3 Γ2 MR2} (vf : value (Arrow t1 MR1 t2) Γ1)
             (Varg : value_context t1 Γ1 t3 Γ2 MR2) :
    comp_context t2 Γ1 MR1 t3 Γ2 MR2
  | ctx_call {t1 t2 Γ1 MR1 t3 Γ2 MR2 R}
             (xR : var R MR1) (x : var (t1,t2) R)
             (Vin : value_context t1 Γ1 t3 Γ2 MR2) : 
    comp_context t2 Γ1 MR1 t3 Γ2 MR2
  | ctx_lift {t1 Γ1 MR1 MR2 t2 Γ2 MR3}
             (C : comp_context t1 Γ1 MR2 t2 Γ2 MR3) : 
    comp_context t1 Γ1 (MR1 ++ MR2) t2 Γ2 MR3
  | ctx_perm {t1 Γ1 MR1 MR2 t2 Γ2 MR3} (Hperm : perm MR1 MR2)
             (C : comp_context t1 Γ1 MR1 t2 Γ2 MR3) : 
    comp_context t1 Γ1 MR2 t2 Γ2 MR3
  | ctx_mfix1 {t1 Γ1 R MR1 t2 Γ2 MR2}
              (Bodies : bodies_context Γ1 MR1 R R t2 Γ2 MR2)
              (c : comp t1 Γ1 (R :: MR1)) :
    comp_context t1 Γ1 MR1 t2 Γ2 MR2
  | ctx_mfix2 {t1 Γ1 R MR1 t2 Γ2 MR2}
              (bodies : mfix_bodies Γ1 MR1 R R)
              (C : comp_context t1 Γ1 (R :: MR1) t2 Γ2 MR2) : 
    comp_context t1 Γ1 MR1 t2 Γ2 MR2
with value_context : vtype -> ctx -> vtype -> ctx -> mfix_ctx -> Type :=
  | ctx_cons1 {t1 Γ1 t2 Γ2 MR} 
              (Vh : value_context t1 Γ1 t2 Γ2 MR)
              (vt : value (List t1) Γ1) : 
    value_context (List t1) Γ1 t2 Γ2 MR
  | ctx_cons2 {t1 Γ1 t2 Γ2 MR}
              (vh : value t1 Γ1)
              (Vt : value_context (List t1) Γ1 t2 Γ2 MR) :
    value_context (List t1) Γ1 t2 Γ2 MR
  | ctx_pair1 {t1 t2 Γ1 t3 Γ2 MR}
              (V1 : value_context t1 Γ1 t3 Γ2 MR)
              (v2 : value t2 Γ1) :
    value_context (Pair t1 t2) Γ1 t3 Γ2 MR
  | ctx_pair2 {t1 t2 Γ1 t3 Γ2 MR}
              (v1 : value t1 Γ1)
              (V2 : value_context t2 Γ1 t3 Γ2 MR) : 
    value_context (Pair t1 t2) Γ1 t3 Γ2 MR
  | ctx_inl {t1 t2 Γ1 t3 Γ2 MR}
            (V : value_context t1 Γ1 t3 Γ2 MR) : 
    value_context (Sum t1 t2) Γ1 t3 Γ2 MR
  | ctx_inr {t1 t2 Γ1 t3 Γ2 MR}
            (V : value_context t2 Γ1 t3 Γ2 MR) : 
    value_context (Sum t1 t2) Γ1 t3 Γ2 MR
  | ctx_abs {t1 MR1 t2 Γ1 t3 Γ2 MR2}
            (cbody : comp_context t2 (t1 :: Γ1) MR1 t3 Γ2 MR2) :
      value_context (Arrow t1 MR1 t2) Γ1 t3 Γ2 MR2
with bodies_context : ctx -> mfix_ctx -> call_frame -> call_frame -> vtype -> ctx -> mfix_ctx -> Type :=
  | ctx_bodies_cons1 {t1 t2 Γ1 MR1 R1 R2 t3 Γ2 MR2}
                     (Cbody : comp_context t2 (t1 :: Γ1) (R1 :: MR1) t3 Γ2 MR2)
                     (bodies : mfix_bodies Γ1 MR1 R1 R2) :
    bodies_context Γ1 MR1 R1 ((t1, t2) :: R2) t3 Γ2 MR2
  | ctx_bodies_cons2 {t1 t2 Γ1 MR1 R1 R2 t3 Γ2 MR2}
                     (cbody : comp t2 (t1 :: Γ1) (R1 :: MR1))
                     (Bodies : bodies_context Γ1 MR1 R1 R2 t3 Γ2 MR2) :
    bodies_context Γ1 MR1 R1 ((t1, t2) :: R2) t3 Γ2 MR2
.

Equations subst_comp_context {t1 Γ1 MR1 t2 Γ2 MR2}
          (C : comp_context t1 Γ1 MR1 t2 Γ2 MR2) (c : comp t2 Γ2 MR2) : comp t1 Γ1 MR1 :=
{
  subst_comp_context ctx_hole c := c;
  subst_comp_context (ctx_ret V) c := comp_ret (subst_value_context V c);
  subst_comp_context (ctx_let1 C1 c2) c := comp_let (subst_comp_context C1 c) c2;
  subst_comp_context (ctx_let2 c1 C2) c := comp_let c1 (subst_comp_context C2 c);
  subst_comp_context (ctx_match_nat1 Vn cZ cS) c := 
    comp_match_nat (subst_value_context Vn c) cZ cS;
  subst_comp_context (ctx_match_nat2 vn CZ cS) c := 
    comp_match_nat vn (subst_comp_context CZ c) cS;
  subst_comp_context (ctx_match_nat3 vn cZ CS) c :=
    comp_match_nat vn cZ (subst_comp_context CS c);
  subst_comp_context (ctx_succ Vn) c := comp_succ (subst_value_context Vn c);
  subst_comp_context (ctx_match_list1 Vl cnil ccons) c :=
    comp_match_list (subst_value_context Vl c) cnil ccons;
  subst_comp_context (ctx_match_list2 vl Cnil ccons) c :=
    comp_match_list vl (subst_comp_context Cnil c) ccons;
  subst_comp_context (ctx_match_list3 vl cnil Ccons) c :=
    comp_match_list vl cnil (subst_comp_context Ccons c);
  subst_comp_context (ctx_split1 Vp cs) c :=
    comp_split (subst_value_context Vp c) cs;
  subst_comp_context (ctx_split2 vp Cs) c :=
    comp_split vp (subst_comp_context Cs c);
  subst_comp_context (ctx_match_sum1 Vs cinl cinr) c :=
    comp_match_sum (subst_value_context Vs c) cinl cinr;
  subst_comp_context (ctx_match_sum2 vs Cinl cinr) c :=
    comp_match_sum vs (subst_comp_context Cinl c) cinr;
  subst_comp_context (ctx_match_sum3 vs cinl Cinr) c :=
    comp_match_sum vs cinl (subst_comp_context Cinr c);
  subst_comp_context (ctx_app1 Vf varg) c :=
    comp_app (subst_value_context Vf c) varg;
  subst_comp_context (ctx_app2 vf Varg) c :=
    comp_app vf (subst_value_context Varg c);
  subst_comp_context (ctx_call xR x Vin) c :=
    comp_call xR x (subst_value_context Vin c);
  subst_comp_context (ctx_lift C) c :=
    comp_lift (subst_comp_context C c);
  subst_comp_context (ctx_perm Hperm C) c :=
    comp_perm Hperm (subst_comp_context C c);
  subst_comp_context (ctx_mfix1 Bodies c) c0 :=
    comp_mfix _ (subst_bodies_context Bodies c0) c;
  subst_comp_context (ctx_mfix2 bodies C) c :=
    comp_mfix _ bodies (subst_comp_context C c);
}
where subst_value_context {t1 Γ1 t2 Γ2 MR2}
                   (V : value_context t1 Γ1 t2 Γ2 MR2) (c : comp t2 Γ2 MR2) : value t1 Γ1 :=
{
  subst_value_context (ctx_cons1 Vh vt) c := val_cons (subst_value_context Vh c) vt;
  subst_value_context (ctx_cons2 vh Vt) c := val_cons vh (subst_value_context Vt c);
  subst_value_context (ctx_pair1 V1 v2) c := val_pair (subst_value_context V1 c) v2;
  subst_value_context (ctx_pair2 v1 V2) c := val_pair v1 (subst_value_context V2 c);
  subst_value_context (ctx_inl V) c := val_inl (subst_value_context V c);
  subst_value_context (ctx_inr V) c := val_inr (subst_value_context V c);
  subst_value_context (ctx_abs Cbody) c := val_abs (subst_comp_context Cbody c);
}
where subst_bodies_context {Γ1 MR1 R1 R2 t2 Γ2 MR2}
          (Bodies : bodies_context Γ1 MR1 R1 R2 t2 Γ2 MR2) 
          (c : comp t2 Γ2 MR2) : mfix_bodies Γ1 MR1 R1 R2 :=
{
  subst_bodies_context (ctx_bodies_cons1 Cbody bodies) c :=
    mfix_bodies_cons (subst_comp_context Cbody c) bodies;
  subst_bodies_context (ctx_bodies_cons2 cbody Bodies) c :=
    mfix_bodies_cons cbody (subst_bodies_context Bodies c);
}.

Scheme comp_context_mind := Induction for comp_context Sort Prop
  with value_context_mind := Induction for value_context Sort Prop
  with bodies_context_mind := Induction for bodies_context Sort Prop.
Combined Scheme context_mutind from comp_context_mind, value_context_mind, bodies_context_mind.

Lemma subst_context_proper_mutind :
  (forall t1 Γ1 MR1 t2 Γ2 MR2 (C : comp_context t1 Γ1 MR1 t2 Γ2 MR2)
     (c1 c2 : comp t2 Γ2 MR2), 
      comp_equiv (denote_comp c1) (denote_comp c2) -> 
      comp_equiv 
        (denote_comp (subst_comp_context C c1)) 
        (denote_comp (subst_comp_context C c2))) /\
  (forall t1 Γ1 t2 Γ2 MR2 (V : value_context t1 Γ1 t2 Γ2 MR2)
     (c1 c2 : comp t2 Γ2 MR2),
      comp_equiv (denote_comp c1) (denote_comp c2) ->
      forall MR1, comp_equiv (MR := MR1)
        (denote_value (subst_value_context V c1))
        (denote_value (subst_value_context V c2))) /\
  (forall Γ1 MR1 R1 R2 t2 Γ2 MR2 
     (Bodies : bodies_context Γ1 MR1 R1 R2 t2 Γ2 MR2)
     (c1 c2 : comp t2 Γ2 MR2),
      comp_equiv (denote_comp c1) (denote_comp c2) ->
      forall (arg1 arg2 : denote_call_frame R2) (hyps1 hyps2 : denote_ctx Γ1),
        call_frame_pre_equiv R2 arg1 arg2 ->
        ctx_equiv Γ1 hyps1 hyps2 ->
        rutt (mfix_pre_equiv (R1 :: MR1)) (mfix_post_equiv (R1 :: MR1))
             (call_frame_post_equiv R2 arg1 arg2)
             (denote_bodies (subst_bodies_context Bodies c1) hyps1 arg1)
             (denote_bodies (subst_bodies_context Bodies c2) hyps2 arg2)).
Proof.
  apply context_mutind; intros; simp subst_comp_context.
  - red. intros. simp denote_comp. eapply H; eauto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply H; eauto. intros.
    eapply types_equiv_comp_refl. constructor; auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply types_equiv_comp_refl; eauto.
    intros. eapply H; eauto. constructor; eauto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply H; eauto. simp types_equiv.
    intros. subst. destruct r2; eapply types_equiv_comp_refl; eauto.
    constructor; eauto. simp types_equiv. auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply types_equiv_value_refl; auto.
    simp types_equiv. intros. subst. destruct r2.
    eapply H; eauto. eapply types_equiv_comp_refl; auto. constructor; auto.
    simp types_equiv. auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply types_equiv_value_refl; auto.
    simp types_equiv. intros. subst. destruct r2.
    eapply types_equiv_comp_refl; auto. eapply H; auto.
    constructor; auto. simp types_equiv. auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply H; eauto.
    simp types_equiv. intros. subst. apply rutt_Ret. auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto.
    eapply H; eauto. simp types_equiv. intros.
    dependent destruction H2. eapply types_equiv_comp_refl; eauto.
    eapply types_equiv_comp_refl; eauto. constructor; auto. constructor; auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply types_equiv_value_refl; eauto.
    simp types_equiv. intros. dependent destruction H2.
    eapply H; eauto. apply types_equiv_comp_refl; auto.
    repeat constructor; auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply types_equiv_value_refl; eauto.
    simp types_equiv. intros. dependent destruction H2.
    eapply types_equiv_comp_refl; eauto.
    apply H; auto. repeat constructor; auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply H; eauto.
    simp types_equiv. intros. dependent destruction H2.
    destruct r1. destruct r2. eapply types_equiv_comp_refl; eauto.
    repeat constructor; auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply types_equiv_value_refl; eauto.
    simp types_equiv. intros. dependent destruction H2.
    destruct r1. destruct r2. eapply H; auto.
    repeat constructor; auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply H; eauto. simp types_equiv.
    intros vv1 vv2 Hvv12. dependent destruction Hvv12;
      eapply types_equiv_comp_refl; constructor; eauto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply types_equiv_value_refl. eauto.
    simp types_equiv.
    intros vv1 vv2 Hvv12. dependent destruction Hvv12.
    eapply H. eauto. constructor; auto.
    eapply types_equiv_comp_refl. constructor; auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply types_equiv_value_refl. eauto.
    simp types_equiv.
    intros vv1 vv2 Hvv12. dependent destruction Hvv12.
    eapply types_equiv_comp_refl. constructor; auto.
    eapply H. auto. constructor; auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply H; auto.
    intros. simp types_equiv in H2. eapply rutt_bind.
    eapply types_equiv_value_refl; eauto. intros.
    setoid_rewrite tau_eutt. eauto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply types_equiv_value_refl; eauto.
    simp types_equiv. intros. eapply rutt_bind.
    eapply H; auto. intros. setoid_rewrite tau_eutt. eauto.
  - red. intros. simp denote_comp.
    eapply rutt_bind; eauto. eapply H; auto.
    intros. unfold call_term.
    destruct (call_mrec x xR r1) as [ca1 f1] eqn : Heq1.
    destruct (call_mrec x xR r2) as [ca2 f2] eqn : Heq2. 
    setoid_rewrite bind_trigger. apply rutt_Vis.
    eapply mfix_pre_call_mrec; eauto. intros.
    apply rutt_Ret. eapply mfix_post_equiv_types_equiv; eauto.
  - red. intros. simp denote_comp.
    eapply mapE_rutt. eapply rutt_mon; try eapply H; eauto.
    intros. eapply mfix_pre_equiv_lift_handler; eauto.
    intros. eapply mfix_post_equiv_lift_handler; eauto.
  - red. intros. simp denote_comp.
    eapply mapE_rutt. eapply rutt_mon; try eapply H; eauto.
    intros. eapply mfix_pre_equiv_perm_handler; eauto.
    intros. eapply mfix_post_equiv_perm_handler; eauto.
  - red. intros. simp denote_comp.
    eapply interp_mrec_rutt
     with (RPreInv := call_frame_pre_equiv R)
          (RPostInv := call_frame_post_equiv R).
    intros. eapply H; eauto.
    eapply types_equiv_comp_refl with (c := c); auto.
  - red. intros. simp denote_comp.
    eapply interp_mrec_rutt
     with (RPreInv := call_frame_pre_equiv R)
          (RPostInv := call_frame_post_equiv R).
    intros. eapply types_equiv_mfix_bodies_refl; eauto.
    eapply H; auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind. eapply H; eauto. intros.
    eapply rutt_bind. eapply types_equiv_value_refl; auto.
    simp types_equiv. intros.
    apply rutt_Ret. constructor; auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind. eapply types_equiv_value_refl; auto.
    intros. eapply rutt_bind. eapply H; eauto.
    intros. apply rutt_Ret. constructor; auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind. eapply H; eauto. intros.
    eapply rutt_bind. eapply types_equiv_value_refl; auto.
    simp types_equiv. intros.
    apply rutt_Ret. constructor; auto.
  - red. intros. simp denote_comp.
    eapply rutt_bind. eapply types_equiv_value_refl; auto.
    intros. eapply rutt_bind. eapply H; eauto.
    intros. apply rutt_Ret. constructor; auto.
  - red. intros. simp denote_comp. eapply rutt_bind.
    eapply H; eauto. intros. apply rutt_Ret. constructor; auto.
  - red. intros. simp denote_comp. eapply rutt_bind.
    eapply H; eauto. intros. apply rutt_Ret. constructor; auto.
  - red. intros. simp denote_comp.
    apply rutt_Ret. simp types_equiv. intros. eapply H; eauto.
    constructor; auto.
  - simp types_equiv in H1. dependent destruction H1; simp denote_comp.
    + eapply rutt_mon; try eapply H; eauto. simp types_equiv. intros.
      constructor. auto. constructor; auto.
    + eapply types_equiv_mfix_bodies_refl with (bodies := bodies) in H2; eauto. 
      specialize (H2 H1). eapply rutt_mon; try eapply H2; eauto.
      intros. simp types_equiv. constructor. auto.
  - simp types_equiv in H1. dependent destruction H1; simp denote_comp.
    + eapply rutt_mon; try eapply types_equiv_comp_refl; eauto. simp types_equiv. intros.
      constructor. auto. constructor; auto.
    + eapply rutt_mon; try eapply H; eauto.
      simp types_equiv. intros; constructor; auto.
Qed.

Lemma subst_comp_context_proper t1 Γ1 MR1 t2 Γ2 MR2 (C : comp_context t1 Γ1 MR1 t2 Γ2 MR2)
     (c1 c2 : comp t2 Γ2 MR2) :  
      comp_equiv (denote_comp c1) (denote_comp c2) -> 
      comp_equiv 
        (denote_comp (subst_comp_context C c1)) 
        (denote_comp (subst_comp_context C c2)).
Proof.
  destruct subst_context_proper_mutind. eauto.
Qed.

Definition context_equiv {t Γ MR} (c1 c2 : comp t Γ MR) : Prop :=
  forall (C : comp_context Nat [] [] t Γ MR) (n : nat),
    eval_rel (subst_comp_context C c1) (val_const n) <->
      eval_rel (subst_comp_context C c2) (val_const n).
