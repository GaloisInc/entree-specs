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





Definition var_eq_sym {A} {a b : A} {l} (x : var a l) (y : var b l) (Hxy : var_eq x y) : var_eq y x.
Proof.
  dependent induction Hxy. constructor. constructor. auto.
Defined.

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
Definition dep_f_equal {A B C} (f g : forall a : A, B a -> C a) := forall a b, f a b = g a b.

Lemma dep_f_equal_var_map_skip A Γ1 Γ2 (t : A)
      (f : forall t', var t' Γ1 -> var t' Γ2) (g : forall t', var t' Γ1 -> var t' Γ2) : 
  dep_f_equal f g -> dep_f_equal (var_map_skip (b := t) f) (var_map_skip (b := t) g).
Proof.
  intros. red. intros. dependent destruction b; simp var_map_skip.
  auto. rewrite H. auto.
Qed.

Lemma comp_val_map_fequal :
  (forall t Γ1 MR (c : comp t Γ1 MR) Γ2 
     (f : forall t', var t' Γ1 -> var t' Γ2) (g : forall t', var t' Γ1 -> var t' Γ2),
      dep_f_equal f g ->
      comp_map c f = comp_map c g) /\
    (forall t Γ1 (v : value t Γ1) Γ2 
       (f : forall t', var t' Γ1 -> var t' Γ2) (g : forall t', var t' Γ1 -> var t' Γ2),
        dep_f_equal f g ->
      val_map v f = val_map v g) /\
  (forall Γ1 MR R1 R2 (bodies : mfix_bodies Γ1 MR R1 R2) Γ2
     (f : forall t', var t' Γ1 -> var t' Γ2) (g : forall t', var t' Γ1 -> var t' Γ2),
      dep_f_equal f g ->
      bodies_map bodies f = bodies_map bodies g).
Proof.
  apply comp_value_mutind; intros; simp comp_map; auto;
    try (erewrite H, H0; eauto; fail);
    try (erewrite H; eauto; fail);
    try (erewrite H, H0; eauto; try apply dep_f_equal_var_map_skip; auto; fail).
  - erewrite H; eauto; try apply dep_f_equal_var_map_skip; auto.
  - erewrite H; eauto. erewrite H0; eauto; try apply dep_f_equal_var_map_skip; auto.
    erewrite H1;  eauto; try apply dep_f_equal_var_map_skip; auto.
  - erewrite H; eauto. erewrite H0; eauto; try apply dep_f_equal_var_map_skip; auto.
    erewrite H1;  eauto; try apply dep_f_equal_var_map_skip; auto.
    apply dep_f_equal_var_map_skip; auto.
  - erewrite H; eauto. erewrite H0; eauto; try apply dep_f_equal_var_map_skip; auto.
    apply dep_f_equal_var_map_skip; auto.
Qed.


#[local] Instance comp_map_dep_f_equal t Γ1 Γ2 MR : 
  Proper (eq ==> dep_f_equal ==> eq) (comp_map (t := t) (Γ1 := Γ1) (Γ2 := Γ2) (MR := MR)).
Proof.
  repeat intro. subst. destruct comp_val_map_fequal as [H _].
  erewrite H; eauto.
Qed.

#[local] Instance val_map_dep_f_equal t Γ1 Γ2 : 
  Proper (eq ==> dep_f_equal ==> eq) (val_map (t := t) (Γ1 := Γ1) (Γ2 := Γ2)).
Proof.
  repeat intro. subst. destruct comp_val_map_fequal as [_ [H _]].
  erewrite H; eauto.
Qed.

Lemma comp_val_map_fusion :
  (forall t Γ1 MR (c : comp t Γ1 MR) Γ2 Γ3 
     (f : forall t', var t' Γ1 -> var t' Γ2) (g : forall t', var t' Γ2 -> var t' Γ3),
      comp_map (comp_map c f) g = comp_map c (fun t' x => g _ (f _ x))) /\
  (forall t Γ1 (v : value t Γ1) Γ2 Γ3
     (f : forall t', var t' Γ1 -> var t' Γ2) (g : forall t', var t' Γ2 -> var t' Γ3),
      val_map (val_map v f) g = val_map v (fun t' x => g _ (f _ x))) /\
  (forall Γ1 MR R1 R2 (bodies : mfix_bodies Γ1 MR R1 R2) Γ2 Γ3
     (f : forall t', var t' Γ1 -> var t' Γ2) (g : forall t', var t' Γ2 -> var t' Γ3),
      bodies_map (bodies_map bodies f) g = bodies_map bodies (fun t' x => g _ (f _ x))).
Proof.
  apply comp_value_mutind; intros; simp comp_map; auto;
    try (rewrite H; rewrite H0; auto; fail);
    try (rewrite H; auto; fail).
  - rewrite H. f_equal. eapply comp_map_dep_f_equal. auto.
    red. intros. dependent destruction b; simp var_map_skip; auto.
  - rewrite H; rewrite H0. f_equal; auto. eapply comp_map_dep_f_equal. auto.
    red. intros. dependent destruction b; simp var_map_skip; auto.
  - rewrite H; rewrite H0; rewrite H1. f_equal; auto. 
    eapply comp_map_dep_f_equal. auto.
    red. intros. dependent destruction b; simp var_map_skip; auto.
  - rewrite H; rewrite H0; rewrite H1. f_equal.
    eapply comp_map_dep_f_equal. auto.
    red. intros. dependent destruction b; simp var_map_skip; auto. f_equal.
    dependent destruction b1; simp var_map_skip; auto.
  - rewrite H; rewrite H0. f_equal; auto. eapply comp_map_dep_f_equal. auto.
    red. intros. dependent destruction b; simp var_map_skip; auto. f_equal.
    dependent destruction b1; simp var_map_skip; auto.
  - rewrite H; rewrite H0. f_equal. eapply comp_map_dep_f_equal. auto.
    red. intros. dependent destruction b; simp var_map_skip; auto.
Qed.


Lemma val_map_fusion : forall t Γ1 (v : value t Γ1) Γ2 Γ3
     (f : forall t', var t' Γ1 -> var t' Γ2) (g : forall t', var t' Γ2 -> var t' Γ3),
      val_map (val_map v f) g = val_map v (fun t' x => g _ (f _ x)).
Proof.
  specialize (comp_val_map_fusion); tauto.
Qed.

Equations var_of {A} Γ1 {t : A} {Γ2} : var t (Γ1 ++ [t] ++ Γ2) :=
 var_of [] := VarZ;
 var_of (t0 :: Γ1) := VarS (var_of Γ1).

Lemma remove_var_of A (t : A) Γ1 Γ2 : remove t (Γ1 ++ [t] ++ Γ2) (var_of Γ1) = Γ1 ++ Γ2.
Proof.
  revert Γ2. induction Γ1.
  - cbn. intros. simp var_of. simp remove. auto.
  - intros. simp var_of. cbn. simp remove. setoid_rewrite IHΓ1. auto.
Qed.

Lemma VarZ_JMeq A t1 t2 Γ1 Γ2 : t1 = t2 -> Γ1 = Γ2 -> (@VarZ A t1 Γ1) ~= (@VarZ A t2 Γ2).
Proof.
  intros. subst. auto.
Qed.

Lemma VarS_JMeq A (t1 t2 t3 : A) Γ1 Γ2 (x : var t1 Γ1) (y : var t2 Γ2) : 
  t1 = t2 -> Γ1 = Γ2 -> x ~= y -> VarS (b := t3) x ~= VarS (b := t3) y.
Proof.
  intros. subst. auto.
Qed.

Lemma VarS_JMeq_inv A (t1 t2 t3 : A) Γ1 Γ2 (x : var t1 Γ1) (y : var t2 Γ2) : 
  t1 = t2 -> Γ1 = Γ2 -> VarS (b := t3) x ~= VarS (b := t3) y -> x ~= y.
Proof. 
  intros. subst. apply JMeq_eq in H1. injection H1. intros. inj_existT.
  subst. auto.
Qed.

Lemma VarS_VarZ_JMeq_inv A Γ1 Γ2 (t : A) (y : var t Γ1) :
  Γ1 = Γ2 ->
  @VarS A t t Γ1 y ~= @VarZ A t Γ2 -> False.
Proof.
  intros. subst. apply JMeq_eq in H0. discriminate.
Qed.

Lemma val_var_VarZ_JMeq t1 t2 Γ1 Γ2 : t1 = t2 -> Γ1 = Γ2 -> val_var (@VarZ _ t1 Γ1)  ~= val_var (@VarZ _ t2 Γ2).
Proof.
  intros. subst. auto.
Qed.

Lemma val_var_VarS_JMeq (t1 t2 t3 : type) Γ1 Γ2 (x : var t1 Γ1) (y : var t2 Γ2) : 
  t1 = t2 -> Γ1 = Γ2 -> x ~= y -> val_var (VarS (b := t3) x) ~= val_var (VarS (b := t3) y).
Proof.
  intros. subst. auto.
Qed.

Lemma val_map_val_var_JMeq t Γ1 Γ2 Γ3 (v : value t Γ1) (x : var t Γ2) 
      (f : forall t', var t' Γ1 -> var t' Γ3) (z : var t Γ3) : 
  (forall y : var t Γ1, x ~= y -> f _ y = z) ->
  Γ1 = Γ2 -> v ~= val_var x -> val_map v f = val_var z.
Proof.
  intros. subst. subst. simp comp_map. rewrite H; auto.
Qed.



Lemma remove_var_var_of (A : Type) (t1 t2 : A) Γ1 Γ2 (x : var t1 (Γ1 ++ [t2] ++ Γ2)) (Hneq : var_neq (var_of Γ1) x) : exists y : var t1 (Γ1 ++ Γ2),
    y ~= remove_var _ _ _ _ _ Hneq.
Proof.
  generalize dependent Γ1. intros Γ1. induction Γ1.
  - cbn. simp var_of. intros x Hneq. dependent destruction Hneq.
    setoid_rewrite remove_var_equation_1. eexists. eauto.
  - cbn. simp var_of. intros x Hneq. dependent destruction x.
    + dependent destruction Hneq. setoid_rewrite remove_var_equation_2.
      exists VarZ. Transparent remove. cbn. Opaque remove. apply VarZ_JMeq; auto.
      symmetry. apply remove_var_of.
    + dependent destruction Hneq. specialize (IHΓ1 x Hneq). destruct IHΓ1 as [y Hy].
      exists (VarS y). setoid_rewrite remove_var_equation_3. 
      Transparent remove. cbn. Opaque remove. apply VarS_JMeq; auto.
      symmetry. apply remove_var_of.
Qed.


(* these correspond to the cases of subst_var *)
Lemma subst_var_var_of t Γ1 Γ2 (v : value t Γ2) : subst_var Γ1 Γ2 v (var_of Γ1) = weaken_l_value Γ1 v.
Proof.
  induction Γ1.
  - simp var_of. simp subst_var. unfold weaken_l_value. rewrite val_map_id. auto.
    cbn. intros. simp weaken_var_l. auto.
  - simp var_of. simp subst_var. rewrite IHΓ1. unfold weaken_l_value_single.
    simp weaken_l_value. unfold weaken_l_value. rewrite val_map_fusion.
    apply val_map_dep_f_equal. auto. red. intros. clear IHΓ1.
    generalize dependent Γ1. induction Γ2. 
    + intros. simp weaken_var_l. auto.
    + intros. simp weaken_var_l. auto.
Qed.

Lemma subst_var_var_eq_of t1 t2 Γ1 Γ2 (v : value t2 Γ2) (x : var t1 (Γ1 ++ [t2] ++ Γ2) ) (Heq : var_eq x (@var_of _ Γ1 t2 Γ2)) :
  subst_var Γ1 Γ2 v x ~= weaken_l_value Γ1 v.
Proof.
  generalize dependent Γ1. intros Γ1. induction Γ1.
  - cbn. simp var_of. intros. dependent destruction Heq. simp subst_var. unfold weaken_l_value.
    rewrite val_map_id; auto.
  - cbn. simp var_of. intros. dependent destruction Heq. simp subst_var.
    unfold weaken_l_value_single. specialize (IHΓ1 x0 Heq).
    assert (t1 = t2). eapply var_eq_eq'; eauto. subst.
    rewrite IHΓ1. match goal with |- ?x ~= ?y => enough (x = y) end. rewrite H. auto.
    setoid_rewrite val_map_fusion. auto.
Qed.

Lemma subst_var_neq_var_of t1 t2 Γ1 Γ2 (v : value t2 Γ2) (x : var t1 (Γ1 ++ [t2] ++ Γ2))
      (Hneq : var_neq (var_of Γ1) x) : subst_var Γ1 Γ2 v x ~= val_var (remove_var _ _ _ _ _ Hneq).
Proof.
  revert v. generalize dependent Γ1. intros Γ1. induction Γ1.
  - cbn. simp var_of. intros. dependent destruction Hneq. simp remove_var.
    setoid_rewrite remove_var_equation_1. destruct Γ2; simp subst_var; auto. inversion x0.
  - cbn. simp var_of. intros x Hneq v.
    dependent destruction Hneq.
    + simp subst_var. cbn. simp remove. setoid_rewrite remove_var_equation_2.
      clear IHΓ1. Transparent remove. cbn. Opaque remove.
      eapply val_var_VarZ_JMeq. auto.
      cbn. setoid_rewrite remove_var_of. auto.
    + simp subst_var. cbn. simp remove_var. setoid_rewrite remove_var_equation_3. 
      specialize IHΓ1 with (x := y) (Hneq := Hneq) (v := v). unfold weaken_l_value_single, weaken_l_value.
      specialize remove_var_var_of with (Hneq := Hneq) as [z Hz].
      (**)
      erewrite val_map_val_var_JMeq; try apply IHΓ1; eauto.
      3 : symmetry; apply remove_var_of.
      Unshelve.
      3 : exact (VarS z).
      * Transparent remove. cbn. Opaque remove. eapply val_var_VarS_JMeq; auto.
        symmetry. apply remove_var_of.
      * intros. simp weaken_var_l. assert (y0 ~= z). symmetry in H. eapply JMeq_trans; try apply H. 
        symmetry. auto. subst. auto.
Qed.

(* if trivial subst holds then substitution is just renaming,
   prove that the correct weakening implies trivial subst holds
*)
Inductive trivial_subst_value : forall {t1 Γ1 t2 Γ2}, value t1 (Γ1 ++ [t2] ++ Γ2) -> Prop :=
| tsv_var t1 Γ1 t2 Γ2 (x : var t1 (Γ1 ++ [t2] ++ Γ2)) (Hneq : var_neq x (var_of Γ1)) :
  trivial_subst_value (val_var x)
| tsv_abs t1 t2 Γ1 t3 Γ2 MR (cbody : comp t2 ((t1 :: Γ1) ++ [t3] ++ Γ2) MR) :
          trivial_subst_comp  cbody ->
          trivial_subst_value (val_abs cbody)
| tsv_const Γ1 t2 Γ2 (n : nat) :
  @trivial_subst_value Nat Γ1 t2 Γ2 (val_const n)
| tsv_nil t1 Γ1 t2 Γ2 :
  @trivial_subst_value (List t1) Γ1 t2 Γ2 val_nil
| tsv_cons t1 Γ1 t2 Γ2 (vh : value t1 (Γ1 ++ [t2] ++ Γ2)) (vt : value (List t1) (Γ1 ++ [t2] ++ Γ2)) :
  trivial_subst_value vh -> trivial_subst_value vt ->
  trivial_subst_value (val_cons vh vt)
| tsv_pair t1 t2 Γ1 t3 Γ2 
           (v1 : value t1 (Γ1 ++ [t3] ++ Γ2)) (v2 : value t2 (Γ1 ++ [t3] ++ Γ2)) :
  trivial_subst_value v1 -> trivial_subst_value v2 ->
  trivial_subst_value (val_pair v1 v2)
with trivial_subst_comp  : forall {t1 MR Γ1 t2 Γ2}, comp t1 (Γ1 ++ [t2] ++ Γ2) MR -> Prop :=
| tsv_ret t1 Γ1 t2 Γ2 MR (v : value t1 (Γ1 ++ [t2] ++ Γ2)) :
  trivial_subst_value v -> trivial_subst_comp (comp_ret (MR := MR) v)
| tsv_let t1 t2 Γ1 t3 Γ2 MR 
          (c1 : comp t1 ((Γ1 ++ [t3] ++ Γ2)) MR) (c2 : comp t2 ((t1 :: Γ1) ++ [t3] ++ Γ2) MR) :
  trivial_subst_comp c1 -> trivial_subst_comp c2 ->
  trivial_subst_comp (comp_let c1 c2)
| tsv_match_nat t1 Γ1 t2 Γ2 MR (vn : value Nat (Γ1 ++ [t2] ++ Γ2))
                (cZ : comp t1 (Γ1 ++ [t2] ++ Γ2) MR) 
                (cS : comp t1 ((Nat :: Γ1) ++ [t2] ++ Γ2) MR) :
  trivial_subst_value vn -> trivial_subst_comp cZ -> trivial_subst_comp cS ->
  trivial_subst_comp (comp_match_nat vn cZ cS)
| tsv_succ Γ1 t2 Γ2 MR (vn : value Nat (Γ1 ++ [t2] ++ Γ2)) :
  trivial_subst_value vn -> trivial_subst_comp (comp_succ (MR := MR) vn)
| tsv_match_list t1 t2 Γ1 t3 Γ2 MR (vl : value (List t1) (Γ1 ++ [t3] ++ Γ2))
                 (cnil : comp t2 (Γ1 ++ [t3] ++ Γ2) MR)
                 (ccons : comp t2 ((t1 :: (List t1) :: Γ1) ++ [t3] ++ Γ2) MR) :
  trivial_subst_value vl -> trivial_subst_comp cnil -> trivial_subst_comp ccons ->
  trivial_subst_comp (comp_match_list vl cnil ccons)
| tsv_split t1 t2 t3 Γ1 t4 Γ2 MR (vp : value (Pair t1 t2) (Γ1 ++ [t4] ++ Γ2))
            (cs : comp t3 (((t1 :: t2 :: Γ1) ++ [t4] ++ Γ2)) MR) :
  trivial_subst_value vp -> trivial_subst_comp cs ->
  trivial_subst_comp (comp_split vp cs)
| tsv_app t1 t2 Γ1 t3 Γ2 MR 
          (vf : value (Arrow t1 MR t2) (Γ1 ++ [t3] ++ Γ2)) 
          (varg : value t1 (Γ1 ++ [t3] ++ Γ2)) :
  trivial_subst_value vf -> trivial_subst_value varg ->
  trivial_subst_comp (comp_app vf varg)
| tsv_call t1 t2 Γ1 t3 Γ2 MR R (xR : var R MR) (x : var (t1, t2) R) 
           (v : value t1 (Γ1 ++ [t3] ++ Γ2)) : 
  trivial_subst_value v -> trivial_subst_comp (comp_call xR x v)
| tsv_mfix t1 Γ1 t2 Γ2 MR R
           (bodies : mfix_bodies (Γ1 ++ [t2] ++ Γ2) MR R R)
           (c : comp t1 (Γ1 ++ [t2] ++ Γ2) (R :: MR)) :
  trivial_subst_bodies bodies -> trivial_subst_comp c ->
  trivial_subst_comp (comp_mfix R bodies c)
| tsv_lift t1 Γ1 t2 Γ2 MR1 MR2 (c : comp t1 (Γ1 ++ [t2] ++ Γ2) MR2) : 
  trivial_subst_comp c -> trivial_subst_comp (comp_lift (MR1 := MR1) c)
| tsv_perm t1 Γ1 t2 Γ2 MR1 MR2 (Hperm : perm MR1 MR2)
           (c : comp t1 (Γ1 ++ [t2] ++ Γ2) MR1) :
  trivial_subst_comp c -> trivial_subst_comp (comp_perm Hperm c)
with trivial_subst_bodies : forall {MR R1 R2 Γ1 t2 Γ2}, mfix_bodies (Γ1 ++ [t2] ++ Γ2) MR R1 R2 -> Prop :=
| tsv_bodies_nil MR R1 Γ1 t2 Γ2 : trivial_subst_bodies 
                                    (@mfix_bodies_nil (Γ1 ++ [t2] ++ Γ2) MR R1)
| tsv_bodies_cons MR t1 t2 R1 R2 Γ1 t3 Γ2 
                  (cbody : comp t2 (((t1 :: Γ1) ++ [t3] ++ Γ2)) (R1 :: MR))
                  (bodies : mfix_bodies (Γ1 ++ [t3] ++ Γ2) MR R1 R2) :
  trivial_subst_comp cbody -> trivial_subst_bodies bodies ->
  trivial_subst_bodies (mfix_bodies_cons cbody bodies)
.

(* need a lemma with neq_var var_of Γ1*)

Definition subst_comp_comm_ind t3 Γ MR (c1 : comp t3 Γ MR) : Prop :=
  forall Γ1 Γ2 t1 t2 
    (c2 : comp t3 (Γ1 ++ ([t1] ++ ([t2] ++ Γ2))) MR)
    (c3 : comp t3 ((Γ1 ++ [t1]) ++ [t2] ++ Γ2) MR)
    (c4 : comp t3 (Γ1 ++ [t1] ++ Γ2) MR)
    (v1 : closed_value t1) (v2 : closed_value t2), 
    Γ = Γ1 ++ ([t1] ++ ([t2] ++ Γ2)) ->
    c1 ~= c2 ->
    c2 ~= c3 ->
    c4 ~= subst_comp c3 (weaken_r_value Γ2 v2) ->
    subst_comp (subst_comp c2 (weaken_r_value (t2 :: Γ2) v1)) (weaken_r_value Γ2 v2) = 
      subst_comp c4 (weaken_r_value _ v1).

Definition subst_value_comm_ind t3 Γ (v01 : value t3 Γ) : Prop :=
  forall Γ1 Γ2 t1 t2
    (v02 : value t3 (Γ1 ++ ([t1] ++ ([t2] ++ Γ2))))
    (v03 : value t3 ((Γ1 ++ [t1]) ++ [t2] ++ Γ2))
    (v04 : value t3 (Γ1 ++ [t1] ++ Γ2))
    (v1 : closed_value t1) (v2 : closed_value t2),
    Γ = Γ1 ++ ([t1] ++ ([t2] ++ Γ2)) ->
    v01 ~= v02 ->
    v02 ~= v03 ->
    v04 ~= subst_value v03 (weaken_r_value Γ2 v2) ->
    subst_value (subst_value v02 (weaken_r_value (t2 :: Γ2) v1)) (weaken_r_value _ v2) =
      subst_value v04 (weaken_r_value _ v1).

Definition subst_bodies_comm_ind Γ MR R1 R2 (bodies1 : mfix_bodies Γ MR R1 R2) : Prop :=
  forall Γ1 Γ2 t1 t2
    (bodies2 : mfix_bodies (Γ1 ++ ([t1] ++ ([t2] ++ Γ2))) MR R1 R2)
    (bodies3 : mfix_bodies ((Γ1 ++ [t1]) ++ [t2] ++ Γ2) MR R1 R2)
    (bodies4 : mfix_bodies (Γ1 ++ [t1] ++ Γ2) MR R1 R2)
    (v1 : closed_value t1) (v2 : closed_value t2),
    Γ = Γ1 ++ ([t1] ++ ([t2] ++ Γ2)) ->
    bodies1 ~= bodies2 -> 
    bodies2 ~= bodies3 ->
    bodies4 ~= subst_bodies bodies3 (weaken_r_value Γ2 v2) ->
    subst_bodies (subst_bodies bodies2 (weaken_r_value (t2 :: Γ2) v1)) (weaken_r_value _ v2) =
      subst_bodies bodies4 (weaken_r_value _ v1).

Lemma val_const_JMeq Γ1 Γ2 n (v : value Nat Γ2) :
      Γ1 = Γ2 -> val_const (Γ := Γ1) n ~= v -> v = val_const n.
Proof.
  intros. subst. auto.
Qed.


Lemma val_nil_JMeq Γ1 Γ2 t (v : value (List t) Γ2) :
      Γ1 = Γ2 -> val_nil (t := t) (Γ := Γ1) ~= v -> v = val_nil.
Proof.
  intros. subst. auto.
Qed.



Lemma val_cons_JMeq Γ1 Γ2 t (v : value (List t) Γ2)
      (vh : value t Γ1) (vt : value (List t) Γ1) :
  Γ1 = Γ2 ->
  val_cons vh vt ~= v ->
  exists vh' vt', vh' ~= vh /\ vt' ~= vt /\ v = val_cons vh' vt'.
Proof.
  intros. subst. do 2 eexists. repeat (split; eauto).
Qed.



Lemma val_pair_JMeq Γ1 Γ2 t1 t2 (v : value (Pair t1 t2) Γ2)
      (v1 : value t1 Γ1) (v2 : value t2 Γ1) :
  Γ1 = Γ2 ->
  val_pair v1 v2 ~= v ->
  exists v1' v2', v1' ~= v1 /\ v2' ~= v2 /\ v = val_pair v1' v2'.
Proof.
  intros. subst. do 2 eexists. repeat (split; eauto).
Qed.



Lemma val_abs_JMeq Γ1 Γ2 MR t1 t2 (v : value (Arrow t1 MR t2) Γ2)
      (cbody : comp t2 (t1 :: Γ1) MR) :
  Γ1 = Γ2 ->
  val_abs cbody ~= v ->
  exists cbody', cbody' ~= cbody /\ v = val_abs cbody'.
Proof.
  intros. subst. eexists. repeat (split; eauto).
Qed.


Lemma val_var_JMeq Γ1 Γ2 t (v : value t Γ2) (x : var t Γ1) :
  Γ1 = Γ2 -> 
  val_var x ~= v ->
  exists x', x' ~= x /\ v = val_var x'.
Proof.
  intros. subst. eexists. repeat (split; eauto).
Qed.


Lemma comp_ret_JMeq Γ1 Γ2 MR t (c : comp t Γ2 MR) (v : value t Γ1):
  Γ1 = Γ2 -> 
  comp_ret (MR := MR) v ~= c ->
  exists v', v' ~= v /\ c = comp_ret v'.
Proof.
  intros. subst. eexists. repeat (split; eauto).
Qed.



Lemma comp_let_JMeq Γ1 Γ2 MR t1 t2 (c : comp t2 Γ2 MR) (c1 : comp t1 Γ1 MR) (c2 : comp t2 (t1 :: Γ1) MR):
  Γ1 = Γ2 -> 
  comp_let c1 c2 ~= c ->
  exists c1' c2', c1' ~= c1 /\ c2' ~= c2 /\ c = comp_let (t1 := t1) c1' c2'.
Proof.
  intros. subst. do 2 eexists. repeat (split; eauto).
Qed.



Lemma comp_match_nat_JMeq Γ1 Γ2 MR t (c : comp t Γ2 MR) (vn : value Nat Γ1) (cZ : comp t Γ1 MR) (cS: comp t (Nat :: Γ1) MR):
  Γ1 = Γ2 -> 
  comp_match_nat vn cZ cS ~= c ->
  exists vn' cZ' cS', vn' ~= vn /\ cZ' ~= cZ /\ cS' ~= cS /\ c = comp_match_nat vn' cZ' cS'.
Proof.
  intros. subst. do 3 eexists. repeat (split; eauto).
Qed.


Lemma comp_match_list_JMeq Γ1 Γ2 MR t1 t2 (c : comp t2 Γ2 MR) (vl : value (List t1) Γ1) 
      (cnil : comp t2 Γ1 MR) (ccons: comp t2 (t1 :: List t1 :: Γ1) MR):
  Γ1 = Γ2 -> 
  comp_match_list vl cnil ccons ~= c ->
  exists vl' cnil' ccons', vl' ~= vl /\ cnil' ~= cnil /\ ccons' ~= ccons /\ c = comp_match_list (t1 := t1) vl' cnil' ccons'.
Proof.
  intros. subst. do 3 eexists. repeat (split; eauto).
Qed.



Lemma comp_succ_JMeq Γ1 Γ2 MR (c : comp Nat Γ2 MR) (vn : value Nat Γ1) : 
  Γ1 = Γ2 ->
  comp_succ (MR := MR) vn ~= c ->
  exists vn', vn' ~= vn /\ c = comp_succ vn'.
Proof.
  intros. subst. eexists. split; eauto.
Qed.


Lemma comp_split_JMeq Γ1 Γ2 MR t1 t2 t3 (c : comp t3 Γ2 MR) (vp : value (Pair t1 t2) Γ1) 
      (cs : comp t3 (t1 :: t2 :: Γ1) MR):
  Γ1 = Γ2 -> 
  comp_split vp cs ~= c ->
  exists vp' cs', vp' ~= vp /\ cs' ~= cs /\ c = comp_split (t1 := t1) (t2:= t2) vp' cs'.
Proof.
  intros. subst. do 2 eexists. repeat (split; eauto).
Qed.


Lemma comp_app_JMeq Γ1 Γ2 MR t1 t2 (c : comp t2 Γ2 MR) (vf : value (Arrow t1 MR t2) Γ1) (varg : value t1 Γ1):
  Γ1 = Γ2 -> 
  comp_app vf varg ~= c ->
  exists vf' varg', vf' ~= vf /\ varg' ~= varg /\ c = comp_app (t1 := t1) vf' varg'.
Proof.
  intros. subst. do 2 eexists. repeat (split; eauto).
Qed.

Lemma comp_call_JMeq Γ1 Γ2 MR t1 t2 R (c : comp t2 Γ2 MR) (xR : var R MR) (x : var (t1, t2) R)
      (v : value t1 Γ1) :
  Γ1 = Γ2 ->
  comp_call xR x v ~= c ->
  exists v', v' ~= v /\ c = comp_call xR x v'.
Proof.
  intros. subst. eexists. split; eauto.
Qed.

Lemma comp_mfix_JMeq Γ1 Γ2 MR t R (c : comp t Γ2 MR) (bodies : mfix_bodies Γ1 MR R R) (cin : comp t Γ1 (R :: MR)) :
  Γ1 = Γ2 ->
  comp_mfix R bodies cin ~= c ->
  exists bodies' cin', bodies' ~= bodies /\ cin' ~= cin /\ c = comp_mfix R bodies' cin'.
Proof.
  intros. subst. do 2 eexists. repeat (split; eauto).
Qed.

Lemma comp_lift_JMeq Γ1 Γ2 MR1 MR2 t (c : comp t Γ2 (MR1 ++ MR2)) (c0 : comp t Γ1 MR2) :
  Γ1 = Γ2 ->
  comp_lift (MR1 := MR1) c0 ~= c ->
  exists c0', c0' ~= c0 /\ c = comp_lift (MR1 := MR1) c0'.
Proof.
  intros. subst. eexists. split; eauto.
Qed.

Lemma comp_perm_JMeq Γ1 Γ2 MR1 MR2 t (c : comp t Γ2 MR2) (Hperm : perm MR1 MR2) (c0 : comp t Γ1 MR1) : 
  Γ1 = Γ2 ->
  comp_perm Hperm c0 ~= c ->
  exists c0', c0' ~= c0 /\ c = comp_perm Hperm c0'.
Proof.
  intros. subst. eexists. split; eauto.
Qed.

Lemma mfix_bodies_nil_JMeq Γ1 Γ2 MR R1 (bodies : mfix_bodies Γ2 MR R1 nil) :
  Γ1 = Γ2 ->
  mfix_bodies_nil (MR := MR) (R := R1) (Γ := Γ1) ~= bodies ->
  bodies = mfix_bodies_nil.
Proof.
  intros. subst. auto.
Qed.

Lemma mfix_bodies_cons_JMeq Γ1 Γ2 MR R1 R2 t1 t2 (bodies : mfix_bodies Γ2 MR R1 ((t1,t2) :: R2))
      (cbody : comp t2 (t1 :: Γ1) (R1 :: MR)) (bodiest : mfix_bodies Γ1 MR R1 R2) : 
  Γ1 = Γ2 ->
  mfix_bodies_cons cbody bodiest ~= bodies ->
  exists cbody' bodiest', cbody' ~= cbody /\ bodiest' ~= bodiest /\ bodies = mfix_bodies_cons cbody' bodiest'.
Proof.
  intros. subst. do 2 eexists. repeat (split; eauto).
Qed.


Ltac subst_comp_list_solve := repeat rewrite List.app_assoc; auto.

Ltac learn_type H := auto.

Ltac comp_val_inv :=
  match goal with
  | H : val_const ?n ~= ?v |- _ => learn_type H; eapply val_const_JMeq in H;
                                 try subst_comp_list_solve;
                                 subst
  | H : val_nil ~= ?v |- _ => learn_type H; eapply val_nil_JMeq in H;  
                            try subst_comp_list_solve;
                                 subst
  | H : val_cons ?vh ?vt ~= ?v |- _ => learn_type H; eapply val_cons_JMeq in H;
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : val_pair ?v1 ?v2 ~= ?v |- _ => learn_type H; eapply val_pair_JMeq in H;
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : val_abs ?cbody ~= ?v |- _ => learn_type H; eapply val_abs_JMeq in H;
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : val_var ?x ~= ?v |- _ => learn_type H; eapply val_var_JMeq in H;
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : comp_ret ?v ~= ?c |- _ => learn_type H; eapply comp_ret_JMeq in H;
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : comp_let ?c1 ?c2 ~= ?c |- _ => learn_type H; eapply comp_let_JMeq in H;
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : comp_match_nat ?vn ?cZ ?cS ~= ?c |- _ => learn_type H; 
                                               eapply comp_match_nat_JMeq in H; 
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : comp_succ ?vn  ~= ?c |- _ => learn_type H; eapply comp_succ_JMeq in H;
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : comp_match_list ?vl ?cnil ?ccons ~= ?c |- _ => 
      learn_type H; eapply comp_match_list_JMeq in H; 
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst
  | H : comp_split ?vp ?cs ~= ?c |- _ => learn_type H; eapply comp_split_JMeq in H; 
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : comp_app ?vf ?varg ~= ?c |- _ => learn_type H; eapply comp_app_JMeq in H; 
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : comp_call ?xR ?x ?v ~= ?c |- _ => learn_type H; eapply comp_call_JMeq in H; 
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : comp_mfix ?R ?bodies ?c0 ~= ?c |- _ => learn_type H; eapply comp_mfix_JMeq in H; 
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : comp_lift ?c0 ~= ?c |- _ => learn_type H; eapply comp_lift_JMeq in H; 
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : comp_perm ?Hperm ?c0 ~= ?c |- _ => learn_type H; eapply comp_perm_JMeq in H; 
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  | H : mfix_bodies_nil ~= ?bodies |- _ => learn_type H; eapply mfix_bodies_nil_JMeq in H; 
                                     try subst_comp_list_solve; 
                                     subst; clear H
  | H : mfix_bodies_cons ?cbody ?bodiest ~= ?bodies  |- _ => learn_type H; 
                                      eapply mfix_bodies_cons_JMeq in H; 
                                     try subst_comp_list_solve; 
                                     decompose record H; clear H; subst 
  end.

Lemma var_eq_var_of_contra:
  forall (t : vtype) (Γ1 Γ2 : ctx) (t1 t2 : vtype) (x : var t (Γ1 ++ [t1] ++ [t2] ++ Γ2))
    (x0 : var t ((Γ1 ++ [t1]) ++ [t2] ++ Γ2)), var_eq (var_of Γ1) x -> var_eq (var_of (Γ1 ++ [t1])) x0 -> x0 ~= x -> False.
Proof.
  intros t Γ1 Γ2 t1 t2 x x0. generalize dependent x. generalize dependent x0.
  induction Γ1.
  - cbn. simp var_of. intros. subst. dependent destruction X. dependent destruction X0.
  - cbn. simp var_of. intros. dependent destruction x0.
    + dependent destruction X0.
    + dependent destruction x. dependent destruction X.
      dependent destruction X. dependent destruction X0. eapply IHΓ1; eauto.
      clear - H. cbn in *. remember  ((Γ1 ++ [t1]) ++ t2 :: Γ2) as Γ.
      remember (Γ1 ++ t1 :: t2 :: Γ2) as Γ'.
      assert (Γ = Γ'). subst. setoid_rewrite <- List.app_assoc. auto.
      clear HeqΓ HeqΓ'. subst. apply JMeq_eq in H. injection H. intros. inj_existT.
      subst. auto.
Qed.

Lemma subst_value_JMeq_val_var  t t2 Γ1 Γ2 Γ3 (v1 : value t (Γ1 ++ [t2] ++ Γ2)) (v2 : value t2 Γ2)
      (x : var t Γ3) (y : var t (Γ1 ++ [t2] ++ Γ2)): 
  Γ3 = Γ1 ++ [t2] ++ Γ2 -> x ~= y -> v1 ~= val_var x -> subst_value v1 v2 ~= subst_var _ _ v2 y. 
Proof.
  intros. subst. simp subst_comp. auto.
Qed.

Ltac app_rew H1 H2 := symmetry in H2; eapply H1 in H2; eauto; rewrite H2.

Lemma subst_var_weaken_var_mid:
  forall (t : vtype) (Γ1 Γ2 : ctx) (x : var t (Γ1 ++ Γ2)) (t2 : vtype) (v2 : value t2 Γ2),
    subst_var Γ1 Γ2 v2 (weaken_var_mid Γ1 [t2] Γ2 t x) = val_var x.
Proof.
  intros t Γ1. induction Γ1; cbn.
  - intros. simp weaken_var_mid. simp weaken_var_l. simp subst_var.
    destruct Γ2; simp subst_var; auto. inversion x.
  - intros. dependent destruction x.
    + simp weaken_var_mid. simp subst_var. auto.
    + simp weaken_var_mid. simp subst_var. rewrite IHΓ1.
      unfold weaken_l_value_single, weaken_l_value. simp comp_map. simp weaken_var_l. auto.
Qed.

Lemma subst_weaken_mid_aux : 
  (forall t1 Γ MR (c1 : comp t1 Γ MR) Γ1 Γ2 t2 (c1' : comp t1 (Γ1 ++ Γ2) MR) (v2 : value t2 Γ2),
      Γ = Γ1 ++ Γ2 -> c1 ~= c1' ->
      subst_comp (weaken_mid_comp [t2] c1') v2 = c1') /\
  (forall t1 Γ (v1 : value t1 Γ) Γ1 Γ2 t2 (v1' : value t1 (Γ1 ++ Γ2)) (v2 : value t2 Γ2), 
      Γ = Γ1 ++ Γ2 -> v1 ~= v1' ->
      subst_value (weaken_mid_value [t2] v1') v2 = v1') /\
  (forall Γ MR R1 R2 (bodies1 : mfix_bodies Γ MR R1 R2) Γ1 Γ2 t2 (bodies1' : mfix_bodies (Γ1 ++ Γ2) MR R1 R2) (v2 : value t2 Γ2),
      Γ = Γ1 ++ Γ2 -> bodies1 ~= bodies1' ->
      subst_bodies (weaken_mid_bodies [t2] bodies1') v2 = bodies1').  
Proof.
  apply comp_value_mutind; intros; subst; simp subst_comp; auto.
  - unfold weaken_mid_value. simp comp_map. simp subst_comp. 
    f_equal; eauto.
  - unfold weaken_mid_value. simp comp_map. simp subst_comp.
    f_equal; eauto.
  - unfold weaken_mid_value. simp comp_map. simp subst_comp. f_equal.
    erewrite <- H with (v2 := v2); eauto.
  - unfold weaken_mid_value. simp comp_map. simp subst_comp.
    apply subst_var_weaken_var_mid.
  - unfold weaken_mid_comp. simp comp_map. simp subst_comp.
    f_equal. eauto.
  - unfold weaken_mid_comp. simp comp_map. simp subst_comp.
    f_equal; eauto. erewrite <- H0 with (v2 := v2); eauto.
  - unfold weaken_mid_comp. simp comp_map. simp subst_comp.
    f_equal; eauto. erewrite <- H1 with (v2 := v2); eauto.
  - unfold weaken_mid_comp. simp comp_map. simp subst_comp.
    f_equal; eauto.
  - unfold weaken_mid_comp. simp comp_map. simp subst_comp.
    f_equal; eauto. erewrite <- H1 with (v2 := v2); eauto.
  - unfold weaken_mid_comp. simp comp_map. simp subst_comp.
    f_equal; eauto. erewrite <- H0 with (v2 := v2); eauto.
  - unfold weaken_mid_comp. simp comp_map. simp subst_comp.
    f_equal; eauto.
  - unfold weaken_mid_comp. simp comp_map. simp subst_comp.
    f_equal; eauto.
  - unfold weaken_mid_comp. simp comp_map. simp subst_comp.
    f_equal; eauto.
  - unfold weaken_mid_comp. simp comp_map. simp subst_comp.
    f_equal; eauto.
  - unfold weaken_mid_comp. simp comp_map. simp subst_comp.
    f_equal; eauto.
  - unfold weaken_mid_bodies. simp comp_map. simp subst_comp.
    f_equal; eauto. erewrite <- H with (v2 := v2); eauto.
Qed.

Lemma subst_weaken_mid_value t1 Γ1 Γ2 t2 (v1 : value t1 (Γ1 ++ Γ2)) (v2 : value t2 Γ2) :
  subst_value (weaken_mid_value [t2] v1) v2 = v1.
Proof.
  destruct subst_weaken_mid_aux as [_ [? _]]; eauto.
Qed.

Lemma val_map_f_JMeq t1 Γ1 Γ2 Γ3 (v1 : value t1 Γ1) 
      (f : forall t, var t Γ1 -> var t Γ2) (g : forall t, var t Γ1 -> var t Γ3) :
  Γ2 = Γ3 -> (forall t x, f t x ~= g t x) -> val_map v1 f ~= val_map v1 g.
Proof.
  intros. subst. assert (forall t x, f t x = g t x). intros. rewrite H0. auto.
  match goal with |- ?x ~= ?y => enough (x = y) end.
  rewrite H1. auto. eapply val_map_dep_f_equal; eauto.
Qed.

Lemma weaken_mid_weaken_l t1 t2 Γ1 Γ2 (v1 : value t1 Γ2) :
  weaken_l_value (Γ1 ++ [t2]) v1 ~= weaken_mid_value [t2] (weaken_l_value Γ1 v1).
Proof.
  unfold weaken_l_value, weaken_mid_value. rewrite val_map_fusion.
  eapply val_map_f_JMeq. rewrite List.app_assoc. auto.
  intros.
  induction Γ1.
  - cbn. simp weaken_var_mid. auto.
  - cbn. simp weaken_var_l. simp weaken_var_mid.
    eapply VarS_JMeq; auto. rewrite List.app_assoc. auto.
Qed.

Lemma subst_weaken_l t1 Γ1 t2 Γ2 (v1 : value t1 Γ2) (v2 : value t2 Γ2)
      (v1' : value t1 (Γ1 ++ [t2] ++ Γ2)):
  v1' ~= weaken_l_value (Γ1 ++ [t2]) v1 ->
  subst_value v1' v2 = weaken_l_value Γ1 v1.
Proof.
  intros. assert (v1' ~= weaken_mid_value [t2] (weaken_l_value Γ1 v1)).
  eapply JMeq_trans; eauto ;try eapply weaken_mid_weaken_l.
  rewrite H0, subst_weaken_mid_value. auto.
Qed.

Lemma subst_comp_comm_var_aux1:
  forall (Γ1 Γ2 : ctx) (t1 t2 : vtype) (x0 : var t2 ((Γ1 ++ [t1]) ++ [t2] ++ Γ2)),
    var_eq (var_of (Γ1 ++ [t1])) x0 ->
    forall (y : var t2 (Γ1 ++ [t2] ++ Γ2)) (x : var t2 (Γ1 ++ [t1] ++ [t2] ++ Γ2))
      (Hx : var_neq (var_of Γ1) x),
      x0 ~= x ->
      y ~= remove_var t1 t2 (Γ1 ++ [t1] ++ [t2] ++ Γ2) (var_of Γ1) x Hx -> var_eq y (var_of Γ1).
Proof.
  intros Γ1 Γ2 t1 t2 x0 Hx0 y x Hx Hx0' Hy.
  induction Γ1.
  - cbn in *. simp var_of. 
    Transparent var_of. cbn in Hy. cbn in Hx. cbn in Hx0. 
    subst. dependent destruction Hx0. dependent destruction Hx0.
    dependent destruction Hx.
    Transparent remove_var. cbn. Opaque var_of. Opaque remove_var. constructor.
  - cbn in *. simp var_of. simp var_of in Hx0. dependent destruction Hx0.
    simp var_of in Hx. Transparent var_of. cbn in Hx.
    dependent destruction Hx.
    + cbn in Hy. exfalso. eapply VarS_VarZ_JMeq_inv; try eapply Hx0'. 
      rewrite <- List.app_assoc. auto.
    + Transparent var_of. cbn in Hy. Transparent remove_var. cbn in Hy.
      Opaque var_of. Opaque remove_var.
      specialize (IHΓ1 y Hx0).
      dependent destruction y0.
      symmetry in Hy. exfalso. 
      eapply VarS_VarZ_JMeq_inv with (y := (remove_var t1 a (Γ1 ++ t1 :: a :: Γ2) (var_of Γ1) y1 Hx)). 
      2 : apply Hy. apply remove_var_of.
      specialize (IHΓ1 y0 y1 Hx).
      constructor. apply IHΓ1.
      * eapply VarS_JMeq_inv; eauto. repeat rewrite <- List.app_assoc. auto.
      * eapply VarS_JMeq_inv with (t3 := a); eauto. 
        setoid_rewrite remove_var_of. auto.
Qed.
Transparent var_of. Transparent remove_var. 
Lemma subst_comp_comm_var_aux2:
  forall (t1 : vtype) (Γ1 Γ2 : ctx) (t2 : vtype) (x : var t1 (Γ1 ++ [t1] ++ [t2] ++ Γ2))
    (x0 : var t1 ((Γ1 ++ [t1]) ++ [t2] ++ Γ2)) (y' : var t1 (Γ1 ++ [t1] ++ Γ2))
    (Hx0 : var_neq (var_of (Γ1 ++ [t1])) x0),
    var_eq (var_of Γ1) x ->
    x0 ~= x ->
    remove_var t2 t1 ((Γ1 ++ [t1]) ++ [t2] ++ Γ2) (var_of (Γ1 ++ [t1])) x0 Hx0 ~= y' ->
    var_eq y' (var_of Γ1).
Proof.
  intros t1 Γ1. revert t1. induction Γ1; intros.
  - simp var_of. simp var_of in X. dependent destruction X.
    cbn in Hx0. dependent destruction Hx0.
    + cbn in H0.  subst. constructor.
    + exfalso. eapply VarS_VarZ_JMeq_inv; try eapply H; auto.
  - cbn in *. dependent destruction X. dependent destruction Hx0.
    exfalso. symmetry in H. eapply VarS_VarZ_JMeq_inv; try eapply H; auto. 
    rewrite <- List.app_assoc. auto.
    cbn in H0. dependent destruction y'.
    exfalso. eapply VarS_VarZ_JMeq_inv with (y := (remove_var t2 a ((Γ1 ++ [a]) ++ t2 :: Γ2) (var_of (Γ1 ++ [a])) y0 Hx0)); 
      try eapply H0; auto.  setoid_rewrite remove_var_of. rewrite <- List.app_assoc. auto.
    constructor. 
    eapply IHΓ1. eauto. eapply VarS_JMeq_inv; eauto. rewrite <- List.app_assoc. auto.
    Unshelve. 2 : apply Hx0. eapply VarS_JMeq_inv with (t3 := a); eauto.
    setoid_rewrite remove_var_of. rewrite <- List.app_assoc. auto.
Qed.
Opaque var_of. Opaque remove_var.
Lemma var_JMeq_exists (A : Type) (t : A) Γ1 Γ2 (x : var t Γ1) :
  Γ1 = Γ2 -> exists y : var t Γ2, x ~= y.
Proof. 
  intros. subst. eexists. eauto.
Qed.

Transparent var_of. Transparent remove_var. Transparent remove.
Lemma subst_comm_var_aux3:
  forall (t : vtype) (Γ1 Γ2 : ctx) (t1 t2 : vtype) (x : var t (Γ1 ++ [t1] ++ [t2] ++ Γ2))
    (v1 : closed_value t1) (v2 : closed_value t2) (x0 : var t ((Γ1 ++ [t1]) ++ [t2] ++ Γ2))
    (y : var t (Γ1 ++ [t2] ++ Γ2)) (z' : var t (Γ1 ++ [t1] ++ Γ2)),
    x0 ~= x ->
    forall (Hx : var_neq (var_of Γ1) x) (Hx0 : var_neq (var_of (Γ1 ++ [t1])) x0),
      remove_var t2 t ((Γ1 ++ [t1]) ++ [t2] ++ Γ2) (var_of (Γ1 ++ [t1])) x0 Hx0 ~= z' ->
      y ~= remove_var t1 t (Γ1 ++ [t1] ++ [t2] ++ Γ2) (var_of Γ1) x Hx ->
      subst_var Γ1 Γ2 (weaken_r_value Γ2 v2) y = subst_var Γ1 Γ2 (weaken_r_value Γ2 v1) z'.
Proof.
  intros t Γ1. revert t. induction Γ1; cbn; intros.
  - dependent destruction Hx. cbn in H1. dependent destruction Hx0.
    cbn in H0. dependent destruction Hx0. cbn in H0.
    dependent destruction y.
    symmetry in H1. exfalso. eapply VarS_VarZ_JMeq_inv with (y := x); eauto.
    dependent destruction z'. exfalso. eapply VarS_VarZ_JMeq_inv with (y := x); eauto.
    destruct Γ2. inversion y. simp subst_var. cbn in *. 
    eapply VarS_JMeq_inv in H0; auto. rewrite <- H0. eapply VarS_JMeq_inv in H1; auto.
    rewrite H1. auto.
  - dependent destruction Hx.
    + cbn in *. dependent destruction Hx0.
      * cbn in H0. cbn in *. 
        assert (y = VarZ).
        { dependent destruction y; auto. exfalso. eapply VarS_VarZ_JMeq_inv; try apply H1.
          setoid_rewrite remove_var_of. auto. }
        assert (z' = VarZ).
        { dependent destruction z'; auto. symmetry in H0. exfalso. eapply VarS_VarZ_JMeq_inv; try apply H0.
          setoid_rewrite remove_var_of. rewrite <- List.app_assoc. auto. }
        subst.
        simp subst_var. auto.
      * exfalso. eapply VarS_VarZ_JMeq_inv with (y := y0); try eapply H. rewrite <- List.app_assoc. auto.
    + cbn in *. dependent destruction Hx0.
      * exfalso. symmetry in H. eapply VarS_VarZ_JMeq_inv; try apply H. rewrite <- List.app_assoc. auto.
      * cbn in*.
        dependent destruction z'. exfalso. eapply VarS_VarZ_JMeq_inv; try apply H0. 
        setoid_rewrite remove_var_of. rewrite <- List.app_assoc. auto.
        dependent destruction y. symmetry in H1. exfalso. eapply VarS_VarZ_JMeq_inv; try apply H1.
        setoid_rewrite remove_var_of. auto.
        eapply VarS_JMeq_inv in H1; auto. 2 : setoid_rewrite remove_var_of; auto.
        eapply VarS_JMeq_inv in H0; auto. 2 : setoid_rewrite remove_var_of; auto.
        2 : rewrite <- List.app_assoc; auto. simp subst_var. f_equal.
        eapply IHΓ1; eauto. eapply VarS_JMeq_inv; eauto. rewrite <- List.app_assoc. auto.
Qed.
Opaque var_of. Opaque remove_var. Opaque remove.

Lemma subst_comp_comm_mut_ind :
      (forall t3 Γ MR c1, subst_comp_comm_ind t3 Γ MR c1) /\
      (forall t3 Γ v01, subst_value_comm_ind t3 Γ v01) /\
      (forall Γ MR R1 R2 bodies1, subst_bodies_comm_ind Γ MR R1 R2 bodies1).
Proof.
  apply comp_value_mutind.
  - red. intros. subst. learn_type H1. comp_val_inv. simp subst_comp. 
    simp subst_comp in H2. symmetry in H2. comp_val_inv. simp subst_comp. auto.
  - red. intros. subst. simp subst_comp. comp_val_inv. simp subst_comp in H2. symmetry in H2.
    comp_val_inv. simp subst_comp. auto.
  - intros t Γ vh Hvh vt Hvt.  (* try to figure out this case today*)
    red. intros. subst. comp_val_inv. simp subst_comp. simp subst_comp in H2.
    symmetry in H2. comp_val_inv. simp subst_comp. erewrite Hvh; eauto.
    erewrite Hvt; eauto.
  - intros t1 t2 Γ v1 Hv1 v2 Hv2.  red. intros. subst.
    comp_val_inv. simp subst_comp in H2. symmetry in H2. comp_val_inv.
    simp subst_comp. erewrite Hv1; eauto. erewrite Hv2; eauto.
  - intros t1 t2 Γ MR cbody Hcbody. red. intros. subst.
    comp_val_inv. simp subst_comp in H2. symmetry in H2.
    comp_val_inv. simp subst_comp. erewrite Hcbody; eauto.
  - red. intros. subst. simp subst_comp. comp_val_inv.
    simp subst_comp in H2.
    specialize (var_eq_neq _ _ _ (var_of Γ1) x) as [Hx | Hx];
    specialize  (var_eq_neq _ _ _ (var_of (Γ1 ++ [t1])) x0) as [Hx0 | Hx0].
    + exfalso. eapply var_eq_var_of_contra; eauto.
    + specialize subst_var_neq_var_of with (Hneq := Hx0) as Hsubst.
      assert (forall v, subst_var Γ1 ([t2] ++ Γ2) v x ~= weaken_l_value Γ1 v). intros.
      apply subst_var_var_eq_of. apply var_eq_sym. auto.
      assert (v04 ~= val_var (remove_var t2 t ((Γ1 ++ [t1]) ++ [t2] ++ Γ2) (var_of (Γ1 ++ [t1])) x0 Hx0)).
      eapply JMeq_trans; eauto.
      specialize remove_var_var_of with (Hneq := Hx0) as [y Hy].
      assert (t1 = t). apply var_eq_surj in Hx as Ht. auto.
      subst. rename t into t1.
      specialize (H (weaken_r_value (t2 :: Γ2) v1)).
      specialize subst_weaken_l with (v1' := subst_var Γ1 ([t2] ++ Γ2) (weaken_r_value (t2 :: Γ2) v1) x) as Hsubstwl.
      erewrite Hsubstwl with (v1 := weaken_r_value Γ2 v1).
      2 : { eapply JMeq_trans; eauto. unfold weaken_l_value, weaken_r_value.
            repeat rewrite val_map_fusion. 
            simp weaken_val_r. unfold weaken_var_r. 
            eapply val_map_f_JMeq. rewrite List.app_assoc. auto.
            intros. inversion x1. }
      clear Hsubstwl.
      assert (exists y' : var t1 (Γ1 ++ [t1] ++ Γ2), remove_var t2 t1 ((Γ1 ++ [t1]) ++ [t2] ++ Γ2) (var_of (Γ1 ++ [t1])) x0 Hx0 ~= y').
      { eapply var_JMeq_exists. rewrite remove_var_of. rewrite List.app_assoc. auto. }
      destruct H3 as [y' Hy'].
      
      eapply subst_value_JMeq_val_var in H1; eauto.
      2 : rewrite remove_var_of; rewrite List.app_assoc; auto.
      Unshelve. 2 : apply (weaken_r_value Γ2 v1).
      rewrite H1.
      assert (var_eq y' (var_of Γ1)).
      eapply subst_comp_comm_var_aux2; eauto.
      erewrite (subst_var_var_eq_of _ _ _ _ _ _ X).
      auto.
    + assert (t = t2). apply var_eq_surj in Hx0. auto.
      subst.
      specialize subst_var_neq_var_of with (Hneq := Hx) as Hsubst.
      specialize remove_var_var_of with (Hneq := Hx) as [y Hy].
      eapply subst_value_JMeq_val_var in Hsubst; eauto.
      2 : apply remove_var_of. 
      Unshelve. 2 : apply (weaken_r_value (t2 :: Γ2) v1).
      2 : apply (weaken_r_value Γ2 v2).
      assert (var_eq x0 (var_of (Γ1 ++ [t1]))). apply var_eq_sym; auto.
      eapply subst_var_var_eq_of with (v :=  (weaken_r_value Γ2 v2)) in X.
      cbn in X. rename X into Hx0'.
      assert (Hx0'' : v04 ~= weaken_l_value (Γ1 ++ [t1]) (weaken_r_value Γ2 v2)).
      eapply JMeq_trans; eauto.
      assert (var_eq y (var_of Γ1)). eapply subst_comp_comm_var_aux1; eauto.
      eapply subst_var_var_eq_of with (v := (weaken_r_value Γ2 v2)) in X.
      cbn in X. erewrite subst_weaken_l with (v1' := v04); eauto.
      rewrite Hsubst, X. auto.
    + specialize subst_var_neq_var_of with (Hneq := Hx) as Hsubst1.
      specialize subst_var_neq_var_of with (Hneq := Hx0) as Hsubst2.
      specialize (Hsubst1 (weaken_r_value (t2 :: Γ2) v1)).
      specialize remove_var_var_of with (Hneq := Hx) as [y Hy].
      eapply subst_value_JMeq_val_var in Hsubst1; eauto.
      2 : apply remove_var_of.
      Unshelve. 2 : apply (weaken_r_value Γ2 v2). rewrite Hsubst1.
      specialize (Hsubst2 (weaken_r_value Γ2 v2)).
      specialize remove_var_var_of with (Hneq := Hx0) as [z Hz].
      assert (exists (z' : var t (Γ1 ++ [t1] ++ Γ2)), remove_var t2 t ((Γ1 ++ [t1]) ++ [t2] ++ Γ2) (var_of (Γ1 ++ [t1])) x0 Hx0 ~= z').
      { eapply var_JMeq_exists. rewrite remove_var_of. rewrite List.app_assoc. auto. }
      destruct H as [z' Hz'].
      assert (v04 ~= val_var (remove_var t2 t ((Γ1 ++ [t1]) ++ [t2] ++ Γ2) (var_of (Γ1 ++ [t1])) x0 Hx0)).
      eapply JMeq_trans; eauto. eapply subst_value_JMeq_val_var in H; eauto.
      2 : rewrite remove_var_of; rewrite List.app_assoc; auto.
      rewrite H. eapply subst_comm_var_aux3; eauto.
  - intros t Γ MR v Hv. red. intros. subst. comp_val_inv.
    simp subst_comp in H2. symmetry in H2. comp_val_inv.
    simp subst_comp. erewrite Hv; eauto.
  - intros t1 t2 Γ MR c1 Hc1 c2 Hc2. red. intros. subst.
    comp_val_inv. simp subst_comp in H2. symmetry in H2.
    comp_val_inv. simp subst_comp. erewrite Hc1; eauto. setoid_rewrite Hc2; eauto.
  - intros t Γ MR vn Hvn cZ HcZ cS HcS. red. intros. subst.
    comp_val_inv. simp subst_comp in H2. symmetry in H2. comp_val_inv.
    simp subst_comp. erewrite Hvn; eauto. erewrite HcZ; eauto.
    erewrite HcS; eauto.
  - intros Γ MR vn Hvn. red. intros. subst. comp_val_inv.
    simp subst_comp in H2. symmetry in H2. comp_val_inv.
    simp subst_comp. erewrite Hvn; eauto.
  - intros t1 t2 Γ MR vl Hvl cnil Hcnil ccons Hccons.
    red. intros. subst. comp_val_inv. symmetry in H2.
    simp subst_comp in H2. comp_val_inv. simp subst_comp.
    erewrite Hvl; eauto. erewrite Hcnil; eauto.
    erewrite Hccons; eauto.
  - intros t1 t2 t3 Γ MR vp Hvp es Hes. red. intros. subst.
    comp_val_inv. simp subst_comp in H2. symmetry in H2.
    comp_val_inv. simp subst_comp. erewrite Hvp; eauto.
    erewrite Hes; eauto.
  - intros t1 t2 Γ MR vf Hvf varg Hvarg. red. intros.
    subst. comp_val_inv. simp subst_comp in H2. symmetry in H2.
    comp_val_inv. simp subst_comp. erewrite Hvarg; eauto.
    erewrite Hvf; eauto.
  - intros t1 t2 Γ MR R xR x v Hv. red. intros.
    subst. comp_val_inv. simp subst_comp in H2. symmetry in H2.
    comp_val_inv. simp subst_comp. erewrite Hv; eauto.
  - intros t Γ MR R bodies Hbodies c Hc.
    red. intros. subst. comp_val_inv.
    simp subst_comp in H2. symmetry in H2.
    comp_val_inv. simp subst_comp.
    erewrite Hbodies; eauto. erewrite Hc; eauto.
  - intros t Γ MR1 MR2 c Hc. red. intros. subst.
    comp_val_inv. symmetry in H2. simp subst_comp in H2.
    comp_val_inv. simp subst_comp. erewrite Hc; eauto.
  - intros t Γ MR1 MR2 Hperm c Hc. red. intros.
    subst. comp_val_inv. symmetry in H2. simp subst_comp in H2. 
    comp_val_inv. simp subst_comp. erewrite Hc; eauto.
  - intros Γ MR R. red. intros. subst.
    comp_val_inv. simp subst_comp in H2. symmetry in H2.
    comp_val_inv.
    simp subst_comp. auto.
  - intros Γ MR t1 t2 R1 R2 body Hbody bodies Hbodies. red.
    intros. subst. comp_val_inv.
    symmetry in H2. simp subst_comp in H2. comp_val_inv.
    simp subst_comp. erewrite Hbodies; eauto. erewrite Hbody; eauto.
Qed.

Lemma subst_comp_cons_comm:
  forall (a : vtype) (Γ : ctx) (t1 t2 : vtype) (MR : mfix_ctx) (cbody : comp t2 (t1 :: a :: Γ) MR) (v1 : value a [])
    (v2 : closed_value t1),
    subst_comp_cons (subst_comp (Γ1 := [t1]) cbody (weaken_r_value Γ v1)) (weaken_r_value Γ v2) =
      subst_comp_cons (subst_comp_cons cbody (weaken_r_value (a :: Γ) v2)) (weaken_r_value Γ v1).
Proof.
  intros. destruct subst_comp_comm_mut_ind as [H _].
  setoid_rewrite H; eauto. auto.
Qed.


Lemma subst_comp_weaken_r:
  forall (t1 t2 t3 : vtype) (MR : mfix_ctx) (c3 : comp t3 [t2] MR) (v1 : closed_value t1),
    subst_comp (weaken_r_comp [t2] c3) v1 = c3.
Proof.
  intros t1 t2 t3 MR c3 v1. destruct (subst_weaken_mid_aux) as [H _].
  specialize (H t3 [t2] MR c3 [t2] []). erewrite <- H  with (v2 := v1); eauto.
  f_equal. unfold weaken_r_comp, weaken_mid_comp.
  eapply comp_map_dep_f_equal; eauto. unfold weaken_var_r. red. cbn. intros.
  dependent destruction b; try inversion b1. 
  simp append_var. simp weaken_var_mid. auto.
Qed.

Lemma subst_value_weaken_r:
  forall (t1 t3 : vtype) (v3 : value t3 []) (v1 : closed_value t1),
    subst_value (weaken_r_value [t1] v3) v1 = v3.
Proof.
  intros. destruct subst_weaken_mid_aux as [_ [H _]].
  specialize (H t3 [] v3 [] []). erewrite <- H with (v2 := v1); eauto.
  f_equal. eapply val_map_dep_f_equal; eauto.
  red. cbn. intros. inversion b. 
Qed.

Lemma subst_bodies_weaken_r : 
  forall t1 R MR (bodies : mfix_bodies [] MR R R) (v : closed_value t1),
    subst_bodies (weaken_r_bodies (G2 := [t1]) bodies ) v = bodies.
Proof.
  intros. destruct subst_weaken_mid_aux as [_ [_ H]].
  erewrite <- H; eauto. f_equal. destruct comp_val_map_fequal as [_ [_ H']].
  unfold weaken_r_bodies, weaken_mid_bodies. eapply H'.
  red. intros. inversion b.
Qed.
(*
Lemma subst_value_weaken_r' :
  forall (t1 t2 t3 : vtype) Γ (v3 : value t3 (t2 :: Γ) ) (v1 : closed_value t1),
    subst_value (weaken_r_value [t1] v3) v1 ~= v3.
Proof.
  intros. destruct subst_weaken_mid_aux as [_ [H _]].
  specialize (H t3 (t2 :: Γ) v3 [t2] Γ).
  erewrite <- H with (v1' := v3) (t2 := t2); auto.
  Unshelve. 
  at 2.
  *)
