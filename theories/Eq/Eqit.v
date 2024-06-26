From Coq Require Import
     Program
     Setoid
     Morphisms
     Relations.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Utils
     Basics.HeterogeneousRelations
     Eq.Paco2
     Basics.Monad
.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition.

Local Open Scope entree_scope.


Local Coercion is_true : bool >-> Sortclass.

#[global] Instance Symmetric_bot2 (A : Type) : @Symmetric A bot2.
Proof. auto. Qed.

#[global] Instance Transitive_bot2 (A : Type) : @Transitive A bot2.
Proof. auto. Qed.

(** Definition of core equivalence relation for EnTrees *)
Section eqit.

  Context {E : Type} `{EncodingType E} {R1 R2 : Type@{entree_u}} (RR : R1 -> R2 -> Prop).

  Inductive eqitF (b1 b2 : bool) vclo (sim : entree E R1 -> entree E R2 -> Prop) :
    entree' E R1 -> entree' E R2 -> Prop :=
  | EqRet r1 r2 (REL : RR r1 r2) : eqitF b1 b2 vclo sim (RetF r1) (RetF r2)
  | EqTau m1 m2 (REL : sim m1 m2) : eqitF b1 b2 vclo sim (TauF m1) (TauF m2)
  | EqVis (e : E) k1 k2 (REL : forall a : encodes e, vclo sim (k1 a) (k2 a) : Prop) :
    eqitF b1 b2 vclo sim (VisF e k1) (VisF e k2)
  | EqTauL t1 ot2 (CHECK : b1) (REL : eqitF b1 b2 vclo sim (observe t1) ot2) :
    eqitF b1 b2 vclo sim (TauF t1) ot2
  | EqTauR ot1 t2 (CHECK : b2) (REL : eqitF b1 b2 vclo sim ot1 (observe t2)) :
    eqitF b1 b2 vclo sim ot1 (TauF t2)
  .
  Hint Constructors eqitF : entree.

  Definition eqit_ b1 b2 vclo sim : entree E R1 -> entree E R2 -> Prop :=
    fun t1 t2 => eqitF b1 b2 vclo sim (observe t1) (observe t2).

  Lemma eqitF_mono b1 b2 x0 x1 vclo vclo' sim sim'
        (IN: eqitF b1 b2 vclo sim x0 x1)
        (MON: monotone2 vclo)
        (LEc: vclo <3= vclo')
        (LE: sim <2= sim'):
    eqitF b1 b2 vclo' sim' x0 x1.
  Proof.
    intros. induction IN; eauto with entree.
  Qed.

  Lemma eqit__mono b1 b2 vclo (MON: monotone2 vclo) : monotone2 (eqit_ b1 b2 vclo).
  Proof. do 2 red. intros. eapply eqitF_mono; eauto. Qed.

  Hint Resolve eqit__mono : paco.


  Lemma eqit_idclo_mono: monotone2 (@id (entree E R1 -> entree E R2 -> Prop)).
  Proof. unfold id. eauto. Qed.

  Hint Resolve eqit_idclo_mono : paco.

  Definition eqit b1 b2 : entree E R1 -> entree E R2 -> Prop :=
    paco2 (eqit_ b1 b2 id) bot2.

  Definition eq_itree := eqit false false.
  Definition eutt := eqit true true.
  Definition euttge := eqit true false.

End eqit.

#[global] Hint Constructors eqitF : entree.
#[global] Hint Unfold eqit_ : entree.
#[global] Hint Resolve eqit__mono : paco.
#[global] Hint Resolve eqit_idclo_mono : paco.
#[global] Hint Unfold eqit : entree.
#[global] Hint Unfold eq_itree : entree.
#[global] Hint Unfold eutt : entree.
#[global] Hint Unfold euttge : entree.
#[global] Hint Unfold id : entree.

Ltac unfold_eqit :=
  (try match goal with [|- eqit_ _ _ _ _ _ _ _ ] => red end);
  (repeat match goal with [H: eqit_ _ _ _ _ _ _ _ |- _ ] => red in H end).

Lemma eqit_Ret {E R1 R2} `{EncodingType E} b1 b2 (RR : R1 -> R2 -> Prop) r1 r2 : 
  RR r1 r2 -> eqit RR b1 b2 (Ret r1) (Ret r2).
Proof.
  intros. pstep. constructor. auto.
Qed.

Lemma eqit_Tau {E R1 R2} `{EncodingType E} {b1 b2 RR} t1 t2 :
  @eqit E _ R1 R2 RR b1 b2 t1 t2 ->
  eqit RR b1 b2 (Tau t1) (Tau t2).
Proof.
  intros. pstep. constructor. left. apply H0.
Qed.

Lemma eqit_Vis {E R1 R2} `{EncodingType E} b1 b2 (RR : R1 -> R2 -> Prop) (e : E) k1 k2 :
  (forall a, eqit RR b1 b2 (k1 a) (k2 a)) -> 
  eqit RR b1 b2 (Vis e k1) (Vis e k2).
Proof.
  intros. pstep. constructor. left. apply H0.
Qed.

Lemma eqit_Vis_inv {E R1 R2} `{EncodingType E} b1 b2 (RR : R1 -> R2 -> Prop) (e : E) k1 k2 :
  eqit RR b1 b2 (Vis e k1) (Vis e k2) -> forall a, eqit RR b1 b2 (k1 a) (k2 a).
Proof.
  intros. punfold H0. red in H0. dependent destruction H0. pclearbot. apply REL.
Qed.

Lemma eqit_inv_Tau_l {E R1 R2 RR} `{enc: EncodingType E} b1 t1 t2 :
  @eqit E _ R1 R2 RR b1 true (Tau t1) t2 -> eqit RR b1 true t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t1) as tt1. genobs t2 ot2.
  hinduction H before b1; intros; try discriminate.
  - inv Heqtt1. pclearbot. pstep. red. simpobs. econstructor; eauto. pstep_reverse.
  - inv Heqtt1. punfold_reverse H.
  - red in IHeqitF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
Qed.

Lemma eqit_inv_Tau_r {E R1 R2 RR} `{enc : EncodingType E} b2 t1 t2 :
  @eqit E _ R1 R2 RR true b2 t1 (Tau t2) -> eqit RR true b2 t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t2) as tt2. genobs t1 ot1.
  hinduction H before b2; intros; try discriminate.
  - inv Heqtt2. pclearbot. pstep. red. simpobs. econstructor; eauto. pstep_reverse.
  - red in IHeqitF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
  - inv Heqtt2. punfold_reverse H.
Qed.

Lemma eqit_inv_Tau {E R1 R2 RR} `{enc : EncodingType E} b1 b2 t1 t2 :
  @eqit E _ R1 R2 RR b1 b2 (Tau t1) (Tau t2) -> eqit RR b1 b2 t1 t2.
Proof with eauto with entree.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t1) as tt1. remember (TauF t2) as tt2.
  hinduction H before b2; intros; try discriminate.
  - inv Heqtt1. inv Heqtt2. pclearbot. eauto.
  - inv Heqtt1. inv H.
    + pclearbot. punfold REL. pstep. red. simpobs...
    + pstep. red. simpobs. econstructor; eauto. pstep_reverse. apply IHeqitF; eauto.
    + eauto with entree.
  - inv Heqtt2. inv H.
    + pclearbot. punfold REL. pstep. red. simpobs...
    + eauto with entree.
    + pstep. red. simpobs. econstructor; auto. pstep_reverse. apply IHeqitF; eauto.
Qed.

Lemma eqit_flip {E R1 R2} `{EncodingType E} RR b1 b2 : 
  forall (t1 : entree E R1) (t2 : entree E R2),
    eqit (flip RR) b2 b1 t2 t1 -> eqit RR b1 b2 t1 t2.
Proof.
  pcofix CIH. intros t1 t2 Ht12. pstep. red.
  punfold Ht12. red in Ht12. hinduction Ht12 before r; intros; pclearbot; eauto with entree.
  constructor. right. apply CIH. apply REL.
Qed.

Lemma eqit_mon {E R1 R2} `{EncodingType E} RR RR' (b1 b2 b1' b2': bool)
      (LEb1: b1 -> b1')
      (LEb2: b2 -> b2')
      (LERR: RR <2= RR'):
  @eqit E _ R1 R2 RR b1 b2 <2= eqit RR' b1' b2'.
Proof.
  cbn. pcofix CIH. intros t1 t2 Ht12. pstep. red. clear CIH0.
  punfold Ht12. red in Ht12. hinduction Ht12 before r; intros; pclearbot; eauto with entree.
  constructor. right. apply CIH. apply REL.
Qed.

#[global] Hint Unfold flip : entree.

Infix "≅" := (eq_itree eq) (at level 70) : type_scope.

Infix "≈" := (eutt eq) (at level 70) : type_scope.

Infix "≳" := (euttge eq) (at level 70) : type_scope.

Section eqit_closure.

Context {E : Type} `{EncodingType E} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive eqit_trans_clo b1 b2 b1' b2' (r : entree E R1 -> entree E R2 -> Prop)
          : entree E R1 -> entree E R2 -> Prop :=
  | eqit_trans_clo_intro t1 t2 t1' t2' RR1 RR2
      (EQVl: eqit RR1 b1 b1' t1 t1')
      (EQVr: eqit RR2 b2 b2' t2 t2')
      (REL: r t1' t2')
      (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
      (LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y)
  : eqit_trans_clo b1 b2 b1' b2' r t1 t2.
Hint Constructors eqit_trans_clo : entree.

Definition eqitC b1 b2 := eqit_trans_clo b1 b2 false false.
Hint Unfold eqitC : entree.

Lemma eqitC_mon b1 b2 r1 r2 t1 t2
      (IN: eqitC b1 b2 r1 t1 t2)
      (LE: r1 <2= r2):
  eqitC b1 b2 r2 t1 t2.
Proof.
  destruct IN. econstructor; eauto.
Qed.

Hint Resolve eqitC_mon : paco.

Lemma eqitC_wcompat b1 b2 vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC b1 b2) vclo <3= compose vclo (eqitC b1 b2)):
  wcompatible2 (@eqit_ E _ R1 R2 RR b1 b2 vclo) (eqitC b1 b2).
Proof with eauto with paco entree.
  econstructor; [ eauto with paco itree | ].
  intros. destruct PR.
  punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction REL before r; intros; clear t1' t2'; pclearbot; eauto with entree.
  - remember (RetF r1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; [ | eauto with entree ].
    remember (RetF r3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy...
  - remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; [ | eauto with entree ].
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; [ | eauto with entree ].
    pclearbot. econstructor. gclo.
    econstructor; eauto with paco.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; try discriminate Heqx; [ | eauto with entree ].
    dependent destruction Heqx.
    remember (VisF e0 k3) as y.
    hinduction EQVr before r; intros; try discriminate Heqy; [ | eauto with entree ].
    dependent destruction Heqy.
    econstructor. intros. pclearbot.
    eapply MON.
    + apply CMP. econstructor...
    + intros. apply gpaco2_clo, PR.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; pclearbot; try inv CHECK; [ | eauto with entree ].
    constructor. auto. eapply IHREL; eauto. pstep_reverse.
  - remember (TauF t2) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; [ | eauto with entree ].
    pclearbot. punfold REL...
Qed.


Hint Resolve eqitC_wcompat : paco.

Lemma eqit_idclo_compat b1 b2: compose (eqitC b1 b2) id <3= compose id (eqitC b1 b2).
Proof.
  intros. apply PR.
Qed.
Hint Resolve eqit_idclo_compat : paco.

Lemma eqitC_dist b1 b2:
  forall r1 r2, eqitC b1 b2 (r1 \2/ r2) <2= (eqitC b1 b2 r1 \2/ eqitC b1 b2 r2).
Proof.
  intros. destruct PR. destruct REL; eauto with entree.
Qed.

Hint Resolve eqitC_dist : paco.

Lemma eqit_clo_trans b1 b2 vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC b1 b2) vclo <3= compose vclo (eqitC b1 b2)):
  eqit_trans_clo b1 b2 false false <3= gupaco2 (eqit_ RR b1 b2 vclo) (eqitC b1 b2).
Proof.
  intros. destruct PR. gclo. econstructor; eauto with paco.
Qed.

End eqit_closure.

#[global] Hint Unfold eqitC : entree.
#[global] Hint Resolve eqitC_mon : paco.
#[global] Hint Resolve eqitC_wcompat : paco.
#[global] Hint Resolve eqit_idclo_compat : paco.
#[global] Hint Resolve eqitC_dist : paco.
Arguments eqit_clo_trans : clear implicits.
#[global] Hint Constructors eqit_trans_clo : entree.

#[global] Instance geuttgen_cong_eqit {E R1 R2 RR1 RR2 RS} `{EncodingType E} b1 b2 r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (gpaco2 (@eqit_ E _ R1 R2 RS b1 b2 id) (eqitC RS b1 b2) r rg).
Proof.
  repeat intro. guclo eqit_clo_trans. econstructor; cycle -3; eauto.
  - eapply eqit_mon, H0; eauto; try discriminate.
  - eapply eqit_mon, H1; eauto; discriminate.
Qed.

#[global] Instance geuttgen_cong_eqit_eq {E R1 R2 RS} `{EncodingType E} b1 b2 r rg:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (@eqit_ E _ R1 R2 RS b1 b2 id) (eqitC RS b1 b2) r rg).
Proof.
  eapply geuttgen_cong_eqit; intros; subst; eauto.
Qed.

#[global] Instance geutt_cong_euttge {E R1 R2 RR1 RR2 RS} `{EncodingType E} r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (euttge RR1 ==> euttge RR2 ==> flip impl)
         (gpaco2 (@eqit_ E _ R1 R2 RS true true id) (eqitC RS true true) r rg).
Proof.
  repeat intro. guclo eqit_clo_trans. eauto with entree.
Qed.

#[global] Instance geutt_cong_euttge_eq {E R1 R2 RS} `{EncodingType E} r rg:
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (gpaco2 (@eqit_ E _ R1 R2 RS true true id) (eqitC RS true true) r rg).
Proof.
  eapply geutt_cong_euttge; intros; subst; eauto.
Qed.

#[global] Instance geuttge_cong_euttge {E R1 R2 RR1 RR2 RS b} `{EncodingType E} r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (euttge RR1 ==> eq_itree RR2 ==> flip impl)
         (gpaco2 (@eqit_ E _ R1 R2 RS true b id) (eqitC RS true b) r rg).
Proof.
  repeat intro. destruct b. eapply geutt_cong_euttge; eauto.
  eapply eqit_mon; try apply H1; eauto. 
  guclo eqit_clo_trans.  eauto with entree.  
Qed.

#[global] Instance geuttge_cong_euttge_eq {E R1 R2 RS b} `{EncodingType E} r rg:
  Proper (euttge eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (@eqit_ E _ R1 R2 RS true b id) (eqitC RS true b) r rg).
Proof.
  eapply geuttge_cong_euttge; intros; subst; eauto.
Qed.

#[global] Instance geuttge_cong_euttger {E R1 R2 RR1 RR2 RS b} `{EncodingType E} r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (eq_itree RR1 ==> euttge RR2 ==> flip impl)
         (gpaco2 (@eqit_ E _ R1 R2 RS b true id) (eqitC RS b true) r rg).
Proof.
  repeat intro. destruct b. eapply geutt_cong_euttge; eauto.
  eapply eqit_mon; try apply H0; eauto.
  guclo eqit_clo_trans.  eauto with entree.  
Qed.

#[global] Instance geuttge_cong_euttger_eq {E R1 R2 RS b} `{EncodingType E} r rg:
  Proper (eq_itree eq ==> euttge eq ==> flip impl)
         (gpaco2 (@eqit_ E _ R1 R2 RS b true id) (eqitC RS b true) r rg).
Proof.
  eapply geuttge_cong_euttger; intros; subst; eauto.
Qed.



#[global] Instance eqitgen_cong_eqit {E R1 R2 RR1 RR2 RS} `{EncodingType E} b1 b2
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (@eqit E _ R1 R2 RS b1 b2).
Proof.
  ginit. intros. eapply geuttgen_cong_eqit; eauto. gfinal. eauto.
Qed.

#[global] Instance eqitgen_cong_eqit_eq {E R1 R2 RS} `{EncodingType E} b1 b2:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (@eqit E _ R1 R2 RS b1 b2).
Proof.
  eapply eqitgen_cong_eqit; intros; subst; auto.
Qed.


Section eqit_gen.

(** *** Properties of relation transformers. *)

Context {E : Type} `{EncodingType E} {R: Type} (RR : R -> R -> Prop).

#[global] Instance Reflexive_eqitF b1 b2 (sim : entree E R -> entree E R -> Prop)
: Reflexive RR -> Reflexive sim -> Reflexive (eqitF RR b1 b2 id sim).
Proof.
  red. destruct x; constructor; eauto with entree.
Qed.

#[global] Instance Symmetric_eqitF b (sim : entree E R -> entree E R -> Prop)
: Symmetric RR -> Symmetric sim -> Symmetric (eqitF RR b b id sim).
Proof.
  red. induction 3; constructor; subst; eauto.
  intros. apply H1. apply REL.
Qed.
(* should I have used that def of bind ? *)
#[global] Instance Reflexive_eqit_ b1 b2 (sim : entree E R -> entree E R -> Prop)
: Reflexive RR -> Reflexive sim -> Reflexive (eqit_ RR b1 b2 id sim).
Proof. repeat red. intros. reflexivity. Qed.

#[global] Instance Symmetric_eqit_ b (sim : entree E R -> entree E R -> Prop)
: Symmetric RR -> Symmetric sim -> Symmetric (eqit_ RR b b id sim).
Proof. repeat red; symmetry; auto. Qed.

(** *** [eqit] is an equivalence relation *)

#[global] Instance Reflexive_eqit_gen b1 b2 (r rg: entree E R -> entree E R -> Prop) :
  Reflexive RR -> Reflexive (gpaco2 (eqit_ RR b1 b2 id) (eqitC RR b1 b2) r rg).
Proof.
  pcofix CIH. gstep; intros.
  repeat red. destruct (observe x); eauto with paco entree.
Qed.

#[global] Instance Reflexive_eqit b1 b2 : Reflexive RR -> Reflexive (@eqit E _ _ _ RR b1 b2).
Proof.
  red; intros. ginit. apply Reflexive_eqit_gen; eauto.
Qed.

#[global] Instance Symmetric_eqit b : Symmetric RR -> Symmetric (@eqit E _ _ _ RR b b).
Proof.
  red; intros. apply eqit_flip.
  eapply eqit_mon, H1; eauto.
Qed.

#[global] Instance eq_sub_euttge:
  subrelation (@eq_itree E _ _ _ RR) (euttge RR).
Proof.
  ginit. pcofix CIH. intros.
  punfold H1. gstep. red in H1 |- *.
  hinduction H1 before CIH; subst; econstructor; try inv CHECK; pclearbot; auto 7 with paco entree.
Qed.

#[global] Instance euttge_sub_eutt:
  subrelation (@euttge E _ _ _ RR) (eutt RR).
Proof.
  ginit. pcofix CIH. intros.
  punfold H1. gstep. red in H1 |- *.
  hinduction H1 before CIH; subst; econstructor; pclearbot; auto 7 with paco entree.
Qed.

#[global] Instance eq_sub_eutt:
  subrelation (@eq_itree E _ _ _ RR) (eutt RR).
Proof.
  red; intros. eapply euttge_sub_eutt. eapply eq_sub_euttge. assumption.
Qed.

End eqit_gen.


#[global] Hint Resolve Reflexive_eqit Reflexive_eqit_gen : reflexivity.

Section eqit_eq.
Context {E : Type} `{EncodingType E} {R : Type}.


Lemma itree_eta_ (t : entree E R) : t ≅ go _ _ (_observe _ _ t).
Proof. 
  revert t.
  pcofix CIH. intros t. pstep. red. cbn.
  unfold observe. destruct (_observe _ _ t); eauto with entree paco.
  - constructor. left. eapply paco2_mon; eauto. eapply Reflexive_eqit. typeclasses eauto.
  - constructor. left. eapply paco2_mon; eauto. eapply Reflexive_eqit. typeclasses eauto.
Qed.

Lemma itree_eta (t : entree E R) : t ≅ go _ _ (observe t).
Proof. apply itree_eta_. Qed.

Lemma itree_eta' (ot : entree' E R) : ot = observe (go _ _ ot).
Proof. auto. Qed.

End eqit_eq.


(** ** Equations for core combinators *)

Lemma bind_ret_l {E} `{EncodingType E} {R S} (r : R) (k : R -> entree E S) : 
  EnTree.bind (Ret r) k ≅ k r.
Proof.
  pstep. red. unfold EnTree.bind, EnTree.subst. simpl. pstep_reverse.
  enough (k r ≅ k r). auto. reflexivity.
Qed.

Lemma bind_tau {E} `{EncodingType E} {R S} (t : entree E R) (k : R -> entree E S) :
  EnTree.bind (Tau t) k ≅ Tau (EnTree.bind t k).
Proof.
  pstep. red. unfold EnTree.bind, EnTree.subst at 1. simpl. constructor.
  left. unfold EnTree.subst, EnTree.subst'. match goal with |- paco2 _ _ ?t1 ?t2 => enough (t1 ≅ t2) end.
  auto. reflexivity.
Qed.

Lemma bind_vis {E} `{EncodingType E} {R S} (e : E) (ke : encodes e -> entree E R) (k : R -> entree E S) :
  EnTree.bind (Vis e ke) k ≅ Vis e (fun x => EnTree.bind (ke x) k ).
Proof.
  pstep. red. unfold EnTree.bind, EnTree.subst at 1. simpl. constructor.
  left. unfold EnTree.subst, EnTree.subst'.
  match goal with |- paco2 _ _ ?t1 ?t2 => enough (t1 ≅ t2) end.
  auto. reflexivity.
Qed.

Lemma bind_trigger {E} `{EncodingType E} {S} (e : E) (k : encodes e -> entree E S) :
  EnTree.bind (EnTree.trigger e) k ≅ Vis e k.
Proof.
  pstep. red. cbn. constructor. left. pstep. red. simpl. pstep_reverse.
  match goal with |- paco2 _ _ ?t1 ?t2 => enough (t1 ≅ t2) end.
  auto. reflexivity.
Qed.

Lemma unfold_iter {E} `{EncodingType E} {R S} (body : R -> entree E (R + S)) (x : R) :
  (EnTree.iter body x) ≅ EnTree.bind (body x) (fun rs => match rs with
                                                      | inl r => Tau (EnTree.iter body r)
                                                      | inr s => Ret s end
                                              ).
Proof.
  match goal with |- _ ≅ ?t => set t as tl end.
  pstep. red. unfold EnTree.iter.
  simpl. cbn. pstep_reverse.
  match goal with |- paco2 _ _ ?t1 ?t2 => enough (t1 ≅ t2) end.
  auto. reflexivity.
Qed.

Section eqit_closure.

Context {E : Type} `{EncodingType E} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive eqit_bind_clo b1 b2 (r : entree E R1 -> entree E R2 -> Prop) :
  entree E R1 -> entree E R2 -> Prop :=
| pbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
      (EQV: eqit RU b1 b2 t1 t2)
      (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
  : eqit_bind_clo b1 b2 r (EnTree.bind t1 k1) (EnTree.bind t2 k2)
.
Hint Constructors eqit_bind_clo : entree.

Ltac auto_ctrans :=
  intros; repeat (match goal with [H: rcompose _ _ _ _ |- _] => destruct H end); subst; eauto.
Ltac auto_ctrans_eq := try instantiate (1:=eq); auto_ctrans.

Lemma eqit_clo_bind b1 b2 vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC RR b1 b2) vclo <3= compose vclo (eqitC RR b1 b2))
      (ID: id <3= vclo):
  eqit_bind_clo b1 b2 <3= gupaco2 (eqit_ RR b1 b2 vclo) (eqitC RR b1 b2).
Proof.
  intros rr. pcofix CIH. intros. destruct PR.
  guclo eqit_clo_trans.
  econstructor; auto_ctrans_eq.
  1,2:  reflexivity.
  punfold EQV. unfold_eqit.
  unfold EnTree.bind, EnTree.subst.
  hinduction EQV before CIH; intros; pclearbot; cbn.
  - guclo eqit_clo_trans. econstructor; auto_ctrans_eq.
    setoid_rewrite bind_ret_l. reflexivity.
    setoid_rewrite bind_ret_l. reflexivity. eauto with paco.
  - gstep. red. cbn. econstructor. gfinal. left. eapply CIH. econstructor; eauto.
  - gstep. red. cbn. constructor. intros. apply ID. red.
    gfinal. left. eapply CIH. econstructor; eauto. apply REL.
  - destruct b1; try discriminate.
    guclo eqit_clo_trans.
    econstructor; auto_ctrans_eq; eauto; try reflexivity.
    pstep. red. cbn. constructor. auto. pstep_reverse. 
    apply Reflexive_eqit. auto.
  - destruct b2; try discriminate.
    guclo eqit_clo_trans. econstructor; auto_ctrans_eq; eauto; try reflexivity.
    pstep. red. cbn. constructor. auto. pstep_reverse.
    apply Reflexive_eqit. auto.
Qed.

Lemma eqit_bind {U1 U2 UU} b1 b2 t1 t2 k1 k2
      (EQT: @eqit E _ U1 U2 UU b1 b2 t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> eqit RR b1 b2 (k1 u1) (k2 u2)):
  eqit RR b1 b2 (EnTree.bind t1 k1) (EnTree.bind t2 k2).
Proof.
  ginit. guclo eqit_clo_bind. econstructor; eauto.
  intros. gfinal. right. apply EQK. auto.
Qed.

Lemma eutt_clo_bind {U1 U2 UU} t1 t2 k1 k2
      (EQT: @eutt E _ U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> eutt RR (k1 u1) (k2 u2)):
  eutt RR (EnTree.bind t1 k1) (EnTree.bind t2 k2).
Proof.
  eapply eqit_bind; eauto.
Qed.

End eqit_closure.
Arguments eqit_clo_bind : clear implicits.

#[global] Instance eqit_subst {E R S} `{EncodingType E} b1 b2 :
  Proper (pointwise_relation _ (eqit eq b1 b2) ==> eqit eq b1 b2 ==>
          eqit eq b1 b2) (@EnTree.subst E _ R S).
Proof.
  repeat intro. eapply eqit_bind; eauto. intros. subst. auto.
Qed.

#[global] Instance eqit_bind_proper {E R S} `{EncodingType E} b1 b2 :
  Proper (eqit eq b1 b2 ==> pointwise_relation _ (eqit eq b1 b2) ==>
          eqit eq b1 b2) (@EnTree.bind E _ R S).
Proof.
  repeat intro. eapply eqit_subst; eauto.
Qed.

Lemma simpobs {E R} `{EncodingType E} ot (t : entree E R) :
  ot = (observe t) -> go _ _ ot ≅ t.
Proof.
  intros. pstep. red. rewrite <- H0. rewrite itree_eta'. pstep_reverse.
  apply Reflexive_eqit. auto.
Qed.

(** *** Transitivity properties *)

Lemma trans_rcompose {R} RR (TRANS : Transitive RR) :
  forall x y : R, rcompose RR RR x y -> RR x y.
Proof.
  intros. repeat destruct H; eauto.
Qed.

Lemma eqit_trans {E R1 R2 R3} `{EncodingType E} (RR1: R1->R2->Prop) (RR2: R2->R3->Prop) b1 b2 t1 t2 t3
      (INL: eqit RR1 b1 b2 t1 t2)
      (INR: eqit RR2 b1 b2 t2 t3):
  @eqit E _ _ _ (rcompose RR1 RR2) b1 b2 t1 t3.
Proof.
  revert_until b2. pcofix CIH. intros.
  pstep. punfold INL. punfold INR. red in INL, INR |- *. genobs_clear t3 ot3.
  hinduction INL before CIH; intros; subst; clear t1 t2.
  - remember (RetF r2) as ot. hinduction INR before CIH; intros; inv Heqot; eauto with paco entree.
    constructor. red. eexists. eauto.
  - assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
    { destruct ot3; eauto; right; red; intros; discriminate. }
    destruct DEC as [EQ | EQ].
    + destruct EQ as [m3 ?]; subst.
      econstructor. right. pclearbot. eapply CIH; eauto with entree.
      apply eqit_inv_Tau. auto with entree.
    + inv INR; try (exfalso; eapply EQ; eauto; fail).
      econstructor; eauto.
      pclearbot. punfold REL. red in REL.
      hinduction REL0 before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
      * remember (RetF r1) as ot.
        hinduction REL0 before CIH; intros; inv Heqot; eauto with paco entree. constructor.
        eexists. eauto.
      * remember (VisF e k1) as ot.
        hinduction REL0 before CIH; intros; try discriminate; [  | eauto with entree ].
        inv Heqot.
        econstructor. intros. right.
        destruct (REL a), (REL0 a); try contradiction. 
        apply inj_pair2 in H2. subst. eauto.
      * eapply IHREL0; eauto. pstep_reverse.
        destruct b1; inv CHECK0.
        apply eqit_inv_Tau_r. eauto with entree.
  - remember (VisF e k2) as ot.
    hinduction INR before CIH; intros; try discriminate; [  | eauto with entree ].
    inv Heqot. apply inj_pair2 in H2. subst. constructor.
    pclearbot. right. eapply CIH; [apply REL0 | apply REL ].
  - eauto with entree.
  - remember (TauF t0) as ot.
    hinduction INR before CIH; intros; try inversion Heqot; subst.
    2,3: eauto 3 with itree.
    eapply IHINL. pclearbot. punfold REL. eauto with entree.
    constructor; eauto with entree.
Qed.

#[global] Instance Transitive_eqit {E} `{EncodingType E} {R: Type} (RR : R -> R -> Prop) (b1 b2: bool):
  Transitive RR -> Transitive (@eqit E _ _ _ RR b1 b2).
Proof.
  red; intros. eapply eqit_mon, eqit_trans; eauto using (trans_rcompose RR).
Qed.

#[global] Instance Transitive_eqit_eq {E} `{EncodingType E} {R: Type} (b1 b2: bool):
  Transitive (@eqit E _ R R eq b1 b2).
Proof.
  apply Transitive_eqit. repeat intro; subst; eauto.
Qed.

#[global] Instance Equivalence_eqit {E} `{EncodingType E} {R: Type} (RR : R -> R -> Prop) (b: bool):
  Equivalence RR -> Equivalence (@eqit E _ R R RR b b).
Proof.
  constructor; try typeclasses eauto.
Qed.

#[global] Instance Equivalence_eqit_eq {E} `{EncodingType E} {R: Type} (b: bool):
  Equivalence (@eqit E _ R R eq false false).
Proof.
  constructor; try typeclasses eauto.
Qed.

#[global] Instance Transitive_eutt {E R RR} `{EncodingType E} : Transitive RR -> Transitive (@eutt E _ R R RR).
Proof.
  red; intros. eapply eqit_mon, eqit_trans; eauto using (trans_rcompose RR).
Qed.

#[global] Instance Equivalence_eutt {E R RR} `{EncodingType E} : Equivalence RR -> Equivalence (@eutt E _ R R RR).
Proof.
  constructor; try typeclasses eauto.
Qed.


Lemma bind_ret_r {E R} `{EncodingType E} :
  forall s : entree E R,
    EnTree.bind s (fun x => Ret x) ≅ s.
Proof.
  ginit. gcofix CIH. intros.
  destruct (observe s) eqn : Heq; symmetry in Heq; apply simpobs in Heq; rewrite <- Heq.
  - rewrite bind_ret_l. apply Reflexive_eqit_gen. auto.
  - rewrite bind_tau. gstep. constructor. gfinal. eauto.
  - rewrite bind_vis. gstep. constructor. gfinal. eauto.
Qed.

Theorem bind_bind E R S T `{EncodingType E} :
  forall (s : entree E R) (k : R -> entree E S) (h : S -> entree E T),
    EnTree.bind (EnTree.bind s k) h ≅ EnTree.bind s (fun r => EnTree.bind (k r) h).
Proof.
  ginit. gcofix CIH. intros.
  destruct (observe s) eqn : Hs; symmetry in Hs; apply simpobs in Hs.
  - setoid_rewrite <- Hs. setoid_rewrite bind_ret_l. gfinal. right.
    eapply paco2_mon with (r := bot2); intros; try contradiction.
    apply Reflexive_eqit. auto.
  - setoid_rewrite <- Hs. repeat rewrite bind_tau. gstep. red. constructor.
    gfinal. left. eauto.
  - setoid_rewrite <- Hs. repeat rewrite bind_vis. gstep. red. constructor.
    intros. gfinal. left. eauto.
Qed.

Theorem eqit_iter E R1 R2 S1 S2 `{EncodingType E} b1 b2 RR RS
        (body1 : R1 -> entree E (R1 + S1)) (body2 : R2 -> entree E (R2 + S2)) :
  (forall r1 r2, (RR r1 r2 : Prop) -> eqit (sum_rel RR RS) b1 b2 (body1 r1) (body2 r2)) ->
  forall r1 r2, RR r1 r2 -> eqit RS b1 b2 (EnTree.iter body1 r1) (EnTree.iter body2 r2).
Proof.
  intro Hbodies. ginit. gcofix CIH. intros r1 r2 Hr.
  specialize (Hbodies r1 r2 Hr) as Hbodies'.
  punfold Hbodies'. red in Hbodies'.
  remember (observe (body1 r1)) as or1.
  remember (observe (body2 r2)) as or2.
  hinduction Hbodies' before r; intros;  apply simpobs in Heqor1, Heqor2.
  - setoid_rewrite unfold_iter. rewrite <- Heqor1. rewrite <- Heqor2.
    setoid_rewrite bind_ret_l.
    inv REL.
    + gstep. constructor. gfinal. eauto.
    + gstep. constructor. auto.
  - setoid_rewrite unfold_iter.
    rewrite <- Heqor1. rewrite <- Heqor2. setoid_rewrite bind_tau.
    gstep. constructor. pclearbot. guclo eqit_clo_bind. econstructor; eauto.
    intros. inv H0.
    + gstep. constructor. gfinal. eauto.
    + gstep. constructor. auto.
  - setoid_rewrite unfold_iter.
    rewrite <- Heqor1. rewrite <- Heqor2. setoid_rewrite bind_vis.
    gstep. constructor. pclearbot. guclo eqit_clo_bind. econstructor; eauto.
    intros. apply REL. intros. inv H0.
    + gstep. constructor. gfinal. eauto.
    + gstep. constructor. auto.
  - setoid_rewrite unfold_iter. rewrite <- Heqor1.
    guclo eqit_clo_bind. econstructor; eauto. rewrite Heqor1. eauto.
    intros. inv H0.
    + gstep. constructor. gfinal. eauto.
    + gstep. constructor. auto.
  - setoid_rewrite unfold_iter. rewrite <- Heqor2.
    guclo eqit_clo_bind. econstructor; eauto. rewrite Heqor2. eauto.
    intros. inv H0.
    + gstep. constructor. gfinal. eauto.
    + gstep. constructor. auto.
Qed.

Theorem tau_euttge E R `{EncodingType E} : forall (t : entree E R), Tau t ≳ t.
Proof.
  intros. pstep. constructor. auto. pstep_reverse. apply Reflexive_eqit. auto.
Qed.

Theorem tau_eutt E R `{EncodingType E} : forall (t : entree E R), Tau t ≈ t.
Proof.
  intros. pstep. constructor. auto. pstep_reverse. apply Reflexive_eqit. auto.
Qed.

#[global] Instance Eq1_entree {E} `{EncodingType E} : Eq1 (@entree E _) :=
  fun A m1 m2 => @eq_itree E _ _ _ eq m1 m2.

#[global] Instance MonadLaws_entree {E} `{EncodingType E} : MonadLawsE (@entree E _).
Proof.
constructor.
- intros. apply bind_ret_l.
- intros. apply bind_ret_r.
- intros. apply bind_bind.
- intros. apply eqit_bind_proper.
Qed.

Arguments tau_eutt {_ _ _}.
