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
     Basics.Monad
     Eq.Paco2.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Basics.QuantType
     Eq.Eqit
     Core.EnTreeDefinition
     Core.SubEvent
     Ref.EnTreeSpecDefinition
     Ref.EnTreeSpecFacts
.
Local Open Scope entree_scope.



Inductive isConcreteF {E R} `{EncodingType E} (F : entree_spec E R -> Prop) :
  entree_spec' E R -> Prop :=
  | isConcrete_Ret (r : R) : isConcreteF F (RetF r)
  | isConcrete_Tau (phi : entree_spec E R) :
      F phi -> isConcreteF F (TauF phi)
  | isConcrete_Vis e kphi :
      (forall a, F (kphi a)) -> isConcreteF F (VisF (Spec_vis e) kphi).

Hint Constructors isConcreteF.
Definition isConcrete_ {E R} `{EncodingType E} F (t: entree_spec E R) : Prop :=
  isConcreteF F (observe t).

Lemma monotone_isConcreteF {E R} `{EncodingType E} (ot : entree_spec' E R) sim sim'
  (LE : sim <1= sim')
  (IN : isConcreteF sim ot) :
  isConcreteF sim' ot.
Proof.
  induction IN; eauto.
Qed.

Lemma monotone_isConcrete_ {E R} `{EncodingType E} : monotone1 (@isConcrete_ E R _).
Proof. red. intros. eapply monotone_isConcreteF; eauto. Qed.

Hint Resolve monotone_isConcrete_ : paco.

Definition isConcrete {E R} `{EncodingType E} : entree_spec E R -> Prop := paco1 isConcrete_ bot1.

Lemma isConcreteVisInv {E R} `{EncodingType E} e (k : _ -> entree_spec E R) a :
  isConcrete (Vis (Spec_vis e) k) -> isConcrete (k a).
Proof.
  intro isc; punfold isc. inversion isc.
  assert (kphi0 = k); [ inj_existT; assumption | ].
  subst. pclearbot. apply H1.
Qed.


Variant voidE : Type := .
Instance voidE_encoded : EncodingType voidE := fun _ => False.

Section non_padded_completeness_counter.
  Program Instance quant_bool : QuantType bool :=
    {|
      quantEnc := QEnc_sum (QEnc_prop True) (QEnc_prop True);
      quantEnum := fun x => match x with | inl _ => true | inr _ => false end;
      quantEnumInv := fun b => if b then inl I else inr I;
    |}.
  Next Obligation.
    destruct a; auto.
  Qed.

  Definition top1 : entree_spec voidE unit :=
    EnTree.bind (assume_spec False) (fun _ => Ret tt).

  Lemma top1_top : forall (t : entree_spec voidE unit) RPre RPost RR,
      refines RPre RPost RR t top1.
  Proof.
    intros. pstep. red. cbn. constructor. cbn. intros [].
  Qed.


  Definition top2 : entree_spec voidE unit :=
    EnTree.bind (exists_spec bool) (fun b => if b then Ret tt else EnTree.spin).
  Context (Hdec : forall (t : entree_spec voidE unit), isConcrete t -> eutt eq t (Ret tt) \/ eutt eq t EnTree.spin).


  Lemma top2_top : forall (t : entree_spec voidE unit) RPre RPost,
      isConcrete t ->
      refines RPre RPost eq t top2.
  Proof.
    intros. specialize (Hdec t H). destruct Hdec; clear H Hdec; rename H0 into Ht.
    - punfold Ht. red in Ht. cbn in Ht. pstep. red.
      remember (RetF tt) as x.
      hinduction Ht before t; intros; inv Heqx; eauto.
      + econstructor. Unshelve. 2 : exact (inl I). cbn. constructor. auto.
      + constructor. auto.
    - pstep. red. cbn. econstructor. Unshelve. 2 : exact (inr I). cbn.
      constructor. pstep_reverse.
      generalize dependent t. pcofix CIH. intros t Ht.
      pstep. red. punfold Ht. red in Ht. remember (observe EnTree.spin) as x.
      hinduction Ht before r; intros; inv Heqx; pclearbot; eauto.
      + constructor. eauto.
      + cbn. constructor. left. pstep. red. eapply IHHt; eauto.
  Qed.


  Lemma not_refines_top1_top2 RPre RPost RR : ~ refines RPre RPost RR top1 top2.
    Proof.
      intro Hcontra. punfold Hcontra. red in Hcontra.
      inversion Hcontra.
      - cbn in *. destruct a; cbn in *.
        + subst. destruct t. cbn in *. cbn in H2. inj_existT. subst. cbn in *.
          inversion H1. cbn in *. contradiction.
        + inj_existT. subst. cbn in *. clear Hcontra.
          remember (TauF EnTree.spin) as y. remember ((VisF (Spec_forall (QEnc_prop False))
            (fun _ : False => EnTree.subst' (fun _ : () => Ret ()) (RetF ())))) as x.
          hinduction H1 before RR; intros; inv Heqx; try inv Heqy; eauto.
      - destruct a.
    Qed.
End non_padded_completeness_counter.
