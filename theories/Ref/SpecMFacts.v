From Coq Require Export
     Morphisms
     Setoid
     Program.Equality
     Lists.List
     Logic.EqdepFacts
     Eqdep EqdepFacts
.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Basics.QuantType
     Core.EnTreeDefinition
     Core.SubEvent
     Ref.EnTreeSpecDefinition
     Ref.EnTreeSpecFacts
     Ref.EnTreeSpecCombinatorFacts
     Ref.SpecM
     Eq.Eqit
     Ref.MRecSpec
.

Import SpecMNotations.
Local Open Scope entree_scope.

From Paco Require Import paco.

Section interp_mrec_spec_quantl.
Context (D E F: Type) `{EncodingType D} `{EncodingType E} `{EncodingType F}.
Context (body : forall d : D, entree_spec (D + E) (encodes d)).
Context (RPre : Rel E F ) (RPost : PostRel E F).
Context (R1 R2 : Type) (RR : Rel R1 R2).

Lemma interp_mrec_spec_forall A `{QuantType A} : 
  interp_mrec_spec body (forall_spec A) ≅ forall_spec A.
Proof.
  pstep. red. cbn. constructor. intros. left. pstep. constructor.
  auto.
Qed.

Lemma interp_mrec_spec_exists A `{QuantType A} : 
  interp_mrec_spec body (exists_spec A) ≅ exists_spec A.
Proof.
  pstep. red. cbn. constructor. intros. left. pstep. constructor.
  auto.
Qed.

Lemma interp_mrec_spec_assume P : 
  interp_mrec_spec body (assume_spec P) ≅ assume_spec P.
Proof.
  pstep. red. cbn. constructor. intros. left. pstep. constructor.
  auto.
Qed.

Lemma interp_mrec_spec_assert P : 
  interp_mrec_spec body (assert_spec P) ≅ assert_spec P.
Proof.
  pstep. red. cbn. constructor. intros. left. pstep. constructor.
  auto.
Qed.

Lemma padded_refines_assumel (P : Prop) (HP : P) k phi:
  padded_refines RPre RPost RR (k tt) phi ->
  padded_refines RPre RPost RR (EnTree.bind (assume_spec P) k) phi.
Proof.
  intros. setoid_rewrite bind_bind. apply padded_refines_forall_specl.
  eauto.
Qed.

Lemma padded_refines_assertl (P : Prop)  k phi:
  (P -> padded_refines RPre RPost RR (k tt) phi) ->
  padded_refines RPre RPost RR (EnTree.bind (assert_spec P) k) phi.
Proof.
  intros. setoid_rewrite bind_bind. apply padded_refines_exists_specl.
  eauto.
Qed.

Lemma interp_mrec_spec_forall_specl (A : Type) `{QuantType A} k phi (a : A) : 
  padded_refines RPre RPost RR (interp_mrec_spec body (k a)) phi ->
  padded_refines RPre RPost RR (interp_mrec_spec body (EnTree.bind (forall_spec A) k )) phi.
Proof.
  intros. setoid_rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_forall. apply padded_refines_forall_specl.
  eauto.
Qed.

Lemma interp_mrec_spec_exists_specl (A : Type) `{QuantType A} k phi : 
  (forall (a : A), padded_refines RPre RPost RR (interp_mrec_spec body (k a)) phi) ->
  padded_refines RPre RPost RR (interp_mrec_spec body (EnTree.bind (exists_spec A) k )) phi.
Proof.
  intros. setoid_rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_exists. apply padded_refines_exists_specl.
  eauto.
Qed.

Lemma interp_mrec_spec_assumel (P : Prop) (HP : P) k phi:
  padded_refines RPre RPost RR (interp_mrec_spec body (k tt)) phi ->
  padded_refines RPre RPost RR (interp_mrec_spec body (EnTree.bind (assume_spec P) k) ) phi.
Proof.
  intros. rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_assume.
  setoid_rewrite bind_bind. apply padded_refines_forall_specl.
  exists HP. rewrite bind_ret_l. auto.
Qed.

Lemma interp_mrec_spec_assertl (P : Prop) k phi : 
  (P -> padded_refines RPre RPost RR (interp_mrec_spec body (k tt)) phi) -> 
  padded_refines RPre RPost RR (interp_mrec_spec body (EnTree.bind (assert_spec P) k) ) phi.
Proof.
  intros. rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_assert. setoid_rewrite bind_bind.
  apply padded_refines_exists_specl. auto.
Qed.



End interp_mrec_spec_quantl.

Section interp_mrec_spec_quantr.

Context (D E F: Type) `{EncodingType D} `{EncodingType E} `{EncodingType F}.
Context (body : forall d : D, entree_spec (D + F) (encodes d)).
Context (RPre : Rel E F ) (RPost : PostRel E F).
Context (R1 R2 : Type) (RR : Rel R1 R2).


Lemma interp_mrec_spec_forall_specr (A : Type) `{QuantType A} k phi : 
  (forall (a : A), padded_refines RPre RPost RR phi (interp_mrec_spec body (k a))) ->
  padded_refines RPre RPost RR phi (interp_mrec_spec body (EnTree.bind (forall_spec A) k )).
Proof.
  intros. setoid_rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_forall. apply padded_refines_forall_specr.
  eauto.
Qed.

Lemma interp_mrec_spec_exists_specr (A : Type) `{QuantType A} k phi (a : A) : 
  (padded_refines RPre RPost RR phi (interp_mrec_spec body (k a))) ->
  padded_refines RPre RPost RR phi (interp_mrec_spec body (EnTree.bind (exists_spec A) k )).
Proof.
  intros. setoid_rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_exists. apply padded_refines_exists_specr.
  eauto.
Qed.

Lemma padded_refines_assumer (P : Prop) k phi :
  (P -> padded_refines RPre RPost RR phi (k tt)) ->
  padded_refines RPre RPost RR phi ((EnTree.bind (assume_spec P) k)).
Proof.
  intros. setoid_rewrite bind_bind.
  apply padded_refines_forall_specr. auto.
Qed.

Lemma padded_refines_assertr (P : Prop) (HP : P) k phi :
  padded_refines RPre RPost RR phi (k tt) ->
  padded_refines RPre RPost RR phi ((EnTree.bind (assert_spec P) k)).
Proof.
  intros. setoid_rewrite bind_bind.
  apply padded_refines_exists_specr. eauto.
Qed.

Lemma interp_mrec_spec_assumer (P : Prop) k phi :
  (P -> padded_refines RPre RPost RR phi (interp_mrec_spec body (k tt))) ->
  padded_refines RPre RPost RR phi (interp_mrec_spec body (EnTree.bind (assume_spec P) k)).
Proof.
  intros. rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_assume.
  setoid_rewrite bind_bind.
  apply padded_refines_forall_specr. auto.
Qed.

Lemma interp_mrec_spec_assertr (P : Prop) (HP : P) k phi :
  padded_refines RPre RPost RR phi (interp_mrec_spec body (k tt)) ->
  padded_refines RPre RPost RR phi (interp_mrec_spec body (EnTree.bind (assert_spec P) k)).
Proof.
  intros. rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_assert.
  setoid_rewrite bind_bind.
  apply padded_refines_exists_specr. exists HP.
  auto.
Qed.

End interp_mrec_spec_quantr.
