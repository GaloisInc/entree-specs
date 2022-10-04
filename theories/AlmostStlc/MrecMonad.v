From Coq Require Import
     Program
     Setoid
     Morphisms
     Relations.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Tacs
     Basics.HeterogeneousRelations
     Eq.Paco2.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Core.SubEvent
.

Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.

Require Import ITree.Basics.Basics.

Require Export TypedVar.

From Equations Require Import Equations Signature.

Variant void : Set := .
Global Instance voidEncodedType : EncodedType void := fun v => match v with end.

Notation "a && b" := (existT _ a b).

Notation mrec_ctx := (list {T : Type & EncodedType T}).

Fixpoint denote_mrec_ctx (MR : mrec_ctx) : Type@{entree_u} :=
  match MR with
  | nil => void
  | cons (T && _) MR => T + denote_mrec_ctx MR 
  end.

Fixpoint encoded_mrec_ctx (MR : mrec_ctx) : EncodedType (denote_mrec_ctx MR) :=
  match MR with
  | nil => fun _ => void
  | cons (T1 && encodes) MR =>
      fun x => match x with
            | inl y => encodes y
            | inr y => encoded_mrec_ctx MR y
            end
  end.

Global Instance encoded_mrec_ctx_instance MR : EncodedType (denote_mrec_ctx MR) := encoded_mrec_ctx MR.

Definition mtree MR A : Type@{entree_u} :=
  entree (denote_mrec_ctx MR) A.
Notation mtree' MR A := (entree' (denote_mrec_ctx MR) A).

Equations bring_to_front (MR : mrec_ctx) {In : Type} {Out : EncodedType In}
          (x : var (In && Out) MR)
          (e : denote_mrec_ctx MR) :
  {e' : (In + denote_mrec_ctx (remove (In && Out) MR x )) & encodes e' -> encodes e } :=
bring_to_front ((In && Out) :: MR) (VarZ _ MR ) (inl i) := (inl i && id);
bring_to_front ((In && Out) :: MR) (VarZ _ MR ) (inr e) := (inr e && id);
bring_to_front ((T1 && T2) :: MR) (VarS  _ MR y) (inl i) := (inr (inl i) && id );
bring_to_front ((T1 && T2) :: MR) (VarS _ _ MR y) (inr e) :=
  match bring_to_front MR y e with
  | ((inl i) && f) => inl i && f
  | ((inr e) && f) => (inr (inr e)) && f end.
(*

Equations bring_to_front {A : Type} (MR : mrec_ctx) (In : Type) (Out : EncodedType In)
          (x : var (In && Out) MR)
          (e : denote_mrec_ctx MR)
          (k : encodes e -> A)
  : {i : In & encodes i -> A} + {e : denote_mrec_ctx (remove (In && Out) MR x) & encodes e -> A}   :=
  bring_to_front ((In && Out) :: MR) In Out (VarZ _ MR) (inl i) k :=
    inl (i && k);
  bring_to_front ((In && Out) :: MR) In Out (VarZ _ MR) (inr e) k := inr (e && k);
  bring_to_front ((T1 && T2) :: MR) In Out (VarS _ _ MR y) (inl i) k := inr ((inl i) && k);
  bring_to_front ((T1 && T2) :: MR) In Out (VarS _ _ MR y) (inr e) k :=
    match bring_to_front MR In Out y e k with
    | inl (i && k ) => inl (i && k)
    | inr (e && k) => inr ((inr e) && k )
    end.

Lemma bring_to_front_k_inl_jmeq : forall A MR In Out (x : var (In && Out) MR) (e : denote_mrec_ctx MR) (k : encodes e -> A) i k',
    bring_to_front MR In Out x e k = inl (i && k') -> k ~= k'.
Proof.
  intros A R In Out x. dependent induction x.
  - intros [ | ]; intros; try discriminate.
    simp bring_to_front in H. injection H. intros. subst. apply inj_pair2 in H0. subst. auto.
  - destruct b. cbn. intros [ | ]; try discriminate.
    simp bring_to_front. intros. eapply IHx; eauto. Unshelve. all : auto.
    simp bring_to_front in H. destruct (bring_to_front l In Out x d k) as [ | ]; destruct s; try discriminate.
    injection H. intros. subst. apply inj_pair2 in H0. subst. auto.
Qed.


Lemma bring_to_front_k_inr_jmeq : forall A MR In Out (x : var (In && Out) MR) (e : denote_mrec_ctx MR) (k : encodes e -> A) e' k',
    bring_to_front MR In Out x e k = inr (e' && k') -> k ~= k'.
Proof.
  intros A R In Out x. dependent induction x.
  - intros [ | ]; intros; try discriminate. simp bring_to_front in H.
    cbn in *.  setoid_rewrite bring_to_front_equation_3 in H.
    injection H. intros. subst. dependent destruction H0. auto.
  - destruct b. cbn in *. intros [ | ]; intros; try discriminate.
    + intros. simp bring_to_front in H. injection H. intros. subst.
      match goal with H : inr ?a1 = inr ?a2 |- _ => remember a1 as ek1; remember a2 as ek2; 
                                                  assert (ek1 = ek2) end.
      injection H. intros; auto.
      rewrite Heqek1 in H0. rewrite Heqek2 in H0.
      apply inj_pair2 in H0. subst. auto.
    + cbn in H. simp remove in *. simp bring_to_front in H.
      destruct (bring_to_front l In Out x d k ) as [ | ] eqn :Heq; destruct s; try discriminate.
      injection H. intros. subst. eapply IHx; eauto.
      rewrite Heq.
      match goal with H : inr ?a1 = inr ?a2 |- _ => remember a1 as ek1; remember a2 as ek2; 
                                                  assert (ek1 = ek2) end.
      { injection H. auto. }
      clear H. rewrite Heqek1 in H0. rewrite Heqek2 in H0.
      apply inj_pair2 in H0. subst. auto.
Qed.

Lemma bring_to_front_e_inl :  forall A MR In Out (x : var (In && Out) MR) (e : denote_mrec_ctx MR) (k1 k2 : encodes e -> A)
                                i1 i2 k1' k2',
    bring_to_front MR In Out x e k1 = inl (i1 && k1') -> bring_to_front MR In Out x e k2 = inl (i2 && k2') ->
    i1 = i2.
Proof.
  intros A MR In Out x. dependent induction x.
  - intros [ | ]; intros; try discriminate. simp bring_to_front in H, H0.
    injection H. injection H0. intros. subst. auto.
  - destruct b. cbn in *. intros [ | ]; intros; try discriminate.
     simp bring_to_front in H, H0. 
     destruct (bring_to_front l In Out x d k1) eqn : Heq1; destruct s; try discriminate.
     destruct (bring_to_front l In Out x d k2) eqn : Heq2; destruct s; try discriminate.
     injection H. injection H0. intros. subst. eapply IHx; eauto.
Qed.

Lemma bring_to_front_e_inr :  forall A MR In Out (x : var (In && Out) MR) (e : denote_mrec_ctx MR) (k1 k2 : encodes e -> A)
                                e1 e2 k1' k2',
    bring_to_front MR In Out x e k1 = inr (e1 && k1') -> bring_to_front MR In Out x e k2 = inr (e2 && k2') ->
    e1 = e2.
Proof.
  intros A MR In Out x. dependent induction x.
  - intros [ | ]; intros; try discriminate. simp bring_to_front in H, H0.
    injection H. injection H0. intros. subst. auto.
  - destruct b. cbn in *. intros [ | ]; intros; try discriminate.
    + simp bring_to_front in H, H0. injection H. injection H0. intros. subst. auto.
    + simp bring_to_front in H, H0.
      destruct (bring_to_front l In Out x d k1) eqn : Heq1; destruct s; try discriminate.
      destruct (bring_to_front l In Out x d k2) eqn : Heq2; destruct s; try discriminate.
      injection H. injection H0. intros. subst. eapply IHx in Heq1; eauto. subst.
      auto.
Qed.

Lemma bring_to_front_e_contra : forall A MR In Out (x : var (In && Out) MR) (e : denote_mrec_ctx MR) (k1 k2 : encodes e -> A)
                                i1 e2 k1' k2',
    bring_to_front MR In Out x e k1 = inl (i1 && k1') ->
    bring_to_front MR In Out x e k2 = inr (e2 && k2') -> False.
Proof.
  intros A MR In Out x. dependent induction x.
  - intros [ | ]; intros; try discriminate.
  - destruct b. intros [ | ]; intros; try discriminate. simp bring_to_front in H, H0.
    destruct (bring_to_front l In Out x d k1) eqn : Heq1; destruct s; try discriminate.
    destruct (bring_to_front l In Out x d k2) eqn : Heq2; destruct s; try discriminate.
    injection H0. intros. subst. injection H. intros. subst. eapply IHx in Heq1; eauto.
Qed.
    

(* Lemma bring_to_front_encodes : forall A MR In Out (x : var (In && Out) MR) (e : denote_mrec_ctx MR) k e k',
    bring_to_front MR In Out x e k = *)
*)
Section interp_mtree.
Context (MR : mrec_ctx) (In : Type) (Out : EncodedType In) (x : var (In && Out) MR) {A : Type}.

Context (body : forall i : In, mtree MR (encodes i)).

CoFixpoint interp_mtree' (om : mtree' MR A) : mtree (remove (In && Out) MR x) A :=
  match om with
  | RetF r => Ret r
  | TauF t => Tau (interp_mtree' (observe t))
  | VisF e k => 
      match bring_to_front MR x e with
      | inl i && f => Tau (interp_mtree' (observe (EnTree.bind (body i) (fun x => k (f x)) )) )
      | inr e' && f => Vis e' (fun x => interp_mtree' (observe (k (f x)) ) )
      end 
  end.


Definition interp_mtree (m : mtree MR A) : mtree (remove (In && Out) MR x) A :=
  interp_mtree' (observe m).

End interp_mtree.


Definition handler (D1 D2 : Type) `{EncodedType D1} `{EncodedType D2}  :=
  forall (d : D1), {d' : D2 & encodes d' -> encodes d}.

CoFixpoint mapE' {D1 D2 R} `{EncodedType D1} `{EncodedType D2} (h : handler D1 D2)
           (ot : entree' D1 R) : entree D2 R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (mapE' h (observe t))
  | VisF d k => let '(d' && f) := h d in
               Vis d' (fun x => mapE' h (observe (k (f x))))
  end.

Definition mapE {D1 D2 R} `{EncodedType D1} `{EncodedType D2} (h : handler D1 D2)
           (t : entree D1 R) : entree D2 R :=
  mapE' h (observe t).

(* another function that builds very slowly *)
Equations perm_handler (MR1 MR2 : mrec_ctx) (Hperm : perm MR1 MR2)
          (d : denote_mrec_ctx MR1) : {d' : denote_mrec_ctx MR2 & encodes d' -> encodes d} :=
  perm_handler nil nil perm_nil v := match v : void with end;
  perm_handler ((T1 && T2) :: MR1) ((T1 && T2) :: MR2) (perm_skip _ MR1 MR2 Hperm)
               (inl i) := (inl i && id);
  perm_handler ((T1 && T2) :: MR1) ((T1 && T2) :: MR2) (perm_skip _ MR1 MR2 Hperm)
               (inr d) := let '(d' && f) := perm_handler MR1 MR2 Hperm d in
                          (inr d' && f);
  perm_handler _ _ (perm_swap _ _ _ _ Hperm)
               (inl i) := (inr (inl i) && id);
  perm_handler _ _ (perm_swap _ _ _ _ Hperm)
               (inr (inl i)) := (inl i && id);
  perm_handler _ _ (perm_swap _ _ MR1 MR2 Hperm)
               (inr (inr d)) := let '(d' && f) := perm_handler MR1 MR2 Hperm d in
                                (inr (inr d') && f );
  perm_handler MR1 MR3 (perm_trans MR1 MR2 MR3 Hp12 Hp23) d1 :=
    let '(d2 && f12) := perm_handler MR1 MR2 Hp12 d1 in
    let '(d3 && f23) := perm_handler MR2 MR3 Hp23 d2 in
    (d3 && (fun x => f12 (f23 x) )).

Definition map_perm MR1 MR2 (Hperm : perm MR1 MR2) {A} (m : mtree MR1 A) :
  mtree MR2 A :=
  mapE (perm_handler MR1 MR2 Hperm) m.

Equations concat_handler (MR1 MR2 : mrec_ctx) (d : denote_mrec_ctx MR2) :
          {d' : denote_mrec_ctx (MR1 ++ MR2) & encodes d' -> encodes d } :=
  concat_handler nil MR2 d := (d && id);
  concat_handler ((T1 && T2) :: MR1 ) MR2 d :=
    let '(d' && f) := concat_handler MR1 MR2 d in
    (inr d' && f).

Definition map_concat MR1 MR2 {A} (m : mtree MR2 A) : mtree (MR1 ++ MR2) A :=
  mapE (concat_handler MR1 MR2) m.


Global Instance Monad_mtree MR : (Monad (mtree MR)) := Monad_entree.

Equations call {MR T1} {T2 : EncodedType T1} (x : var (T1 && T2) MR) (v : T1) : 
  {d : denote_mrec_ctx MR & encodes d -> encodes v} :=
  call (VarZ _ _) v := (inl v && id);
  call (VarS _ (_ && _) _ y) v := let '(d && f) := call y v in
                           (inr d && f).

Definition callm {MR T1} {T2 : EncodedType T1} (x : var (T1 && T2) MR) (v : T1) : 
  mtree MR (encodes v) :=
  let '(d && f) := call x v in
  bind (EnTree.trigger d) (fun x => Ret (f x)).


Inductive position {T1 T2} : forall {MR : mrec_ctx}, var (T1 && T2) MR -> T1 -> denote_mrec_ctx MR -> Prop := 
| pos_varZ MR v : position (VarZ _ MR) v (inl v)
| pos_varS T1' T2' MR v e y : position y v e -> position (VarS _ (T1' && T2') MR y) v (inr e)
.

Lemma call_position {MR T1} {T2 : EncodedType T1} (x : var (T1 && T2) MR) : 
  forall v : T1 , position x v (projT1 (call x v)).
Proof.
  dependent induction x.
  - intros. simp call. constructor.
  - destruct b. intros. simp call. 
    specialize (IHx T1 T2 x eq_refl JMeq_refl v).
    destruct (call x v). constructor. auto.
Qed.

Lemma bring_to_front_position {MR In Out} (x : var (In && Out) MR) (i : In) (e : denote_mrec_ctx MR) : 
  position x i e -> projT1 (bring_to_front MR x e) = inl i.
Proof.
  intro Hpos. dependent induction Hpos.
  - simp bring_to_front. auto. 
  - simp bring_to_front. destruct (bring_to_front MR y e).
    destruct x; try discriminate. cbn in *. injection IHHpos. intros. subst.
    auto.
Qed.

Lemma bring_to_front_call {MR In Out} (x : var (In && Out) MR) (v : In) : 
  projT1 (bring_to_front MR x (projT1 (call x v))) = inl v.
Proof.
  apply bring_to_front_position. apply call_position.
Qed.

Lemma call_cont {MR T1} {T2 : EncodedType T1} (x : var (T1 && T2) MR) (v : T1) : 
  projT2 (call x v) ~= (@id (encodes v)).
Proof.
  revert v. dependent induction x.
  - intros. simp call. auto.
  - destruct b. intros. simp call. 
    specialize (IHx T1 T2 x eq_refl JMeq_refl v). destruct (call x v).
    auto.
Qed.

Lemma bring_to_front_cont {MR In Out} (x : var (In && Out) MR) (i : In) (e : denote_mrec_ctx MR) : 
  projT2 (bring_to_front MR x e) ~= (@id (encodes e)).
Proof.
  revert e. dependent induction x.
  - intros [ | ]; simp bring_to_front; auto.
  - destruct b. intros [ | ]; simp bring_to_front; auto.
    specialize (IHx In Out x eq_refl JMeq_refl i d).
    destruct (bring_to_front l x d). cbn in *. destruct x1; auto.
Qed.
(*
Lemma bring_to_front_call_cont {MR In Out} (x : var (In && Out) MR) (v : In) : 
  projT2 (bring_to_front MR x (projT1 (call x v)))
*)

(* made progress need to also need to know that 
   e; e0 is id, definitely true
*)
