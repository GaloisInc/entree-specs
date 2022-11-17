Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.

From Coq Require Import
     Program
     Setoid
     Morphisms
     Relations.

Require Import ITree.Basics.Basics.
Require Import HeterogeneousRelations EnTreeDefinition.
Require Import Eq.Eqit.
From Paco Require Import paco.

Class ReSum (E1 E2 : Type) : Type := resum : E1 -> E2.

Class ReSumRet E1 E2 `{EncodingType E1} `{EncodingType E2} `{ReSum E1 E2} : Type :=
  resum_ret : forall (e : E1), encodes (resum e) -> encodes e.

#[global] Instance ReSum_inl E1 E2 : ReSum E1 (E1 + E2) := inl.
#[global] Instance ReSum_inr E1 E2 : ReSum E2 (E1 + E2) := inr.
#[global] Instance ReSumRet_inl E1 E2 `{EncodingType E1} `{EncodingType E2} : ReSumRet E1 (E1 + E2) :=
  fun _ e => e.
#[global] Instance ReSumRet_inr E1 E2 `{EncodingType E1} `{EncodingType E2} : ReSumRet E2 (E1 + E2) :=
  fun _ e => e.

Definition trigger {E1 E2 : Type} `{ReSumRet E1 E2}
           (e : E1) : entree E2 (encodes e) :=
  Vis (resum e) (fun x : encodes (resum e) => Ret (resum_ret e x)).

CoFixpoint resumEntree' {E1 E2 : Type} `{ReSumRet E1 E2}
           {A} (ot : entree' E1 A) : entree E2 A :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (resumEntree' (observe t))
  | VisF e k => Vis (resum e) (fun x => resumEntree' (observe (k (resum_ret e x))))
  end.

(* Use resum and resum_ret to map the events in an entree to another type *)
Definition resumEntree {E1 E2 : Type} `{ReSumRet E1 E2}
           {A} (t : entree E1 A) : entree E2 A :=
  resumEntree' (observe t).

Lemma resumEntree_Ret {E1 E2 : Type} `{ReSumRet E1 E2}
           {R} (r : R) : 
  resumEntree (Ret r) ≅ Ret r.
Proof. pstep. constructor. auto. Qed.

Lemma resumEntree_Tau  {E1 E2 : Type} `{ReSumRet E1 E2}
           {R} (t : entree E1 R) : 
  resumEntree (Tau t) ≅ Tau (resumEntree t).
Proof.
  pstep. red. cbn. constructor. left. apply Reflexive_eqit. auto.
Qed.

Lemma resumEntree_Vis {E1 E2 : Type} `{ReSumRet E1 E2}
           {R} (e : E1) (k : encodes e -> entree E1 R) : 
  resumEntree (Vis e k) ≅ Vis (resum e) (fun x => resumEntree (k (resum_ret e x))).
Proof. 
  pstep. red. cbn. constructor. left. apply Reflexive_eqit. auto.
Qed.

Lemma resumEntree_proper E1 E2 R1 R2 b1 b2 (RR : R1 -> R2 -> Prop) `{ReSumRet E1 E2} : 
  forall (t1 : entree E1 R1) (t2 : entree E1 R2),
    eqit RR b1 b2 t1 t2 -> eqit RR b1 b2 (resumEntree t1) (resumEntree t2).
Proof.
  ginit. gcofix CIH.
  intros. punfold H4. red in H4.
  unfold resumEntree. hinduction H4 before r; intros.
  - setoid_rewrite resumEntree_Ret. gstep. constructor. auto.
  - pclearbot. setoid_rewrite resumEntree_Tau. gstep. constructor.
    gfinal. eauto.
  - pclearbot. setoid_rewrite resumEntree_Vis. gstep. constructor.
    gfinal. intros. left. eapply CIH. apply REL.
  - setoid_rewrite resumEntree_Tau. inversion CHECK. subst.
    rewrite tau_euttge. eauto.
  - setoid_rewrite resumEntree_Tau. inversion CHECK. subst.
    rewrite tau_euttge. eauto.
Qed.

#[global] Instance resumEntree_proper_inst  E1 E2 R `{ReSumRet E1 E2} :
  Proper (@eq_itree E1 _ R R eq ==> @eq_itree E2 _ R R eq) resumEntree.
Proof.
  repeat intro. apply resumEntree_proper. auto.
Qed.

Lemma resumEntree_bind (E1 E2 : Type) `{ReSumRet E1 E2}
           (R S : Type) (t : entree E1 R) (k : R -> entree E1 S) :
  resumEntree (EnTree.bind t k) ≅
              EnTree.bind (resumEntree t) (fun x => resumEntree (k x)).
Proof.
  revert t. ginit. gcofix CIH.
  intros t. unfold EnTree.bind at 1, EnTree.subst at 1.
  unfold resumEntree at 2. destruct (observe t).
  - setoid_rewrite resumEntree_Ret. setoid_rewrite bind_ret_l.
    apply Reflexive_eqit_gen. auto.
  - setoid_rewrite resumEntree_Tau. setoid_rewrite bind_tau.
    gstep. constructor. gfinal. eauto.
  - setoid_rewrite resumEntree_Vis. setoid_rewrite bind_vis.
    gstep. constructor. gfinal. eauto.
Qed.
    
