From Coq Require Import
     Program
     Setoid
     Morphisms
     Relations.



From ITree Require Import
     Basics.Basics
     Basics.Utils
     Basics.HeterogeneousRelations
 .
From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Eq.Eqit
     Ref.Padded
     Ref.EnTreeSpecDefinition
.

From Paco Require Import paco.

Local Open Scope entree_scope.

Section mrec.
Context {D E} `{EncodingType D} `{EncodingType E}.
Context (bodies : forall (d : D), entree (D + E) (encodes d) ).
CoFixpoint interp_mrec' {R} (ot : entree' (D + E) R) : entree E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mrec' (observe t) )
  | VisF ((inl d)) k => Tau (interp_mrec' (observe (EnTree.bind (bodies d) k )) )
  | VisF ((inr e)) k => Vis e (fun x => interp_mrec' (observe (k x))) 
  end.
Definition interp_mrec {R} (t : entree (D + E) R) : entree E R :=
  interp_mrec' (observe t).
Definition mrec (d : D) := interp_mrec (bodies d).

End mrec.

Section mrec_spec.
Context {D E} `{EncodingType D} `{EncodingType E}.
Context (bodies : forall (d : D), entree_spec (D + E) (encodes d) ).
CoFixpoint interp_mrec_spec' {R} (ot : entree_spec' (D + E) R) : entree_spec E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mrec_spec' (observe t) )
  | VisF (Spec_vis (inl d)) k => Tau (interp_mrec_spec' (observe (EnTree.bind (bodies d) k )) )
  | VisF (Spec_vis (inr e)) k => Vis (Spec_vis e) (fun x => interp_mrec_spec' (observe (k x))) 
  | VisF (Spec_forall _) k => Vis (@Spec_forall E _) (fun x => interp_mrec_spec' (observe (k x)))
  | VisF (Spec_exists _) k => Vis (@Spec_exists E _) (fun x => interp_mrec_spec' (observe (k x)))
end.
Definition interp_mrec_spec {R} (t : entree_spec (D + E) R) : entree_spec E R :=
  interp_mrec_spec' (observe t).
Definition mrec_spec (d : D) := interp_mrec_spec (bodies d).

End mrec_spec.

Variant callE (A B : Type@{entree_u}) : Type@{entree_u} := Call (a : A).
#[global] Instance callE_encodes {A B} : EncodingType (callE A B) :=
  fun _ => B.
