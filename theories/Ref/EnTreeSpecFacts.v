From Coq Require Import
     Program
     Setoid
     Morphisms
     Relations.



From ITree Require Import
     Basics.Basics
     Basics.Tacs
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


Definition padded_refines {E1 E2} `{EncodedType E1} `{EncodedType E2}
           {R1 R2 : Type} (RPre : Rel E1 E2) (RPost : PostRel E1 E2) (RR : Rel R1 R2)
           (t1 : entree_spec E1 R1) (t2 : entree_spec E2 R2) :=
  refines RPre RPost RR (pad t1) (pad t2).

Theorem padded_refines_trans (E1 E2 E3 : Type) `{EncodedType E1} `{EncodedType E2} `{EncodedType E3}
        (R1 R2 R3 : Type) (RPre1 : Rel E1 E2) (RPre2 : Rel E2 E3) (RPost1 : PostRel E1 E2)
        (RPost2 : PostRel E2 E3) (RR1 : Rel R1 R2) (RR2 : Rel R2 R3) t1 t2 t3:
  padded_refines RPre1 RPost1 RR1 t1 t2 ->
  padded_refines RPre2 RPost2 RR2 t2 t3 ->
  padded_refines (rcompose RPre1 RPre2) (RComposePostRel RPre1 RPre2 RPost1 RPost2) (rcompose RR1 RR2) t1 t3.
Admitted.
