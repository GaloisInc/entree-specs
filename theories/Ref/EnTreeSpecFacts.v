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
     Ref.MRecSpec
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


Theorem padded_refines_bind (E1 E2 : Type) `{EncodedType E1} `{EncodedType E2} (R1 R2 S1 S2: Type)
        (RPre : Rel E1 E2) (RPost : PostRel E1 E2) (RR : Rel R1 R2) (RS : Rel S1 S2) 
        (t1 : entree_spec E1 R1) (t2 : entree_spec E2 R2)
        (k1 : R1 -> entree_spec E1 S1) (k2 : R2 -> entree_spec E2 S2) :
  padded_refines RPre RPost RR t1 t2 ->
  (forall r1 r2, RR r1 r2 -> padded_refines RPre RPost RS (k1 r1) (k2 r2)) ->
  padded_refines RPre RPost RS (EnTree.bind t1 k1) (EnTree.bind t2 k2).
Admitted.


Theorem padded_refines_iter (E1 E2 : Type) `{EncodedType E1} `{EncodedType E2} (R1 R2 S1 S2: Type)
        (RPre : Rel E1 E2) (RPost : PostRel E1 E2) (RR : Rel R1 R2) (RS : Rel S1 S2) 
        (body1 : R1 -> entree_spec E1 (R1 + S1)) (body2 : R2 -> entree_spec E2 (R2 + S2)) r1 r2:
  (forall r1 r2, RR r1 r2 -> padded_refines RPre RPost (sum_rel RR RS) (body1 r1) (body2 r2) ) ->
  RR r1 r2 ->
  padded_refines RPre RPost RS (EnTree.iter body1 r1) (EnTree.iter body2 r2).
Admitted.

Section padded_refines_mrec.
Context (D1 D2 E1 E2 : Type) `{EncodedType D1} `{EncodedType D2} `{EncodedType E1} `{EncodedType E2}.
Context (bodies1 : forall (d1 : D1), entree_spec (D1 + E1) (encodes d1) ).
Context (bodies2 : forall (d2 : D2), entree_spec (D2 + E2) (encodes d2) ).
Context (RPreInv : Rel D1 D2) (RPre : Rel E1 E2) (RPostInv : PostRel D1 D2) (RPost : PostRel E1 E2).

Context (Hbodies : forall d1 d2, RPreInv d1 d2 -> 
        padded_refines (sum_rel RPreInv RPre) (SumPostRel RPostInv RPost) (RPostInv d1 d2) 
          (bodies1 d1) (bodies2 d2) ).

Theorem padded_refines_mrec d1 d2 : RPreInv d1 d2 ->
                                    padded_refines RPre RPost (RPostInv d1 d2) 
                                                   (mrec_spec bodies1 d1) (mrec_spec bodies2 d2).
Admitted.

End padded_refines_mrec.        
