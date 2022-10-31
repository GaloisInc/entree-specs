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
     SubEvent
.
Print Instances ReSum. Locate trigger.
Locate ReSum.
From Paco Require Import paco.

Local Open Scope entree_scope.


End spec_fix.
