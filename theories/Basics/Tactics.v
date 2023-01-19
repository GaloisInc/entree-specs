Require Import Logic.Eqdep.

Ltac inj_existT := 
  repeat match goal with 
         | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H 
         end.
