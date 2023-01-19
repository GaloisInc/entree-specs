From Equations Require Import Equations Signature.

Inductive type : Type :=
  | Nat : type
  | List : type -> type
  | Pair : type -> type -> type
  | Arrow : type -> (list (list (type * type))) -> type -> type
.
Notation ctx := (list type).
Notation call_frame := (list (type * type)).
Notation mfix_ctx := (list call_frame).

Notation vtype := type.


Section type_mutind.

  Context (Pt : type -> Prop) (Pmfix : mfix_ctx -> Prop) (Pcall : call_frame -> Prop).

  Context (HNat : Pt Nat).
  Context (HList : forall t : type, Pt t -> Pt (List t)).
  Context (HPair : forall t1 t2, Pt t1 -> Pt t2 -> Pt (Pair t1 t2)).
  Context (HArrow : forall t1 MR t2, Pt t1 -> Pmfix MR -> Pt t2 -> Pt (Arrow t1 MR t2)).
  Context (Hnil1 : Pmfix nil) (Hcons1 : forall R MR, Pcall R -> Pmfix MR -> Pmfix (cons R MR)).
  Context (Hnil2 : Pcall nil) (Hcons2 : forall t1 t2 R, Pt t1 -> Pt t2 -> Pcall R -> Pcall (cons (t1, t2) R)).
  
  Equations type_mutind (t : type) : Pt t :=
    {
      type_mutind Nat := HNat;
      type_mutind (List t) := HList t (type_mutind t);
      type_mutind (Pair t1 t2) := HPair t1 t2 (type_mutind t1) (type_mutind t2);
      type_mutind (Arrow t1 MR t2) := HArrow t1 MR t2 (type_mutind t1) (mfix_mutind MR) (type_mutind t2);
    }
   where mfix_mutind (MR : mfix_ctx) : Pmfix MR :=
     {
       mfix_mutind nil := Hnil1;
       mfix_mutind (cons R MR) := Hcons1 R MR (call_frame_mutind R) (mfix_mutind MR);
     }
   where call_frame_mutind (R : call_frame) : Pcall R :=
     {
       call_frame_mutind nil := Hnil2;
       call_frame_mutind (cons (t1,t2) R) := Hcons2 t1 t2 R (type_mutind t1) (type_mutind t2) (call_frame_mutind R);
     }.

  Theorem type_mfix_mutind : (forall t, Pt t) /\ (forall MR, Pmfix MR) /\ (forall R, Pcall R).
  Proof.
    repeat split; try apply type_mutind; try apply mfix_mutind; try apply call_frame_mutind.
  Qed.

End type_mutind.
