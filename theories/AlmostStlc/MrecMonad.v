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


Variant void : Set := .
Global Instance voidEncodedType : EncodedType void := fun v => match v with end.


(* interp_mtree *)

(* could extend to have arbitrary constraints on E, could allow E to include other events*)
(* universe inconsistenty traces back to here, for now could specialize E to void, perhaps,
   this whole mtree idea was a holdover from when you had more complicated mfix effects *)
Definition mtree (D : Type) `{EncodedType D} (A : Type) : Type@{entree_u}:= 
   entree (D + void) A.

Global Instance mtree_monad D `{EncodedType D} : Monad (mtree D) := Monad_entree.


Definition call {D} `{EncodedType D} (d : D) : mtree D (encodes d) := trigger d.

CoFixpoint interp_mtree' {D D' R} `{EncodedType D} `{EncodedType D'}
           (bodies : forall (d : D), entree (D + void) (encodes d)) (ot : entree' (D + void) R ) : 
  entree (D' + void) R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mtree' bodies (observe t))
  | VisF (inl d) k => 
      Tau (interp_mtree' bodies (observe (EnTree.bind (bodies d) k ) ) )
  | VisF (inr v) k => Vis (@inr D' void v) (fun x => interp_mtree' bodies (observe (k x)))
  end.

Definition interp_mtree {D D' R} `{EncodedType D} `{EncodedType D'}
           (bodies : forall (d : D), entree (D + void) (encodes d)) (t : entree (D + void) R) :
  entree (D' + void) R := interp_mtree' bodies (observe t).


(* consider a more complicated mtree monad where you have a list of event types 
   and interp_mtree requires an index and can an event at that index 
*)
