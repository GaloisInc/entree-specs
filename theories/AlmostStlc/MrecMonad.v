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


(* could extend to have arbitrary constraints on E, could allow E to include other events*)
(* universe inconsistenty traces back to here, for now could specialize E to void, perhaps,
   this whole mtree idea was a holdover from when you had more complicated mfix effects *)
Definition mtree (D : Type) `{EncodedType D} (A : Type) : Type@{entree_u}:= 
  forall E `(EncodedType E), entree (D + E) A.

Global Instance mtree_monad D `{EncodedType D} : Monad (mtree D) :=
 {|
   ret := fun _ a E encodes => ret a;
   bind := fun _ _ m k E encodes => EnTree.bind (m E encodes) (fun a => k a E encodes)
 |}.


Definition call {D} `{EncodedType D} (d : D) : mtree D (encodes d) :=
  fun _ _ => trigger d.

CoFixpoint interp_mtree' {D D' E R} `{EncodedType D} `{EncodedType D'} `{EncodedType E}
           (bodies : forall (d : D), entree (D + E) (encodes d)) (ot : entree' (D + E) R ) : 
  entree (D' + E) R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mtree' bodies (observe t))
  | VisF (inl d) k => 
      Tau (interp_mtree' bodies (observe (EnTree.bind (bodies d) k ) ) )
  | VisF (inr e) k => Vis (@inr D' E e) (fun x => interp_mtree' bodies (observe (k x)))
  end.

Definition interp_mtree {D D' E R} `{EncodedType D} `{EncodedType D'} `{EncodedType E}
           (bodies : forall (d : D), entree (D + E) (encodes d)) (t : entree (D + E) R) :
  entree (D' + E) R := interp_mtree' bodies (observe t).


Definition resolve {D D' R} `{EncodedType D} `{EncodedType D'} 
           (bodies : forall (d : D), mtree D (encodes d)) (m : mtree D R) : mtree D' R :=
fun E encodes => interp_mtree (fun d => bodies d E encodes) (m E encodes).



(* define monad structure*)
