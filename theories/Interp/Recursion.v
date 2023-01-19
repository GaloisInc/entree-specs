Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.

Require Import ITree.Basics.Basics.
Require Import HeterogeneousRelations.

Require Export EnTreeDefinition.
Require Export SubEvent.


Section interp_mrec.

Context {D E : Type} `{enc1 : EncodedType D} `{enc2 : EncodedType E}.

CoFixpoint interp_mrec' {R} (bodies : forall d : D, entree (D + E) (encodes d)) 
           (ot : entree' (D + E) R) : entree E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mrec' bodies (observe t))
  | VisF (inl d) k => Tau (interp_mrec' bodies (observe (bind (bodies d) k)))
  | VisF (inr e) k => Vis e (fun x => interp_mrec' bodies (observe (k x)))
  end.

Definition interp_mrec {R} (bodies : forall d : D, entree (D + E) (encodes d)) 
           (t : entree (D + E) R) : entree E R :=
  interp_mrec' bodies (observe t).

Definition mrec (bodies : forall d : D, entree (D + E) (encodes d))
           (d : D) : entree E (encodes d) :=
  interp_mrec bodies (trigger d).

End interp_mrec. 
