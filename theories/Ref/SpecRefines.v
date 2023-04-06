From Coq Require Export
     Datatypes
     Arith.PeanoNat
     Arith.Peano_dec
     Arith.Compare
     Wf_nat
     Morphisms
     Setoid
     Program.Equality
     Lists.List
     Logic.Eqdep_dec
     Logic.EqdepFacts
     Eqdep EqdepFacts
     Logic.ProofIrrelevance
     Bool.Sumbool
.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Basics.QuantType
     Core.EnTreeDefinition
     Core.SubEvent
     Ref.EnTreeSpecDefinition
     Ref.EnTreeSpecFacts
     Ref.EnTreeSpecCombinatorFacts
     Ref.RecSpecFix
     Ref.SpecM
     Eq.Eqit
     Ref.MRecSpec
     Ref.SpecMFacts
.

From Paco Require Import paco.

Export SigTNotations.

Import SpecMNotations.
Local Open Scope entree_scope.

(* FIXME: move to SpecM.v *)
Definition SpecM' (E:EncType) stack A : Type :=
  entree_spec' (FunStackE E stack) A.


Section refines.

Context {E1 E2 : EncType} {stk1 stk2 : FunStack} {R1 R2 : Type}.
Context (funs1 : FrameTuple E1 stk1) (funs2 : FrameTuple E2 stk2).

Context (RPre : Rel (FunStackE E1 stk1) (FunStackE E2 stk2))
  (RPost : PostRel (FunStackE E1 stk1) (FunStackE E2 stk2))
  (RR : R1 -> R2 -> Prop).

Inductive spec_refinesF (sim : SpecM E1 stk1 R1 -> SpecM E2 stk2 R2 -> Prop) : SpecM' E1 stk1 R1 -> SpecM' E2 stk2 R2 -> Prop :=

(* Ret |= Ret *)
| spec_refinesF_Ret r1 r2 : RR r1 r2 -> spec_refinesF sim (RetF r1) (RetF r2)

(* t1 |= t2 => Tau t1 |= Tau t2 *)
| spec_refinesF_Tau t1 t2 : sim t1 t2 -> spec_refinesF sim (TauF t1) (TauF t2)

(* RPre e1 e2 -> (forall a b, RPost e1 e2 a b -> k1 a |= k2 b) ->
   Vis e1 k1 |= Vis e2 k2 *)
| spec_refinesF_Vis e1 e2 k1 k2 : RPre e1 e2 -> (forall a b, RPost e1 e2 a b -> sim (k1 a) (k2 b) ) ->
                               spec_refinesF sim (VisF (Spec_vis e1) k1) (VisF (Spec_vis e2) k2)

(* t1 |= t2 => Tau t1 |= t2 *)
| spec_refinesF_TauL t1 ot2 : spec_refinesF sim (observe t1) ot2 ->
                              spec_refinesF sim (TauF t1) ot2

(* t1 |= t2 => t1 |= Tau t2 *)
| spec_refinesF_TauR ot1 t2 : spec_refinesF sim ot1 (observe t2) ->
                              spec_refinesF sim ot1 (TauF t2)

(* (forall a, t1 |= k a) => t1 |= Forall k *)
| spec_refinesF_forallR A ot1 k : (forall a, spec_refinesF sim ot1 (observe (k a))) ->
                                  spec_refinesF sim ot1 (VisF (Spec_forall A) k)

(* (exists a, t1 |= k a) => t1 |= Exists k *)
| spec_refinesF_existsR A ot1 k a : spec_refinesF sim ot1 (observe (k a)) ->
                                    spec_refinesF sim ot1 (VisF (Spec_exists A) k)

(* (exists a, k a |= t2) => Forall k |= t2 *)
| spec_refinesF_forallL A ot2 k a : spec_refinesF sim (observe (k a)) ot2 ->
                                    spec_refinesF sim (VisF (Spec_forall A) k ) ot2

(* (forall a, k a |= t2) => Exists k |= t2 *)
| spec_refinesF_existsL A ot2 k : (forall a, spec_refinesF sim (observe (k a)) ot2) -> spec_refinesF sim (VisF (Spec_exists A) k) ot2

(* apply funs1 call1 >>= k1 |= t2 => CallS call1 >>= k1 |= t2 *)
| spec_refinesF_unfoldL call1 k1 ot2 :
    spec_refinesF sim (observe (applyFrameTuple E1 stk1 funs1 call1 >>= k1)) ot2 ->
    spec_refinesF sim (VisF (Spec_vis (inl call1)) k1) ot2

(* t1 |= apply funs2 call2 >>= k2 => t1 |= CallS call2 >>= k2 *)
| spec_refinesF_unfoldR ot1 call2 k2 :
    spec_refinesF sim ot1 (observe (applyFrameTuple E2 stk2 funs2 call2 >>= k2)) ->
    spec_refinesF sim ot1 (VisF (Spec_vis (inl call2)) k2)
.

Hint Constructors spec_refinesF : entree_spec.

Definition spec_refines_ sim : SpecM E1 stk1 R1 -> SpecM E2 stk2 R2 -> Prop :=
  fun t1 t2 => spec_refinesF sim (observe t1) (observe t2).

Lemma monotone_spec_refinesF ot1 ot2 sim sim' (LE : sim <2= sim')
      (IN : spec_refinesF sim ot1 ot2) : spec_refinesF sim' ot1 ot2.
Proof with eauto with entree_spec.
  induction IN...
Qed.

Lemma monotone_spec_refines_: monotone2 spec_refines_.
Proof. red. intros. eapply monotone_spec_refinesF; eauto. Qed.

Hint Resolve monotone_spec_refines_ : paco.

Definition refines := paco2 spec_refines_ bot2.

End refines.

