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
     Ref.LetRecRefines
.

From Paco Require Import paco.

Export SigTNotations.
Import SpecMNotations.
Local Open Scope entree_scope.


(*** Definition Refinement and lr_refines_poly ***)

(* One definition refines another iff for all extensions of the recursive
functions of both sides, the bodies refine each other *)
Definition def_refines {E1 E2} RPre RPost
  (d1 : SpecDef E1) (d2 : SpecDef E2)
  (Rin : forall stk1 stk2,
      Rel (LRTInput stk1 (defLRT _ d1)) (LRTInput stk2 (defLRT _ d2)))
  (Rout : forall stk1 stk2,
      PostRel (LRTInput stk1 (defLRT _ d1)) (LRTInput stk2 (defLRT _ d2))) : Prop :=
  forall stk1 incl1 stk2 incl2 funs1 funs2 args1 args2,
    isTupleInst E1 _ stk1 incl1 (defFuns E1 d1) funs1 ->
    isTupleInst E2 _ stk2 incl2 (defFuns E2 d2) funs2 ->
    Rin _ _ args1 args2 ->
    lr_refines funs1 funs2 (liftNilRel RPre) (liftNilPostRel RPost)
      (Rout stk1 stk2 args1 args2)
      (lrtApply _ _ _ (defBody E1 d1 stk1 incl1) args1)
      (lrtApply _ _ _ (defBody E2 d2 stk2 incl2) args2).

(* An instantiation of a pair of polymorphic stack tuples *)
Record TupsInst {E1 E2 stk1 stk2}
  (pfuns1 : PolyStackTuple E1 stk1 stk1)
  (pfuns2 : PolyStackTuple E2 stk2 stk2) : Type :=
  { tupsInst_stk1 : FunStack;
    tupsInst_incl1 : stackIncl stk1 tupsInst_stk1;
    tupsInst_funs1 : StackTuple E1 tupsInst_stk1;
    tupsInst_inst1 : isTupleInst _ _ _ tupsInst_incl1 pfuns1 tupsInst_funs1;
    tupsInst_stk2 : FunStack;
    tupsInst_incl2 : stackIncl stk2 tupsInst_stk2;
    tupsInst_funs2 : StackTuple E2 tupsInst_stk2;
    tupsInst_inst2 : isTupleInst _ _ _ tupsInst_incl2 pfuns2 tupsInst_funs2; }.

(* Refinement wrt polymorphic stack tuples *)
Definition lr_refines_poly {E1 E2 stk1 stk2}
  pfuns1 pfuns2 (inst : @TupsInst E1 E2 stk1 stk2 pfuns1 pfuns2)
  RPre RPost {R1 R2} (RR : Rel R1 R2) m1 m2 : Prop :=
  lr_refines
    (tupsInst_funs1 _ _ inst) (tupsInst_funs2 _ _ inst) RPre RPost RR m1 m2.

(* lr_refines_poly can be used to prove a def_refines *)
Lemma lr_refines_poly_def_refines {E1 E2} RPre RPost
  (d1 : SpecDef E1) (d2 : SpecDef E2)
  (Rin : forall stk1 stk2,
      Rel (LRTInput stk1 (defLRT _ d1)) (LRTInput stk2 (defLRT _ d2)))
  (Rout : forall stk1 stk2,
      PostRel (LRTInput stk1 (defLRT _ d1)) (LRTInput stk2 (defLRT _ d2))) :
  (forall (inst : TupsInst (defFuns E1 d1) (defFuns E2 d2)) args1 args2,
      Rin _ _ args1 args2 ->
      lr_refines_poly (defFuns E1 d1) (defFuns E2 d2) inst
        (liftNilRel RPre) (liftNilPostRel RPost) (Rout _ _ args1 args2)
        (lrtApply _ _ _ (defBody E1 d1 _ (tupsInst_incl1 _ _ inst)) args1)
        (lrtApply _ _ _ (defBody E2 d2 _ (tupsInst_incl2 _ _ inst)) args2)) ->
  def_refines RPre RPost d1 d2 Rin Rout.
Proof.
  unfold def_refines, lr_refines_poly. intros.
  apply (H (Build_TupsInst _ _ _ _ _ _ stk1 incl1 funs1 H0 stk2 incl2 funs2 H1)).
  assumption.
Qed.

Global Instance Proper_lr_refines_poly E1 E2 stk1 stk2 pfuns1 pfuns2 inst
  RPre RPost R1 R2 RR :
  Proper (eutt eq ==> eutt eq ==> Basics.flip Basics.impl)
         (@lr_refines_poly E1 E2 stk1 stk2 pfuns1 pfuns2 inst RPre RPost R1 R2 RR).
Proof.
  repeat intro. red. rewrite H. rewrite H0. assumption.
Qed.


(*** RetS and bind laws for lr_refines_poly ***)

Section lr_refines_poly_rules.
Context {E1 E2 : EncType} {stk1 stk2 : FunStack}.
Context (pfuns1 : PolyStackTuple E1 stk1 stk1)
  (pfuns2 : PolyStackTuple E2 stk2 stk2) (inst : TupsInst pfuns1 pfuns2).

Context (RPre : SpecPreRel E1 E2 (tupsInst_stk1 _ _ inst) (tupsInst_stk2 _ _ inst)).
Context (RPost : SpecPostRel E1 E2 (tupsInst_stk1 _ _ inst) (tupsInst_stk2 _ _ inst)).
Context R1 R2 (RR : Rel R1 R2).

Lemma lr_refines_poly_ret r1 r2 : RR r1 r2 ->
  lr_refines_poly pfuns1 pfuns2 inst RPre RPost RR (RetS r1) (RetS r2).
Proof.
  intros. red. pstep. apply lr_refinesF_Ret. assumption.
Qed.

Lemma lr_refines_poly_ret_bind_r A
  (t1 : SpecM E1 _ R1) r (k2 : A -> SpecM E2 _ R2) :
  lr_refines_poly pfuns1 pfuns2 inst RPre RPost RR t1 (k2 r) ->
  lr_refines_poly pfuns1 pfuns2 inst RPre RPost RR t1 (RetS r >>= k2).
Proof.
  intros; setoid_rewrite bind_ret_l; assumption.
Qed.

Lemma lr_refines_poly_ret_bind_l A
      (k1 : A -> SpecM E1 _ R1) r (t2 : SpecM E2 _ R2) :
  lr_refines_poly pfuns1 pfuns2 inst RPre RPost RR (k1 r) t2 ->
  lr_refines_poly pfuns1 pfuns2 inst RPre RPost RR (RetS r >>= k1) t2.
Proof.
  intros; setoid_rewrite bind_ret_l; assumption.
Qed.

Lemma lr_refines_poly_bind_bind_r A1 A2
      (t1 : SpecM E1 _ R1) (t2 : SpecM E2 _ A1)
      (k1 : A1 -> SpecM E2 _ A2) (k2 : A2 -> SpecM E2 _ R2) :
  lr_refines_poly pfuns1 pfuns2 inst RPre RPost RR t1 (t2 >>= (fun a => k1 a >>= k2)) ->
  lr_refines_poly pfuns1 pfuns2 inst RPre RPost RR t1 ((t2 >>= k1) >>= k2).
Proof.
  intros; setoid_rewrite bind_bind; assumption.
Qed.

Lemma lr_refines_poly_bind_bind_l A1 A2
      (t1 : SpecM E1 _ A1) (k1 : A1 -> SpecM E1 _ A2)
      (k2 : A2 -> SpecM E1 _ R1) (t2 : SpecM E2 _ R2) :
  lr_refines_poly pfuns1 pfuns2 inst RPre RPost RR (t1 >>= (fun a => k1 a >>= k2)) t2 ->
  lr_refines_poly pfuns1 pfuns2 inst RPre RPost RR ((t1 >>= k1) >>= k2) t2.
Proof.
  intros; setoid_rewrite bind_bind; assumption.
Qed.


(*
FIXME:
- Prove the discharge lemma for lr_refines_poly
- Write total_spec and prove lr_refines_poly for it
- Update the easy lemmas (e.g., about binds) from Automation.v to use lr_refines_poly
- Write and prove the lr_refines_poly rule(s) for CallS
- Update all the automation
*)
