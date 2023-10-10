Require Export MrecMonad.
Require Export HeterogeneousRelations.
Require Export EnTreeDefinition.
Require Export Denotation.
Require Export SyntaxSeq.
Require Export Recursion.
From Coq Require Import Lists.List Logic.JMeq.

From Equations Require Import Equations Signature.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Equations denote_comp {t Γ MR} (c : comp t Γ MR) (hyps : denote_ctx Γ) :
  mtree (denote_mfix_ctx MR) (denote_type t) := {
    denote_comp (comp_ret v) hyps := denote_value v hyps;
    denote_comp (comp_let c1 c2) hyps :=
      v <- denote_comp c1 hyps;;
      denote_comp c2 (v,hyps);
    denote_comp (comp_match_nat vn eZ eS) hyps :=
      n <- denote_value vn hyps;;
      match n with
      | 0 => denote_comp eZ hyps
      | S m => denote_comp eS (m, hyps)
      end;
    denote_comp (comp_match_list vl enil econs) hyps :=
      l <- denote_value vl hyps;;
      match l with
      | nil => denote_comp enil hyps
      | h :: t => denote_comp econs (h, (t, hyps))
      end;
    denote_comp (comp_succ vn) hyps :=
      n <- denote_value vn hyps;;
      ret (S n);
    denote_comp (comp_split vp es) hyps :=
      '(v1,v2) <- denote_value vp hyps;;
      denote_comp es (v1, (v2, hyps));
    denote_comp (comp_app vf varg) hyps :=
      vf' <- denote_value vf hyps;;
      varg' <- denote_value varg hyps;;
      Tau (vf' varg');
    denote_comp (comp_call xR x varg) hyps :=
      varg' <- denote_value varg hyps;;
      call_term x xR varg';
    denote_comp (comp_lift c) hyps :=
      mapE lift_handler (denote_comp c hyps);
    denote_comp (comp_perm Hperm c) hyps :=
      map_perm _ _ (perm_denote Hperm) (denote_comp c hyps);

    denote_comp (comp_mfix R bodies c) hyps := 
      interp_mrec (denote_bodies bodies hyps) (denote_comp c hyps);
  }
where denote_value {t Γ MR} (v : value t Γ) (hyps : denote_ctx Γ) : 
  mtree (denote_mfix_ctx MR) (denote_type t) := {
    denote_value (val_const n) _ := ret n;
    denote_value val_nil _ := ret nil;
    denote_value (val_cons vh vt) hyps :=
      vh' <- denote_value vh hyps;;
      vt' <- denote_value vt hyps;;
      ret (cons vh' vt');
    denote_value (val_pair v1 v2) hyps :=
      v1' <- denote_value v1 hyps;;
      v2' <- denote_value v2 hyps;;
      ret (v1',v2');
    denote_value (val_abs cbody) hyps :=
      ret (fun x => denote_comp cbody (x,hyps));
    denote_value (val_var x) hyps := ret (index_ctx x hyps);
}
where denote_bodies {Γ MR R1 R2} (bodies : mfix_bodies Γ MR R1 R2) 
                    (hyps : denote_ctx Γ) (arg : denote_call_frame R2)  : 
  mtree (denote_mfix_ctx (R1 :: MR)) (encodes arg) := {
  denote_bodies (mfix_bodies_cons body _) hyps (inl arg) :=
    denote_comp body (arg, hyps);
  denote_bodies (mfix_bodies_cons _ bodies) hyps (inr arg) :=
    denote_bodies bodies hyps arg
}.
