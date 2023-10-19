
Require Export MrecMonad.
Require Export HeterogeneousRelations.
Require Export EnTreeDefinition.
Require Export Syntax.
From Coq Require Import Lists.List Logic.JMeq.

From Equations Require Import Equations Signature.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Global Instance inout_encoded T1 T2 : EncodedType (T1) :=
  fun _ => T2. 

(*
first try to see if you can get these to unify

*)

Definition denote_mfix_ctx' (MR : list (list {T : Type & EncodedType T} )) :=
  List.map (fun mr => denote_mrec_ctx mr && encoded_mrec_ctx mr ) MR.

(* this is fairly ugly and causing some unification problem maybe try more closely
   mirror how the old version did it  *)
Fixpoint denote_type (t : type) : Type@{entree_u} :=
  match t with 
  | Nat => nat
  | List t => list (denote_type t)
  | Pair t1 t2 => (denote_type t1 * denote_type t2)%type
  | Sum t1 t2 => (denote_type t1 + denote_type t2)%type
  | Arrow t1 MR t2 =>
      let MR' := List.map (
                     fun cf : call_frame => 
                         List.map (fun '(t1,t2) => 
                                     ((denote_type t1) && 
                                        (inout_encoded (denote_type t1) (denote_type t2) ) )) cf)%type 
                          MR
      in 
      denote_type t1 -> mtree (denote_mfix_ctx' MR') (denote_type t2) end.


Definition denote_mfix_ctx (MR : list (list (type * type) ) ) :=
  denote_mfix_ctx' (List.map (List.map (fun '(t1,t2) => ((denote_type t1) && 
                                        (inout_encoded (denote_type t1) (denote_type t2) ) ) ) ) MR )%type.

Definition mrec_of_call_frame (cf : call_frame) : mrec_ctx :=
  (List.map  (fun '(t1,t2) => ((denote_type t1) && 
                                        (inout_encoded (denote_type t1) (denote_type t2) ) ) ) cf).
  

Definition denote_call_frame (cf : call_frame) :=
  denote_mrec_ctx (mrec_of_call_frame cf).

Definition encodes_call_frame (cf : call_frame) : EncodedType (denote_call_frame cf) :=
  encoded_mrec_ctx (mrec_of_call_frame cf).

Fixpoint denote_ctx (Γ : ctx) : Type@{entree_u} :=
  match Γ with
  | nil => unit
  | t :: Γ' => denote_type t * denote_ctx Γ' end.

Equations index_ctx {t : type} {Γ} (x : var t Γ) (hyps : denote_ctx Γ) : denote_type t :=
  index_ctx (@VarZ x Γ') (v, _) := v;
  index_ctx (@VarS _ v1 v2 Γ' y) (_, hyps) := index_ctx y hyps.

Equations call_mrec_call_frame {t1 t2 R} (x :  var (t1, t2) R) (v : denote_type t1) : 
  {d : denote_call_frame R & encodes d -> denote_type t2} :=
  call_mrec_call_frame (@VarZ _ R) v := (inl v && id);
  call_mrec_call_frame (@VarS _ _ (t3,t4) R' y) v := 
    let '(d && f) := call_mrec_call_frame y v in
    (inr d && f).

Equations  call_mrec {t1 t2 MR R} (x : var (t1,t2) R) (y : var R MR ) (v : denote_type t1) :
          {d : denote_mrec_ctx (denote_mfix_ctx MR) & encodes d -> denote_type t2 } :=
  call_mrec x VarZ v := let '(d && f) := call_mrec_call_frame x v in
                              (inl d && f);
  call_mrec x (VarS y) v := let '(d && f) := call_mrec x y v in
                                  (inr d && f).

Definition call_term {t1 t2 MR R} (x : var (t1,t2) R) (y : var R MR ) (v : denote_type t1) 
  : mtree (denote_mfix_ctx MR) (denote_type t2) :=
let '(d && f) := call_mrec x y v in
   Functor.fmap f (EnTree.trigger d).

Definition perm_denote {MR1 MR2} (Hperm : perm MR1 MR2) : 
  perm (denote_mfix_ctx MR1) (denote_mfix_ctx MR2) :=
  perm_map (perm_map Hperm).

Equations lift_handler MR1 MR2 (d : denote_mrec_ctx (denote_mfix_ctx MR2)) :
  {d' : denote_mrec_ctx (denote_mfix_ctx (MR1 ++ MR2) ) & encodes d' -> encodes d} :=
  lift_handler nil MR2 d := (d && id);
  lift_handler (_ :: MR1) MR2 d := let '(d' && f) := lift_handler MR1 MR2 d in
                                  (inr d' && f).

Arguments lift_handler {_ _}.

Equations denote_var {cf : call_frame} {MR : mfix_ctx} (x : var cf MR) : 
  var (denote_call_frame cf && encodes_call_frame cf) (denote_mfix_ctx MR) :=
denote_var VarZ := VarZ;
denote_var (VarS y) := VarS (denote_var y).

Equations remove_denote {R : call_frame} {MR : mfix_ctx} (x : var R MR)
          (d : denote_mrec_ctx (TypedVar.remove _ _ (denote_var x))) : 
  {d' : denote_mrec_ctx (denote_mfix_ctx (TypedVar.remove R MR x) ) & encodes d' -> encodes d} :=
remove_denote VarZ d := (d && id);
remove_denote (VarS _) (inl d) := (inl d && id);
remove_denote (VarS y) (inr d) := let '(d' && f) := remove_denote y d in
                                        (inr d' && f).

Equations remove_denote' {R : call_frame} {MR : mfix_ctx} (x : var R MR)
          (d : denote_mrec_ctx (denote_mfix_ctx (TypedVar.remove R MR x) )) : 
  {d' : denote_mrec_ctx (TypedVar.remove _ _ (denote_var x)) & encodes d' -> encodes d} :=

remove_denote' VarZ d := (d && id);
remove_denote' (VarS _) (inl d) := (inl d && id);
remove_denote' (VarS y) (inr d) := let '(d' && f) := remove_denote' y d in
                                        (inr d' && f).

(*
Lemma remove_denote_jmeq R MR (x : var R MR) : 
  forall d d' f, remove_denote x d = (d' && f) -> (JMeq d' d).
Proof.
  induction x.
  - cbn. intros. simp remove_denote in H. setoid_rewrite remove_denote_equation_1 in H.
    injection H. intros. subst. auto.
  - intros. destruct d.
    + simp remove_denote in H. injection H. intros. subst. constructor. setoid_rewrite remove_denote_equation_2 in H.
 intros.
*)
(*
Equations denote_term {t : type} (Γ : ctx) (MR : mfix_ctx) (e : term t Γ MR) (hyps : denote_ctx Γ)
  : mtree (denote_mfix_ctx MR) (denote_type t) :=
  denote_term Γ MR (term_const n _ _) _ := ret n;

  denote_term Γ MR (term_nil _ _ _) _ := ret nil;

  denote_term Γ MR (term_cons _ _ _ eh et) hyps := vh <- denote_term Γ MR eh hyps;;
                                              vt <- denote_term Γ MR et hyps;;
                                              ret (vh :: vt);

  denote_term Γ MR (term_succ Γ MR en) hyps := vn <- denote_term Γ MR en hyps;;
                                               ret (S vn);

  denote_term Γ MR (term_match_nat t _ _ en eZ eS) hyps := 
    n <- denote_term Γ MR en hyps;;
    match n with
    | 0 => denote_term Γ MR eZ hyps
    | S m => denote_term (Nat :: Γ) MR eS (m, hyps)
    end;

  denote_term Γ MR (term_match_list t1 t2 _ _ el enil econs) hyps := 
    l <- denote_term Γ MR el hyps;;
    match l with
    | nil => denote_term Γ MR enil hyps
    | hd :: tl => denote_term (t1 :: List t1 :: Γ) MR econs (hd, (tl, hyps))
    end;

  denote_term Γ MR (term_var _ _ _ x) hyps := ret (index_ctx x hyps);

  denote_term Γ MR (term_pair _ _ _ _ e1 e2) hyps := v1 <- denote_term Γ MR e1 hyps;;
                                                     v2 <- denote_term Γ MR e2 hyps;;
                                                     ret (v1,v2);

  denote_term Γ MR (term_split t1 t2 _ _ _ ep e) hyps := '(v1,v2) <- denote_term Γ MR ep hyps;;
                                                      denote_term (t1 :: t2 :: Γ) MR e (v1, (v2, hyps));

  denote_term Γ MR (term_app t1 t2 Γ MR ef earg) hyps := vf <- denote_term Γ MR ef hyps;;
                                                         vargs <- denote_term Γ MR earg hyps;;
                                                         vf vargs;

  denote_term Γ MR (term_abs t1 t2 Γ MR MR' e) hyps := ret (fun x : denote_type t1 => denote_term (t1 :: Γ) MR' e (x, hyps));

  denote_term Γ MR2 (term_perm t Γ MR1 MR2 Hperm e) hyps :=
    map_perm (denote_mfix_ctx  MR1) (denote_mfix_ctx MR2) (perm_denote Hperm) (denote_term _ _ e hyps);

  denote_term Γ MR2 (term_lift t Γ MR1 MR2 e) hyps := mapE lift_handler (denote_term Γ MR2 e hyps);

  denote_term Γ MR (term_call t1 t2 Γ MR R x y e) hyps := v <- denote_term Γ MR e hyps;;
                                                          call_term y x v;

  denote_term Γ MR (term_mfix t Γ R MR x bodies e) hyps := 
    mapE (remove_denote x) (interp_mtree _ _ _ (denote_var x) (denote_bodies Γ MR R bodies hyps) (denote_term Γ MR e hyps));
where denote_bodies (Γ : ctx) (MR : mfix_ctx) (R : call_frame) (bodies : mfix_bodies Γ MR R) 
                    (hyps : denote_ctx Γ) (arg : denote_call_frame R)  : 
  mtree (denote_mfix_ctx MR) (encodes arg) by struct bodies :=
  denote_bodies Γ' MR' ((t1,t2) :: R') (mfix_bodies_cons Γ' MR' t1 t2 R' ebody bodies') hyps' (inl arg') :=
    denote_term _ _ ebody (arg', hyps');

  denote_bodies Γ' MR' ((t1,t2) :: R') (mfix_bodies_cons Γ' MR' t1 t2 R' ebody bodies') hyps' (inr arg') :=
    denote_bodies _ _ _ bodies' hyps' arg'.

Arguments denote_term {_ _ _}.
Arguments term_const (_) {_ _}.
Arguments term_cons {_ _ _}.
Arguments term_nil {_ _ _}.
Arguments term_var {_ _ _}.
Arguments term_succ {_ _}.
Arguments term_match_nat {_ _ _}.
Arguments term_match_list {_ _ _ _}.
Arguments term_pair {_ _ _ _}.
Arguments term_split {_ _ _ _ _}.
Arguments term_app {_ _ _ _}.
Arguments term_abs {_ _ _ _ _}.
Arguments term_perm {_ _ _ _}.
Arguments term_call {_ _ _ _ _}.
Arguments term_mfix {_ _} (_) {_}.
Arguments mfix_bodies_nil {_ _}.
Arguments mfix_bodies_cons {_ _ _ _ _}.
Arguments term_lift {_ _} (_) {_}.


*)
