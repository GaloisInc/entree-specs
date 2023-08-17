From Coq Require Import
     List.
Require Export TypedVar.
Require Export SyntaxSeq.
Open Scope list_scope.
Import ListNotations.
From Equations Require Import Equations Signature.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Coq.Program.Equality.
Import MonadNotation.
Local Open Scope monad_scope.
Derive NoConfusion for vtype.

Notation "a && b" := (existT _ a b).

Equations comp_map {t : vtype} {Γ1 Γ2} {MR : mfix_ctx} (c : comp t Γ1 MR)
          (f : forall t', var t' Γ1 -> var t' Γ2) :comp t Γ2 MR := {
    comp_map (comp_ret v) f := comp_ret (val_map v f) ;
    comp_map (comp_let c1 c2) f := comp_let (comp_map c1 f) (comp_map c2 (var_map_skip f));
    comp_map (comp_match_nat vn cZ cS) f := 
      comp_match_nat (val_map vn f) (comp_map cZ f) (comp_map cS (var_map_skip f));
    comp_map (comp_succ vn) f := comp_succ (val_map vn f);
    comp_map (comp_match_list vl cnil ccons) f :=
      comp_match_list (val_map vl f) (comp_map cnil f) (comp_map ccons (var_map_skip (var_map_skip f)));
    comp_map (comp_split vp cs) f :=
      comp_split (val_map vp f) (comp_map cs (var_map_skip (var_map_skip f)) );
    comp_map (comp_app v1 v2) f :=
      comp_app (val_map v1 f) (val_map v2 f);
    comp_map (comp_call xR x v) f := comp_call xR x (val_map v f);
    comp_map (comp_mfix R bodies c) f := comp_mfix R (bodies_map bodies f) (comp_map c f);
    comp_map (comp_lift c) f := comp_lift (comp_map c f);
    comp_map (comp_perm Hperm c) f := comp_perm Hperm (comp_map c f);
  }

where val_map {t : vtype} {Γ1 Γ2} (v : value t Γ1)
               (f : forall t', var t' Γ1 -> var t' Γ2) : value t Γ2 := {
    val_map (val_const n) f := val_const n;
    (* val_map (val_succ vn) f := val_succ (val_map vn f); *)
    val_map val_nil f := val_nil;
    val_map (val_cons vh vt) f := val_cons (val_map vh f) (val_map vt f);
    val_map (val_pair v1 v2) f := val_pair (val_map v1 f) (val_map v2 f);
    val_map (val_abs cbody) f := val_abs (comp_map cbody (var_map_skip f));
    val_map (val_var x) f := val_var (f _ x);
 }
where bodies_map {Γ1 Γ2} {MR R R'} (bodies : mfix_bodies Γ1 MR R R')
                 (f : forall t', var t' Γ1 -> var t' Γ2) : mfix_bodies Γ2 MR R R' := {
    bodies_map mfix_bodies_nil f := mfix_bodies_nil;
    bodies_map (mfix_bodies_cons body bodies) f := mfix_bodies_cons (comp_map body (var_map_skip f)) (bodies_map bodies f);
}

.

Definition exchange_comp MR G1 G2 G3 (u1 u2 t: vtype)
      (e : comp t (G1 ++ [u1] ++ G2 ++ [u2] ++ G3) MR) : 
      comp t (G1 ++ [u2] ++ G2 ++ [u1] ++ G3) MR :=
  comp_map e (fun t' x => perm_var x (exchange_var_perm G1 G2 G3 u1 u2)).
Definition weaken_l_comp MR G1 G2 t (e : comp t G2 MR ) : comp t (G1 ++ G2) MR
  := comp_map e (fun t' e' => weaken_var_l _ _ t' e').
Definition weaken_l_comp_single MR t1 G2 t (e : comp t G2 MR ) : comp t (t1 :: G2) MR :=
  weaken_l_comp MR [t1] G2 t e.

Definition weaken_l_value {t Γ2} Γ1 (v : value t Γ2) : value t (Γ1 ++ Γ2) :=
  val_map v (weaken_var_l _ _).
Definition weaken_l_value_single {t1 Γ2 t} (v : value t Γ2) : value t (t1 :: Γ2) :=
  weaken_l_value [t1] v.

Definition weaken_l_bodies {R MR G1 G2} (bodies : mfix_bodies G2 MR R R) : mfix_bodies (G1 ++ G2) MR R R :=
  bodies_map bodies (fun t' e' => weaken_var_l _ _ t' e').

Definition weaken_l_bodies_single {R MR G t} (bodies : mfix_bodies G MR R R) : mfix_bodies (t :: G) MR R R:=
  @weaken_l_bodies _ _ [t] G bodies.
Definition weaken_r_bodies {R MR G1 G2} (bodies : mfix_bodies G1 MR R R) : mfix_bodies (G1 ++ G2) MR R R :=
  bodies_map bodies (fun t' c' => weaken_var_r _ _ t' c').
Definition weaken_r_comp MR G1 G2 t (e : comp t G1 MR ) : comp t (G1 ++ G2) MR
  := comp_map e (fun t' e' => weaken_var_r _ _ t' e').
Definition weaken_r_value {Γ1 t} Γ2 (e : value t Γ1) : value t (Γ1 ++ Γ2) :=
  val_map e (weaken_var_r _ _).
Definition weaken_mid_comp MR G1 G2 G3 t (e : comp t (G1 ++ G3) MR) : comp t (G1 ++ G2 ++ G3) MR
  := comp_map e (fun t' e' => weaken_var_mid _ _ _ t' e').

Equations subst_var {t u} (Γ1 Γ2 : ctx) (v : value t Γ2) (x : var u (Γ1 ++ [t] ++ Γ2)) : 
  value u (Γ1 ++ Γ2) :=
  subst_var (t1 :: Γ1) _ v VarZ := val_var VarZ;
  subst_var (t1 :: Γ1) Γ2 v (VarS y) := weaken_l_value_single (subst_var Γ1 Γ2 v y);
  subst_var nil Γ2 v VarZ := v;
  subst_var nil (t1 :: Γ2) v (VarS y) := val_var y.

Equations subst_comp {t u Γ2 MR} Γ1 (c1 : comp u (Γ1 ++ [t] ++ Γ2) MR) (v : value t Γ2) :
  comp u (Γ1 ++ Γ2) MR := {
    subst_comp _ (comp_ret vr) v := comp_ret (subst_value vr v);
    subst_comp _ (comp_let c1 c2) v := comp_let (subst_comp _ c1 v) (subst_comp (_ :: _) c2 v);
    subst_comp _ (comp_match_nat vn cZ cS) v := 
      comp_match_nat (subst_value vn v) (subst_comp _ cZ v) (subst_comp (_ :: _) cS v);
    subst_comp _ (comp_succ vn) v :=
      comp_succ (subst_value vn v);
    subst_comp _ (comp_match_list vl cnil ccons) v :=
      comp_match_list (subst_value vl v) (subst_comp _ cnil v) (subst_comp (_ :: _ :: _) ccons v); 
    subst_comp _ (comp_split vp cs) v :=
      comp_split (subst_value vp v) (subst_comp (_ :: _ :: _) cs v );
    subst_comp _ (comp_app vf varg) v :=
      comp_app (subst_value vf v) (subst_value varg v);
    subst_comp _ (comp_call xR x varg) v :=
      comp_call xR x (subst_value varg v);
    subst_comp _ (comp_mfix R bodies c) v :=
      comp_mfix R (subst_bodies bodies v) (subst_comp _ c v);
    subst_comp _ (comp_lift c) v := comp_lift (subst_comp _ c v);
    subst_comp _ (comp_perm Hperm c) v := comp_perm Hperm (subst_comp _ c v);
}
where subst_value {t u Γ1 Γ2} (v1 : value u (Γ1 ++ [t] ++ Γ2) ) (v : value t Γ2) :
  value u (Γ1 ++ Γ2) := {
    subst_value (val_const n) _ := val_const n;
    (* subst_value (val_succ vn) v := val_succ (subst_value vn v); *)
    subst_value val_nil _ := val_nil;
    subst_value (val_cons vh vt) v := val_cons (subst_value vh v) (subst_value vt v);
    subst_value (val_pair v1 v2) v := val_pair (subst_value v1 v) (subst_value v2 v);
    subst_value (val_abs cbody) v := val_abs (subst_comp (_ ::_) (cbody) v);
    subst_value (val_var x) v := subst_var _ _ v x;
}
where subst_bodies {t R R' Γ1 Γ2 MR} (bodies : mfix_bodies (Γ1 ++ [t] ++ Γ2) MR R R') (v : value t Γ2) :
  mfix_bodies (Γ1 ++ Γ2) MR R R' := {
    subst_bodies mfix_bodies_nil _ := mfix_bodies_nil;
    subst_bodies (mfix_bodies_cons body bodies) v := 
      mfix_bodies_cons (subst_comp (_ :: _) body v) (subst_bodies bodies v);
}.
Definition subst_comp_cons {t u Γ MR} (c : comp u (t :: Γ) MR ) (v : value t Γ) : comp u Γ MR :=
  subst_comp [] c v.
Arguments subst_comp {_ _ _ _ _}.

Definition subst_value_cons {t u Γ} (v : value u (t :: Γ)) (v0 : value t Γ) := subst_value (Γ1 := []) v v0.

Definition subst_bodies_cons {t R R' Γ MR} (bodies : mfix_bodies (t :: Γ) MR R R') (v : value t Γ) :
  mfix_bodies Γ MR R R' :=
  subst_bodies (Γ1 := []) bodies v.

Inductive bredex : vtype -> mfix_ctx -> Type :=
  | bredex_let t1 t2 MR (v : closed_value t1) (c : comp t2 [t1] MR ) : bredex t2 MR
  | bredex_app t1 t2 MR (cbody : comp t2 [t1] MR) (varg : closed_value t1) : bredex t2 MR
  | bredex_match_nat t MR (n : nat) (cZ : comp t [] MR) (cS : comp t [Nat] MR) : bredex t MR
  | bredex_succ MR (n : nat) : bredex Nat MR
  | bredex_match_list t1 t2 MR (vl : closed_value (List t1)) (cnil : comp t2 [] MR) (ccons : comp t2 [t1; List t1] MR) :
    bredex t2 MR
  | bredex_split t1 t2 t3 MR (vp : closed_value (Pair t1 t2)) (cs : comp t3 [t1; t2] MR) : 
    bredex t3 MR
  | bredex_mfix t MR R (bodies : mfix_bodies [] MR R R) (v : closed_value t) : 
    bredex t MR
  | bredex_perm t MR1 MR2 (Hperm : perm MR1 MR2) (v : closed_value t) :
    bredex t MR2
  | bredex_lift t MR1 MR2 (v : closed_value t) : 
    bredex t (MR1 ++ MR2)
.
Arguments bredex_succ {MR}.
Arguments bredex_let {t1 t2 MR}.
Arguments bredex_app {t1 t2 MR}.
Arguments bredex_match_nat {t MR}.
Arguments bredex_match_list {t1 t2 MR}.
Arguments bredex_split {t1 t2 t3 MR}.
Arguments bredex_mfix {t MR}.
Arguments bredex_perm {t MR1 MR2}.
Arguments bredex_lift {t MR1 MR2}.


Inductive call (t2 : vtype) (MR : mfix_ctx) : Type :=
  callv t1 R (xR : var R MR) (x : var (t1,t2) R) (v : closed_value t1).
Arguments callv {_ _ _ _}.
(* I think I could rewrite this definition to exclude stuck calls,
   first step is to only associate the exposedness boolean with calls (that is already all it is used for 
   and then add a second boolean for coveredness

   and then we have two ev_hole constructors, one for bredexes that ignored coveredness
     one for calls that 

)

 *)
Inductive eval_context : vtype -> mfix_ctx -> forall t MR, bredex t MR + call t MR -> bool -> Type := 
  | ev_hole t MR (r : bredex t MR + call t MR) : eval_context t MR t MR r true
  | ev_let b t1 t2 t3 MR1 MR2 (r : bredex t3 MR2 + call t3 MR2) (E : eval_context t1 MR1 _ _ r b) (c : comp t2 [t1] MR1) : 
    eval_context t2 MR1 _ _ r b
  | ev_mfix b t1 t2 R MR1 MR2 (r : bredex t2 MR2 + call t2 MR2) 
            (bodies : mfix_bodies [] MR1 R R)
            (E : eval_context t1 (R :: MR1) _ _ r b) :
    eval_context t1 MR1 _ _ r false
  | ev_perm b t1 t2 MR1 MR2 MR3 (r : bredex t2 MR3 + call t2 MR3)
            (Hperm : perm MR1 MR2)
            (E : eval_context t1 MR1 _ _ r b) : 
    eval_context t1 MR2 _ _ r false
  | ev_lift b t1 t2 MR1 MR2 MR3 (r : bredex t2 MR3 + call t2 MR3)
            (E : eval_context t1 MR2 _ _ r b) :
    eval_context t1 (MR1 ++ MR2) _ _ r false
.
Arguments eval_context (_ _) {_ _}.
Arguments ev_hole {t MR r}.
Arguments ev_let {b t1 t2 t3 MR1 MR2 r}.
Arguments ev_mfix (b) {t1 t2} (R) {MR1 MR2 r}.
Arguments ev_perm (b) {t1 t2 MR1 MR2 MR3 r}.
Arguments ev_lift (b) {t1 t2 MR1 MR2 MR3 r}.


Equations normalize_eval_context {t1 t2 MR1 MR2} (ca : call t2 MR2)
          (E : eval_context t1 MR1 (inr ca) true) : 
  {ca : call t2 MR1 & eval_context t1 MR1 (inr ca) true} :=
  normalize_eval_context ca ev_hole := ca && ev_hole;
  normalize_eval_context ca (ev_let E c) :=
    let '(ca' && E') := normalize_eval_context ca E in
    ca' && (ev_let E' c).


Equations step_bredex {t MR} (br : bredex t MR) : comp t [] MR :=
  step_bredex (bredex_succ n) := comp_ret (val_const (S n));
  step_bredex (bredex_let v c) := subst_comp_cons c v;
  step_bredex (bredex_app cbody varg) := subst_comp_cons cbody varg;
  step_bredex (bredex_match_nat n cZ cS) := 
    match n with
    | 0 => cZ
    | S m => subst_comp_cons cS (val_const m) end;
  step_bredex (bredex_match_list val_nil cnil _) := cnil;
  step_bredex (bredex_match_list (val_cons vh vt) _ ccons) :=
    subst_comp_cons (subst_comp_cons ccons (weaken_l_value_single vh)) vt;
  step_bredex (bredex_split (val_pair v1 v2) cs) :=
    subst_comp_cons (subst_comp_cons cs (weaken_l_value_single v1)) v2;
  step_bredex (bredex_mfix _ _ v) := comp_ret v;
  step_bredex (bredex_perm _ v) := comp_ret v;
  step_bredex (bredex_lift v) := comp_ret v.

Equations subst_eval_context {b t1 t2 MR1 MR2} {r : bredex t2 MR2 + call t2 MR2} (E : eval_context t1 MR1 r b)
          (c : comp t2 [] MR2 ) : comp t1 [] MR1 :=
  subst_eval_context ev_hole c := c;
  subst_eval_context (ev_let E1 c2) c := comp_let (subst_eval_context E1 c) c2;
  subst_eval_context (ev_mfix _ R bodies E) c := comp_mfix R bodies (subst_eval_context E c);
  subst_eval_context (ev_perm _ Hperm E) c := comp_perm Hperm (subst_eval_context E c);
  subst_eval_context (ev_lift _ E) c := comp_lift (subst_eval_context E c).

Equations subst_eval_context_ctx {b t1 t2 MR1 MR2 Γ} {r : bredex t2 MR2 + call t2 MR2} (E : eval_context t1 MR1 r b)
          (c : comp t2 Γ MR2 ) : comp t1 Γ MR1 :=
  subst_eval_context_ctx ev_hole c := c;
  subst_eval_context_ctx (ev_let E1 c2) c := 
    comp_let (subst_eval_context_ctx E1 c) (weaken_r_comp _ _ _ _ c2);
  subst_eval_context_ctx (ev_mfix _ R bodies E) c := 
    comp_mfix R (weaken_r_bodies bodies) (subst_eval_context_ctx E c);
  subst_eval_context_ctx (ev_perm _ Hperm E) c := comp_perm Hperm (subst_eval_context_ctx E c);
  subst_eval_context_ctx (ev_lift _ E) c := comp_lift (subst_eval_context_ctx E c).


(* weird error here *)
Equations push_eval_context {t1 t2 MR1 MR2} (r : bredex t2 MR1 + call t2 MR1)
          (E : eval_context t1 MR1 r true)
          (f : forall t Γ, comp t Γ MR1 -> comp t Γ MR2)
          (c : comp t2 [] MR2) : comp t1 [] MR2 :=
  push_eval_context r ev_hole f c := c;
  push_eval_context r (ev_let E1 c2) f c := comp_let (push_eval_context r E1 f c) (f _ [_] c2).

Definition comp_mfix_map {MR R} (bodies : mfix_bodies [] MR R R) : forall t Γ, comp t Γ (R :: MR) -> comp t Γ MR :=
  fun t Γ c => comp_mfix R (weaken_r_bodies bodies) c.
Definition comp_lift_map {MR1 MR2} : forall t Γ, comp t Γ MR2 -> comp t Γ (MR1 ++ MR2) :=
  fun t Γ c => comp_lift c.
Definition comp_perm_map {MR1 MR2} (Hperm : perm MR1 MR2) : forall t Γ, comp t Γ MR1 -> comp t Γ MR2 :=
  fun t Γ c => comp_perm Hperm c.

Instance option_monad : Monad option :=
  {|
    ret := fun _ x => Some x;
    bind := fun _ _ m k =>
              match m with
              | None => None
              | Some x => k x end;
  |}.


(* may need to enrich this type, replace the failure with 
   some kind of evalutation context thing 
 *)
Equations step_eval_context {t1 t2 MR1 MR2} b (r : bredex t2 MR2 + call t2 MR2) (E : eval_context t1 MR1 r b) :
  option (comp t1 [] MR1) :=
  step_eval_context _ (inl br) E := ret (subst_eval_context E (step_bredex br));
  step_eval_context _ (inr ca) (ev_mfix true R bodies E) := 
    let '( (callv yR x v) && E' ) := normalize_eval_context ca E in
    ret (
        match (var_eq_neq _ _ (R :: MR1) VarZ yR) with
        | inl Heq =>
            let fx := nth_body bodies (var_eq_elim VarZ yR Heq x) in
            let c := subst_comp_cons fx v in
            comp_mfix R bodies (subst_eval_context E' c )
        | inr Hneq =>
            let yR' := remove_var _ _ _ VarZ yR Hneq in
            push_eval_context (inr (callv yR x v)) E' (comp_mfix_map bodies)
                              (comp_call yR' x v) 
        end
      );

  step_eval_context _ (inr ca) (ev_mfix false xR bodies E) := 
    c <- step_eval_context _ (inr ca) E;;
    ret (comp_mfix xR bodies c);

  step_eval_context _ (inr ca) (ev_lift true E) :=
    let '( (callv yR x v) && E' ) := normalize_eval_context ca E in
    ret (
        push_eval_context _ E' comp_lift_map
                          (comp_call (weaken_var_l _ _ _ yR) x v)
      );

  step_eval_context _ (inr ca) (ev_lift false E) :=
    c <- step_eval_context _ (inr ca) E;;
    ret (comp_lift c);

  step_eval_context _ (inr ca) (ev_perm true Hperm E) :=
    let '( (callv yR x v) && E' ) := normalize_eval_context ca E in
    ret (
        push_eval_context _ E' (comp_perm_map Hperm)
                          (comp_call (perm_var yR Hperm) x v )
      );

  step_eval_context _ (inr ca) (ev_perm false Hperm E) :=
    c <- step_eval_context _ (inr ca) E;;
    ret (comp_perm Hperm c);

  step_eval_context _ (inr ca) ev_hole := error;

  step_eval_context _ (inr ca) (ev_let E c2) :=
    c1 <- step_eval_context _ _ E;;
    ret (comp_let c1 c2).


Inductive boxed_eval_context t MR : Type :=
  | bec t' MR' (b : bool) (r : bredex t' MR' + call t' MR') (E : eval_context t MR r b).
Arguments bec {_ _ _ _ _}.
Definition bec_of_bredex {t MR} (br : bredex t MR) : boxed_eval_context t MR :=
  bec (inl br) ev_hole.


Equations observe {t MR} (c : comp t [] MR) : boxed_eval_context t MR + closed_value t :=
  observe (comp_ret v) := inr v;
  observe (comp_let c1 c2) :=
    match observe c1 with
    | inl (bec r E) => inl (bec r (ev_let E c2))
    | inr v1 => inl (bec_of_bredex (bredex_let v1 c2) )
    end;
  observe (comp_match_nat (val_const n) cZ cS ) :=
    inl (bec_of_bredex (bredex_match_nat n cZ cS) );
  observe (comp_succ (val_const n)) :=
    inl (bec_of_bredex (bredex_succ n));
  observe (comp_match_list vl cnil ccons) :=
    inl (bec_of_bredex (bredex_match_list vl cnil ccons) );
  observe (comp_split vp cs) :=
    inl (bec_of_bredex (bredex_split vp cs) );
  observe (comp_app (val_abs cbody) varg) :=
    inl (bec_of_bredex (bredex_app cbody varg) );
  (* this case is the only one which can get stuck *)
  observe (comp_call xR x v) :=
    inl (bec (inr (callv xR x v) ) ev_hole );
  observe (comp_mfix xR bodies c) :=
    match observe c with
    | inl (bec r E) => inl (bec r (ev_mfix _ xR bodies E))
    | inr v => inl (bec_of_bredex (bredex_mfix xR bodies v) )
    end;
  observe (comp_lift c) :=
    match observe c with
    | inl (bec r E) => inl (bec r (ev_lift _ E) )
    | inr v => inl (bec_of_bredex (bredex_lift v))
    end;
  observe (comp_perm Hperm c) := 
    match observe c with
    | inl (bec r E) => inl (bec r (ev_perm _ Hperm E))
    | inr v => inl (bec_of_bredex (bredex_perm Hperm v) )
  end
.

Definition step {t MR} (c : comp t [] MR) : option (comp t [] MR) + closed_value t :=
  match observe c with
  | inl (bec r E) => inl (step_eval_context _ r E)
  | inr v => inr v 
  end.


Inductive step_rel {t MR} : comp t [] MR -> comp t [] MR -> Prop :=
  step_rel_intro c c' : step c = inl (Some c') -> step_rel c c'.

(* this definition might be wrong*)
Inductive eval_rel {t MR} : comp t [] MR -> closed_value t -> Prop :=
  | eval_rel_step c1 c2 c3 : step_rel c1 c2 -> eval_rel c2 c3 -> eval_rel c1 c3
  | eval_rel_val c v : step c = inr v -> eval_rel c v
.
