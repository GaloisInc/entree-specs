Require Export TypedVar.
Require Export Types.


Inductive value : vtype -> ctx -> Type :=
  | val_const (n : nat) Γ : value Nat Γ
  | val_nil t Γ : value (List t) Γ
  | val_cons t Γ (vh : value t Γ) (vt : value (List t) Γ) : value (List t) Γ
  | val_pair t1 t2 Γ (v1 : value t1 Γ) (v2 : value t2 Γ) : value (Pair t1 t2) Γ
  | val_abs t1 t2 Γ MR (cbody : comp t2 (t1 :: Γ) MR) : value (Arrow t1 MR t2) Γ
  | val_var t Γ (x : var t Γ) : value t Γ

with comp : vtype -> ctx -> mfix_ctx -> Type :=
  | comp_ret t Γ MR (v : value t Γ) : comp t Γ MR
  | comp_let t1 t2 Γ MR (c1 : comp t1 Γ MR) (c2 : comp t2 (t1 :: Γ) MR) : 
    comp t2 Γ MR
  | comp_match_nat t Γ MR (vn : value Nat Γ) (cZ : comp t Γ MR) (cS : comp t (Nat :: Γ) MR) :
    comp t Γ MR
  | comp_succ Γ MR (vn : value Nat Γ) : comp Nat Γ MR
  | comp_match_list t1 t2 Γ MR (vl : value (List t1) Γ) (cnil : comp t2 Γ MR)
                    (cS : comp t2 (t1 :: (List t1) :: Γ ) MR) :
    comp t2 Γ MR
  | comp_split t1 t2 t3 Γ MR (vp : value (Pair t1 t2) Γ) (es : comp t3 (t1 :: t2 :: Γ) MR) :
    comp t3 Γ MR
  | comp_app t1 t2 Γ MR (vf : value (Arrow t1 MR t2) Γ) (varg : value t1 Γ) : 
    comp t2 Γ MR
  | comp_call t1 t2 Γ MR R (xR : var R MR) (x : var (t1,t2) R) (v : value t1 Γ) : 
    comp t2 Γ MR
  | comp_mfix t Γ MR R (bodies : mfix_bodies Γ MR R R) (c : comp t Γ (R :: MR)) :
    comp t Γ MR
  | comp_lift t Γ MR1 MR2 (c : comp t Γ MR2) : comp t Γ (MR1 ++ MR2)
  | comp_perm t Γ MR1 MR2 (Hperm : perm MR1 MR2) (e : comp t Γ MR1) :
    comp t Γ MR2
with mfix_bodies : ctx -> mfix_ctx -> call_frame -> call_frame -> Type := 
  | mfix_bodies_nil Γ MR R : mfix_bodies Γ MR R nil
  | mfix_bodies_cons Γ MR t1 t2 R R' (body : comp t2 (t1 :: Γ) (R :: MR)) (bodies : mfix_bodies Γ MR R R') :
    mfix_bodies Γ MR R ((t1,t2) :: R')
.

Scheme value_mind := Induction for value Sort Prop
  with comp_mind := Induction for comp Sort Prop
  with mfix_bodies_mind := Induction for mfix_bodies Sort Prop.
Combined Scheme comp_value_mutind from comp_mind, value_mind, mfix_bodies_mind.

Arguments val_const n {_}.
Arguments val_nil {_ _}.
Arguments val_cons {_ _}.
Arguments val_pair {_ _ _}.
Arguments val_abs {_ _ _ _}.
Arguments val_var {_ _}.
Arguments comp_ret {_ _ _}.
Arguments comp_let {_ _ _ _}.
Arguments comp_match_nat {_ _ _}.
Arguments comp_succ {_ _}.
Arguments comp_match_list {_ _ _ _}.
Arguments comp_split {_ _ _ _ _}.
Arguments comp_app {_ _ _ _}.
Arguments comp_call {_ _ _ _ _}.
Arguments comp_mfix {_ _ _}.
Arguments comp_lift {_ _ _ _}.
Arguments comp_perm {_ _ _ _}.
Arguments mfix_bodies_nil {_ _ _}.
Arguments mfix_bodies_cons {_ _ _ _ _ _}.

Equations nth_body {Γ MR R R' t1 t2} (bodies : mfix_bodies Γ MR R R') (x : var (t1, t2) R') : comp t2 (t1 :: Γ) (R :: MR) :=
  nth_body (mfix_bodies_cons e _) VarZ := e;
  nth_body (mfix_bodies_cons _ bodies) (VarS x) := nth_body bodies x.


Definition closed_value (t : vtype) : Type := value t nil.
