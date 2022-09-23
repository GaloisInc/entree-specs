Require Export TypedVar.

Inductive type : Type :=
  | Nat : type
  | List : type -> type
  | Arrow : type -> (list (list (type * type))) -> type -> type
.
Notation ctx := (list type).
Notation call_frame := (list (type * type)).
Notation mfix_ctx := (list call_frame).



(*TODO : add some basic natural number operations *)
Inductive term : type -> ctx -> mfix_ctx -> Type := 
  | term_const (n : nat) Γ MR : term Nat Γ MR
  | term_nil t Γ MR : term (List t) Γ MR
  | term_cons t Γ MR (head : term t Γ MR) (tail : term (List t) Γ MR) : term (List t) Γ MR
  | term_var t Γ MR (x : var t Γ) : term t Γ MR

  | term_match_nat t Γ MR (en : term Nat Γ MR) (eZ : term t Γ MR) (eS : term t (Nat :: Γ) MR ) : term t Γ MR
  | term_match_list t1 t2 Γ MR (el : term (List t1) Γ MR ) (enil : term t2 Γ MR) (econs : term t2 (t1 :: List t1 :: Γ) MR) : term t2 Γ MR
  (* might be some subtleties in the application rule you are not sufficiently considering *)
  | term_app t1 t2 Γ MR (e1 : term (Arrow t1 MR t2) Γ MR) (e2 : term t1 Γ MR) : term t2 Γ MR
  (* same here *)
  | term_abs t1 t2 Γ MR MR' (e : term t2 (t1 :: Γ) MR') : term (Arrow t1 MR' t2) Γ MR
  | term_perm t Γ MR1 MR2 (Hperm : perm MR1 MR2) (e : term t Γ MR1) : term t Γ MR2
  | term_lift t Γ MR1 MR2 (e : term t Γ MR2) : term t Γ (MR1 ++ MR2)
  | term_call t1 t2 Γ MR R (xR : var R MR) (x : var (t1,t2) R) (arg : term t1 Γ MR) : term t2 Γ MR
  | term_mfix t Γ R MR (x : var R MR) (bodies : mfix_bodies Γ MR R) (e : term t Γ MR) : term t Γ (remove R MR x)

with mfix_bodies : ctx -> mfix_ctx -> call_frame -> Type :=
  | mfix_bodies_nil Γ MR : mfix_bodies Γ MR nil
  | mfix_bodies_cons Γ MR t1 t2 R' (body : term t2 (t1 :: Γ) MR) (bodies : mfix_bodies Γ MR R') :
    mfix_bodies Γ MR ((t1,t2) :: R')
.
