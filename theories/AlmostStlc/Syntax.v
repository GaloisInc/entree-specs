
Require Export TypedVar.

Inductive type : Type :=
  | Nat : type
  | List : type -> type
  | Pair : type -> type -> type
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
  | term_succ Γ MR (en : term Nat Γ MR) : term Nat Γ MR
  | term_match_nat t Γ MR (en : term Nat Γ MR) (eZ : term t Γ MR) (eS : term t (Nat :: Γ) MR ) : term t Γ MR
  | term_match_list t1 t2 Γ MR (el : term (List t1) Γ MR ) (enil : term t2 Γ MR) (econs : term t2 (t1 :: List t1 :: Γ) MR) : term t2 Γ MR
  | term_pair t1 t2 Γ MR (e1 : term t1 Γ MR) (e2 : term t2 Γ MR) : term (Pair t1 t2) Γ MR
  | term_split t1 t2 t3 Γ MR (ep : term (Pair t1 t2) Γ MR) (e : term t3 (t1 :: t2 :: Γ) MR) : term t3 Γ MR

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


(* values should include const, nil cons (var?) succ of a value pair split abs (perm?) (lift?)

most important thing is that they do not include calls which enables them to be substituted safely
*)
Inductive value : type -> Type := 
  | val_const (n : nat) : value Nat
  | val_nil t : value (List t)
  | val_cons t (hv : value t) (tv : value (List t)) : value (List t)
  | val_pair t1 t2 (v1 : value t1) (v2 : value t2) : value (Pair t1 t2)
  | val_abs t1 t2 MR (e : term t2 (t1 :: nil) MR) : value (Arrow t1 MR t2)
.
Arguments val_nil {t}.
Arguments val_cons {t}.
Arguments val_pair {t1 t2}.
Arguments val_abs {t1 t2 MR}.



  (* this represents something with that has a call at the top,
     and therefore


     mfix fs in (call e) -> mfix fs in call (mfix fs in e)
     mfix fs in (call v) -> mfix fs in (f v)

     mfix fs in v -> v

   *)
(* not super convinced that this is the right way to do it *)
Inductive call MR (t2 : type) : Type := 
  | callv t1 R  (xR : var R MR)  (x : var (t1,t2) R) (v : value t1)
  (* | calls t1 R  (xR : var R MR)  (x : var (t1,t2) R) (c : call MR t1) *).
Arguments callv {_ _ _ _}.
(* Arguments calls {_ _ _ _}. *)
(*
Equations term_of_call {MR t} (c : call MR t) : term t nil MR :=
  term_of_call (@callv MR t2 t1 R xR x v) := term_call _ _ nil MR R xR x (term_of_value v);
  term_of_call (@calls MR t2 t1 R xR x c) := term_call _ _ nil MR R xR x (term_of_call c).
Transparent term_of_call.
*)
(* essential when reducing denote_bodies *)
Equations nth_body {Γ MR R t1 t2} (bodies : mfix_bodies Γ MR R) (x : var (t1, t2) R) : term t2 (t1 :: Γ) MR :=
  nth_body (mfix_bodies_cons _ _ _ _ _ e _) VarZ := e;
  nth_body (mfix_bodies_cons _ _ _ _ _ _ bodies) (VarS x) := nth_body bodies x.
(* reasoning about *)

