Require Export Syntax.
Require Export TypedVar.
From Equations Require Import Equations Signature.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.

From Coq Require Import
     List.
Open Scope list_scope.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Arguments VarZ {_ _ _}.
Arguments VarS {_ _ _ _}.

Definition weaken_var_r {A} : forall (l1 l2 : list A) (a : A), var a l1 -> var a (l1 ++ l2) := @append_var A.

Equations weaken_var_l {A} (l1 l2 : list A) (a : A) (x : var a l2) : var a (l1 ++ l2) :=
  weaken_var_l nil l2 a x := x;
  weaken_var_l (b :: l1) l2 a x := VarS (weaken_var_l l1 l2 a x). 
Transparent weaken_var_l.
Equations swap_var {A} (l: list A) (a b c: A) (x : var a ([b] ++ [c] ++ l) ) :
  var a ([c] ++ [b] ++ l) :=
  swap_var l a a c VarZ :=  VarS VarZ;
  swap_var l a b a (VarS VarZ) := VarZ;
  swap_var l a b c (VarS (VarS y) ) := VarS (VarS y).


Equations weaken_var_mid {A} (l1 l2 l3 : list A) (a : A) (x : var a (l1 ++ l3) ) :
  var a (l1 ++ l2 ++ l3)  :=
  weaken_var_mid (b :: l1) _ _ b VarZ := VarZ;
  weaken_var_mid (b :: l1) l2 l3 a (VarS y) := VarS (weaken_var_mid _ _ _ a y);
  weaken_var_mid nil l2 l3 a y := weaken_var_l l2 l3 a y.


Arguments perm_trans {_ _ _ _}.
Arguments perm_swap {_ _ _ _ _}.
Arguments perm_refl {_ _ }.
Arguments perm_skip {_ _ _ _}.
Arguments perm_var {_ _ _ _}.
Equations exchange_var_r_perm {A} (l1 l2 : list A) (a b : A) : 
  perm ([a] ++ l1 ++ [b] ++ l2) ([b] ++ l1 ++ [a] ++ l2) :=
  exchange_var_r_perm [] l2 a b := perm_swap perm_refl;
  exchange_var_r_perm (c :: l1) l2 a b :=
    let IHl2 := exchange_var_r_perm l1 l2 a b in
    perm_trans (perm_swap perm_refl) (perm_trans (perm_skip IHl2) (perm_swap perm_refl)).

Equations exchange_var_perm {A} (G1 G2 G3 : list A) (u1 u2 : A) :
  perm (G1 ++ [u1] ++ G2 ++ [u2] ++ G3) (G1 ++ [u2] ++ G2 ++ [u1] ++ G3 ) :=
  exchange_var_perm [] G2 G3 u1 u2 := exchange_var_r_perm G2 G3 u1 u2;
  exchange_var_perm (c :: G1) G2 G3 u1 u2 :=
    perm_skip (exchange_var_perm G1 G2 G3 u1 u2).

Definition exchange_var {A} (G1 G2 G3 : list A) (u1 u2 t : A) 
           (x : var t (G1 ++ [u1] ++ G2 ++ [u2] ++ G3)) : 
  var t (G1 ++ [u2] ++ G2 ++ [u1] ++ G3 ) :=
  perm_var x (exchange_var_perm G1 G2 G3 u1 u2).

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


Scheme term_mind := Induction for term Sort Type
  with mfix_bodies_mind := Induction for mfix_bodies Sort Type.

Combined Scheme term_mfix_bodies_mutind from term_mind, mfix_bodies_mind.


Equations var_map_skip {A} (l1 l2 : list A) (b : A) (f : forall c, var c l1 -> var c l2) a
          (x : var a (b :: l1)) : var a (b :: l2) :=
  var_map_skip l1 l2 _ _ f VarZ := VarZ;
  var_map_skip l1 l2 _ _ f (VarS y) := VarS (f _ y).

Arguments var_map_skip {_ _ _ _}.

Equations term_map {t : type} {G1 G2 : ctx} {MR : mfix_ctx} (e : term t G1 MR) 
          (f : forall t', var t' G1 -> var t' G2) : term t G2 MR :=
  term_map (term_const n) f := term_const n;
  term_map term_nil f := term_nil;
  term_map (term_cons eh et) f := term_cons (term_map eh f) (term_map et f);
  term_map (term_var x) f := term_var (f _ x);
  term_map (term_succ en) f := term_succ (term_map en f);
  term_map (term_match_nat en eZ eS) f :=
    term_match_nat (term_map en f) (term_map eZ f) 
                   (term_map eS (var_map_skip f));
  term_map (term_match_list el enil econs) f :=
    term_match_list (term_map  el f) (term_map enil f)
                    (term_map econs (var_map_skip (var_map_skip f)));
  term_map (term_pair e1 e2) f:=
    term_pair (term_map e1 f) (term_map e2 f);
  term_map (term_split ep e) f :=
    term_split (term_map ep f) (term_map e (var_map_skip (var_map_skip f)) );
  term_map (term_app e1 e2) f :=
    term_app (term_map e1 f) (term_map e2 f);
  term_map (term_abs ebody) f :=
    term_abs (term_map ebody (var_map_skip f));
  term_map (term_perm Hperm e) f := term_perm Hperm (term_map e f);
  term_map (term_lift _ _ _ _ e) f := term_lift _ _ _ _ (term_map e f);
  term_map (term_call xR x arg) f := term_call xR x (term_map arg f);
  term_map (term_mfix _ x bodies e) f :=
    term_mfix _ x (bodies_map bodies f) (term_map e f);
  where bodies_map {G1 G2 : ctx} {MR : mfix_ctx} {R : call_frame} (bodies : mfix_bodies G1 MR R)
                 (f : forall t', var t' G1 -> var t' G2) : mfix_bodies G2 MR R :=
    bodies_map mfix_bodies_nil f := mfix_bodies_nil;
    bodies_map (mfix_bodies_cons body bodies) f :=
      mfix_bodies_cons (term_map body (var_map_skip f)) (bodies_map bodies f).
Transparent term_map.


Definition exchange_term MR G1 G2 G3 (u1 u2 t:type)
      (e : term t (G1 ++ [u1] ++ G2 ++ [u2] ++ G3) MR) : 
      term t (G1 ++ [u2] ++ G2 ++ [u1] ++ G3) MR :=
  term_map e (fun t' x => perm_var x (exchange_var_perm G1 G2 G3 u1 u2)).
Definition weaken_l_term MR G1 G2 t (e : term t G2 MR ) : term t (G1 ++ G2) MR
  := term_map e (fun t' e' => weaken_var_l _ _ t' e').
Definition weaken_l_term_single MR t1 G2 t (e : term t G2 MR ) : term t (t1 :: G2) MR :=
  weaken_l_term MR [t1] G2 t e.

Definition weaken_l_bodies {R MR G1 G2} (bodies : mfix_bodies G2 MR R) : mfix_bodies (G1 ++ G2) MR R :=
  bodies_map bodies (fun t' e' => weaken_var_l _ _ t' e').

Definition weaken_l_bodies_single {R MR G t} (bodies : mfix_bodies G MR R) : mfix_bodies (t :: G) MR R:=
  @weaken_l_bodies _ _ [t] G bodies.

Definition weaken_r_term MR G1 G2 t (e : term t G1 MR ) : term t (G1 ++ G2) MR
  := term_map e (fun t' e' => weaken_var_r _ _ t' e').
Definition weaken_mid_term MR G1 G2 G3 t (e : term t (G1 ++ G3) MR) : term t (G1 ++ G2 ++ G3) MR
  := term_map e (fun t' e' => weaken_var_mid _ _ _ t' e').

Fixpoint term_of_value {t Γ MR} (v : value t) : term t Γ MR :=
  match v with
  | val_const n => term_const n
  | val_nil => term_nil
  | val_cons hv tv => term_cons (term_of_value hv) (term_of_value tv)
  | val_pair v1 v2 => term_pair (term_of_value v1) (term_of_value v2)
  | val_abs e => weaken_r_term _ _ _ _ (term_abs e) 
  end. 

Equations subst_var {MR t u} (G1 G2 : list type) (e : value t) (x : var u (G1 ++ [t] ++ G2 )) :
                term u (G1 ++ G2) MR := 
    subst_var (t1 :: G1) _ e VarZ := term_var VarZ;
    subst_var (t1 :: G1) G2 e (VarS y) := weaken_l_term_single _ _ _ _ (subst_var G1 G2 e y) ;
    subst_var nil G2 e VarZ := weaken_r_term MR [] G2 t (term_of_value e) ;
    subst_var nil (t1 :: G2) e (VarS y) := term_var y.

(* tomorrow draft up a value and change the subst stuff *)
Equations subst_term {t u} G1 G2 MR (e1 : term u (G1 ++ [t] ++ G2) MR ) (v : value t) :
  term u (G1 ++ G2) MR :=
  subst_term _ _ _ (term_const n) _ := term_const n;
  subst_term _ _ _ term_nil _ := term_nil;
  subst_term _ _ _ (term_cons eh et) e2 := 
    term_cons (subst_term _ _ _ eh e2) (subst_term _ _ _ et e2);
  subst_term _ _ _ (term_var x) e2 := subst_var _ _ e2 x;
  subst_term _ _ _ (term_succ en) e2 := term_succ (subst_term _ _ _ en e2);
  subst_term _ _ _ (term_match_nat en eZ eS) e2 :=
    term_match_nat (subst_term _ _ _ en e2) (subst_term _ _ _ eZ e2)
                   (subst_term (Nat :: G1) _ _ eS e2);
  subst_term _ _ _ (term_match_list el enil econs) e2 :=
    term_match_list (subst_term _ _ _ el e2) (subst_term _ _ _ enil e2)
                    (subst_term (_ :: List _ :: G1) _ _ econs e2 );
  subst_term _ _ _ (term_pair el er) e2 :=
    term_pair (subst_term _ _ _ el e2) (subst_term _ _ _ er e2);
  subst_term _ _ _ (term_split ep e) e2 :=
    term_split (subst_term _ _ _ ep e2) (subst_term (_ :: _ :: G1) _ _ e e2 );
  subst_term _ _ _ (term_app ef ex) e2 :=
    term_app (subst_term _ _ _ ef e2) (subst_term _ _ _ ex e2);
  subst_term _ _ _ (term_abs ebody) e2 :=
    term_abs (subst_term (_ :: G1) _ _ ebody e2 );
  subst_term _ _ _ (term_perm Hp e) e2 :=
    term_perm Hp (subst_term _ _ _ e e2);
  subst_term _ _ _ (term_lift _ _ _ _ e) e2 :=
    term_lift _ _ _ _ (subst_term _ _ _ e e2);
  subst_term _ _ _ (term_call xR xt e) e2 :=
    term_call xR xt (subst_term _ _ _ e e2);
  subst_term _ _ _ (term_mfix R x bodies e) e2:=
    term_mfix R x (subst_bodies _ _ _ bodies e2) (subst_term _ _ _ e e2);
  where subst_bodies {t R} G1 G2 MR (bodies : mfix_bodies (G1 ++ [t] ++ G2) MR R) (v : value t) : 
    mfix_bodies (G1 ++ G2) MR R 
    :=
    subst_bodies _ _ _ mfix_bodies_nil _ := mfix_bodies_nil;
    subst_bodies _ _ _ (mfix_bodies_cons ebody bodies') e2 :=
      mfix_bodies_cons (subst_term (_ :: _) _ _ ebody e2) (subst_bodies _ _ _ bodies' e2).
Arguments subst_term {_ _ _ _ _}.
Definition subst_cons {t u Γ MR} (e1 : term u (t :: Γ) MR) (v : value t) :=
  @subst_term t u [] Γ MR e1 v.



Derive NoConfusion for type.
Section redex.
Context (err : forall A, A).

Arguments err {A}.
Notation "a && b" := (existT _ a b).
(* maybe should enforce this is Γ = [] *)
(* add bredexs for perm, lift, and mfix applied to values*)
Inductive bredex : type -> ctx -> mfix_ctx -> Type :=
  | bredex_succ {Γ MR} (vn : value Nat) : bredex Nat Γ MR
  | bredex_match_nat {t Γ MR} (vn : value Nat) (eZ : term t Γ MR) (eS : term t (Nat :: Γ) MR) : 
    bredex t Γ MR
  | bredex_match_list {t1 t2 Γ MR} (vl : value (List t1)) (enil : term t2 Γ MR) 
                     (econs : term t2 (t1 :: (List t1) :: Γ ) MR) : 
    bredex t2 Γ MR
  | bredex_split {t1 t2 t3 Γ MR} (vp : value (Pair t1 t2)) (e : term t3 (t1 :: t2 :: Γ) MR ) : 
    bredex t3 Γ MR
  | bredex_app {t1 t2 Γ MR} (vf : value (Arrow t1 MR t2) ) (vx : value t1) :
    bredex t2 Γ MR
  | bredex_perm {t Γ MR1 MR2} (Hperm : perm MR1 MR2) (v : value t) : 
    bredex t Γ MR2
  | bredex_lift {t Γ MR1 MR2} (v : value t) : 
    bredex t Γ (MR1 ++ MR2)
  | bredex_mfix {t Γ R MR} (x : var R MR) (bodies : mfix_bodies Γ MR R) (v : value t) :
    bredex t Γ (TypedVar.remove R MR x)
  .

Equations step_bredex {t Γ MR} (r : bredex t Γ MR) : term t Γ MR :=
  step_bredex (bredex_succ (val_const n) ) := term_const (1 + n);
  step_bredex (bredex_match_nat (val_const n) eZ eS ) :=
    match n with
    | 0 => eZ
    | S m => subst_cons eS (val_const m)
    end;
  step_bredex (bredex_match_list (val_nil) enil _ ) := enil;
  step_bredex (bredex_match_list (val_cons vh vt) _ econs) :=
    subst_cons (subst_cons econs vh) vt;
  step_bredex (bredex_split (val_pair v1 v2) e) :=
    subst_cons (subst_cons e v1) v2;
  step_bredex (bredex_app (val_abs ebody) varg ) :=
    weaken_r_term _ _ _ _ (subst_cons ebody varg);
  step_bredex (bredex_perm _ v) := term_of_value v;
  step_bredex (bredex_lift v) := term_of_value v;
  step_bredex (bredex_mfix _ _ v) := term_of_value v.


Inductive eval_context : type -> forall Γ :ctx, mfix_ctx -> forall t MR, (bredex t Γ MR + call MR t) -> bool -> Type := 
  | ev_hole t Γ MR (r : (bredex t Γ MR + call MR t) ) : eval_context t Γ MR t MR r true
  | ev_cons_l b t1 t2 Γ MR1 MR2 (r : (bredex t2 Γ MR2 + call MR2 t2)  ) 
           (Eh : eval_context t1 Γ MR1 _ _ r b) (et : term (List t1) Γ MR1) : 
    eval_context (List t1) Γ MR1 _ _ r b
  | ev_cons_r b t1 t2 Γ MR1 MR2 (r : (bredex t2 Γ MR2 + call MR2 t2)  ) 
           (vh : value t1) (Et : eval_context (List t1) Γ MR1 _ _ r b) : 
    eval_context (List t1) Γ MR1 _ _ r b
  | ev_succ b Γ MR1 t2 MR2 (r : (bredex t2 Γ MR2 + call MR2 t2)  )  
         (E : eval_context Nat Γ MR1 _ _ r b) : 
    eval_context Nat Γ MR1 _ _ r b
  | ev_match_nat b t1 Γ MR1 t2 MR2 (r : (bredex t2 Γ MR2 + call MR2 t2)  )
              (En : eval_context Nat Γ MR1 _ _ r b)
              (eZ : term t1 Γ MR1)
              (eS : term t1 (Nat :: Γ) MR1) :
    eval_context t1 Γ MR1 _ _ r b
  | ev_match_list b t1 t2 Γ1 MR1 t3 MR2 (r : (bredex t3 Γ1 MR2 + call MR2 t3)  )
                  (El : eval_context (List t1) Γ1 MR1 _ _ r b)
                  (enil : term t2 Γ1 MR1)
                  (econs : term t2 (t1 :: (List t1) :: Γ1) MR1) : 
    eval_context t2 Γ1 MR1 _ _ r b
  | ev_pair_l b t1 t2 Γ1 MR1 t3 MR2 (r : (bredex t3 Γ1 MR2 + call MR2 t3)  )
            (E1 : eval_context t1 Γ1 MR1 _ _ r b)
            (e2 : term t2 Γ1 MR1) :
    eval_context (Pair t1 t2) Γ1 MR1 _ _ r b
  | ev_pair_r b t1 t2 Γ1 MR1 t3 MR2  (r : (bredex t3 Γ1 MR2 + call MR2 t3)  )
            (v1 : value t1)
            (E2 : eval_context t2 Γ1 MR1 _ _ r b) :
    eval_context (Pair t1 t2) Γ1 MR1 _ _ r b
  | ev_split b t1 t2 t3 Γ1 MR1 t4 MR2 (r : (bredex t4 Γ1 MR2 + call MR2 t4)  )
             (Ep : eval_context (Pair t1 t2) Γ1 MR1 _ _ r b)
             (es : term t3 (t1 :: t2 :: Γ1) MR1 ) : 
    eval_context t3 Γ1 MR1 _ _ r b
  | ev_app_l b t1 t2 Γ1 MR1 t3 MR2 (r : (bredex t3 Γ1 MR2 + call MR2 t3))
             (Ef : eval_context (Arrow t1 MR1 t2) Γ1 MR1 _ _ r b)
             (e : term t1 Γ1 MR1) : 
    eval_context t2 Γ1 MR1 _ _ r b
  | ev_app_r b t1 t2 Γ1 MR1 t3 MR2 (r : (bredex t3 Γ1 MR2 + call MR2 t3))
             (vf : value (Arrow t1 MR1 t2))
             (E : eval_context t1 Γ1 MR1 _ _ r b) : 
    eval_context t2 Γ1 MR1 _ _ r b
  | ev_perm b t1 Γ1 MR1 MR2 t2 MR3  (r : (bredex t2 Γ1 MR3 + call MR3 t2))
            (Hperm : perm MR1 MR2)
            (E : eval_context t1 Γ1 MR1 _ _ r b) : 
    eval_context t1 Γ1 MR2 _ _ r false
  | ev_lift b t1 Γ1 MR1 MR2 t2 MR3 (r : (bredex t2 Γ1 MR3 + call MR3 t2))
            (E : eval_context t1 Γ1 MR2 _ _ r b) : 
    eval_context t1 Γ1 (MR1 ++ MR2) _ _ r false
  | ev_call b t1 t2 Γ1 MR1 R t3 MR2 (r : (bredex t3 Γ1 MR2 + call MR2 t3))
            (xR : var R MR1) (x : var (t1,t2) R)
            (E : eval_context t1 Γ1 MR1 _ _ r b) : 
    eval_context t2 Γ1 MR1 _ _ r b
  | ev_mfix b t1 Γ1 MR1 R1 t2 MR2 (r : (bredex t2 Γ1 MR2 + call MR2 t2)) 
            (x : var R1 MR1) (bodies : mfix_bodies Γ1 MR1 R1)
            (E : eval_context t1 Γ1 MR1 _ _ r b) :
    eval_context t1 Γ1 (TypedVar.remove R1 MR1 x) _ _ r false
.
Arguments ev_hole {_ _ _ _}.
Arguments ev_cons_l {b t1 t2 Γ MR1 MR2 r}.
Arguments ev_cons_r {b t1 t2 Γ MR1 MR2 r}.
Arguments ev_succ {b Γ MR1 t2 MR2 r}.
Arguments ev_match_nat {b t1 Γ MR1 t2 MR2 r}.
Arguments ev_match_list {b t1 t2 Γ1 MR1 t3  MR2 r}.
Arguments ev_pair_l {b t1 t2 Γ1 MR1 t3 MR2 r}.
Arguments ev_pair_r {b t1 t2 Γ1 MR1 t3 MR2 r}.
Arguments ev_split {b t1 t2 t3 Γ1 MR1 t4 MR2 r}.
Arguments ev_app_l {b t1 t2 Γ1 MR1 t3 MR2 r}.
Arguments ev_app_r {b t1 t2 Γ1 MR1 t3 MR2 r}.
Arguments ev_perm (b) {t1 Γ1 MR1 MR2 t2 MR3 r}.
Arguments ev_lift (b) {t1 Γ1 MR1 MR2 t2 MR3 r}.
Arguments ev_call {b t1 t2 Γ1 MR1 R t3 MR2 r}.
Arguments ev_mfix (b) {t1 Γ1 MR1 R1 t2 MR2 r}.
Arguments eval_context (_ _ _) {_ _}.
Equations subst_eval_context {b t1 t2 Γ1 MR1 MR2} (r : (bredex t2 Γ1 MR2 + call MR2 t2)) 
           (E : eval_context t1 Γ1 MR1 r b) (e : term t2 Γ1 MR2) : term t1 Γ1 MR1 :=
  subst_eval_context r ev_hole e := e;
  subst_eval_context r (ev_cons_l Eh et) e := term_cons (subst_eval_context r Eh e) et;
  subst_eval_context r (ev_cons_r vh Et) e := term_cons (term_of_value vh) (subst_eval_context r Et e);
  subst_eval_context r (ev_succ E) e := term_succ (subst_eval_context r E e);
  subst_eval_context r (ev_match_nat En eZ eS) e := 
    term_match_nat (subst_eval_context r En e) eZ eS;
  subst_eval_context r (ev_match_list El enil econs) e := 
    term_match_list (subst_eval_context r El e) enil econs;
  subst_eval_context r (ev_pair_l E1 e2) e :=
    term_pair (subst_eval_context r E1 e) e2;
  subst_eval_context r (ev_pair_r v1 E2) e :=
    term_pair (term_of_value v1) (subst_eval_context r E2 e);
  subst_eval_context r (ev_split Ep es) e :=
    term_split (subst_eval_context r Ep e) es;
  subst_eval_context r (ev_app_l E1 e2) e :=
    term_app (subst_eval_context r E1 e) e2;
  subst_eval_context r (ev_app_r v1 E2) e :=
    term_app (term_of_value v1) (subst_eval_context r E2 e);
  subst_eval_context r (ev_perm _ Hperm E) e :=
    term_perm Hperm (subst_eval_context r E e);
  subst_eval_context r (ev_lift _ E) e :=
    term_lift _ _ _ _(subst_eval_context r E e);
  subst_eval_context r (ev_call xR x E) e :=
    term_call xR x (subst_eval_context r E e);
  subst_eval_context r (ev_mfix _ x bodies E) e :=
    term_mfix _ x bodies (subst_eval_context r E e). 

(* change this to be particular to call *)
Equations normalize_eval_context {t1 t2 Γ1 MR1 MR2} (c : call MR2 t2) 
           (E : eval_context t1 Γ1 MR1 (inr c) true) : 
  {c : call MR1 t2 & eval_context t1 Γ1 MR1 (inr c) true} :=

  normalize_eval_context c ev_hole := c && ev_hole;
  normalize_eval_context c (ev_cons_l Eh et) := 
    let '(c' && Eh') := normalize_eval_context c Eh in
    c' && (ev_cons_l Eh' et);
  normalize_eval_context c (ev_cons_r vh Et) :=
    let '(c' && Et') := normalize_eval_context c Et in
    c' && ev_cons_r vh Et';
  normalize_eval_context c (ev_succ En) :=
    let '(c' && En') := normalize_eval_context c En in
    c' && ev_succ En';
  normalize_eval_context c (ev_match_nat En eZ eS) :=
    let '(c' && En') := normalize_eval_context c En in
    c' && ev_match_nat En' eZ eS;
  normalize_eval_context c (ev_match_list El enil econs) :=
    let '(c' && El') := normalize_eval_context c El in
    c' && ev_match_list El' enil econs;
  normalize_eval_context c (ev_pair_l E1 e2) :=
    let '(c' && E1') := normalize_eval_context c E1 in
    c' && ev_pair_l E1' e2;
  normalize_eval_context c (ev_pair_r v1 E2) :=
    let '(c' && E2') := normalize_eval_context c E2 in
    c' && ev_pair_r v1 E2';
  normalize_eval_context c (ev_split E es) :=
    let '(c' && E') := normalize_eval_context c E in
    c' && ev_split E' es;
  normalize_eval_context c (ev_app_l E1 e2) :=
    let '(c' && E1') := normalize_eval_context c E1 in
    c' && ev_app_l E1' e2;
  normalize_eval_context c (ev_app_r v1 E2) :=
    let '(c' && E2') := normalize_eval_context c E2 in
    c' && ev_app_r v1 E2';
  normalize_eval_context c (ev_call xR x E) :=
    let '(c' && E') := normalize_eval_context c E in
    c' && ev_call xR x E'.
(*
Equations lift_term_map {Γ MR1 MR2 t1} (f : forall t, term t Γ MR1 -> term t Γ MR2) (t : type) 
          (e : term t (t1 :: Γ) MR1) : term t (t1 :: Γ) MR2 :=
  lift_term_map f _ (term_const n) := term_const n;
  lift_term_map f _ term_nil := term_nil;
  lift_term_map f _ (term_cons eh et) := term_cons (lift_term_map f _ eh) (lift_term_map f _ et);
  lift_term_map f _ (term_var VarZ) := term_var VarZ;
  lift_term_map f _ (term_var (VarS x)) := weaken_l_term_single _ _ _ _ (f _ (term_var x));
  lift_term_map f _ (term_succ en) := term_succ (lift_term_map f _ en);
  lift_term_map f _ (term_match_nat en eZ eS) :=
    term_match_nat (lift_term_map f _ en) (lift_term_map f _ eZ)
                   (lift_term_map (lift_term_map f) _ eS);
  lift_term_map f _ (term_match_list el enil econs) :=
    term_match_list (lift_term_map f _ el) (lift_term_map f _ enil)
                    (lift_term_map (lift_term_map (lift_term_map f) ) _ econs);
  lift_term_map f _ (term_pair e1 e2) :=
    term_pair (lift_term_map f _ e1) (lift_term_map f _ e2);
  lift_term_map f _ (term_split ep e) :=
    term_split (lift_term_map f _ ep) (lift_term_map (lift_term_map (lift_term_map f) ) _ e );
  lift_term_map f _ (term_app e1 e2) :=
    term_app (lift_term_map f _ e1) (lift_term_map f _ e2);
  lift_term_map f _ (term_abs ebody) := term_abs ebody;
  lift_term_map f _ _ := err.
*)

Definition term_map_perm {Γ MR1 MR2} (Hperm : perm MR1 MR2) : forall t, term t Γ MR1 -> term t Γ MR2 :=
  fun t e => term_perm Hperm e.
Definition term_map_lift {Γ MR1 MR2} : forall t, term t Γ MR2 -> term t Γ (MR1 ++ MR2) :=
  fun t e => term_lift _ _ _ _ e.

Definition term_map_mfix {Γ R MR} (x : var R MR) (bodies : mfix_bodies Γ MR R) : 
  forall t, term t Γ MR -> term t Γ (TypedVar.remove R MR x) :=
  fun t e => term_mfix R x bodies e.
(* try to work out your new push idea I think it is by far the best idea you currently have,
   it would give you a way to simply push mfix, perm, and lift 
   I also think I need to keep track of depth, if the application in two deep (i.e. two args)
   then I need to change the effect signature of the two lambda, one nested in the other (assuming no call events)
*)
(* weird error message here, pay close attention when get to it *)
Equations push_eval_context {t1 t2 Γ1 MR1 MR2} (r : bredex t2 Γ1 MR1 + call MR1 t2)
           (E : eval_context t1 Γ1 MR1 r true) 
           (f : forall t Γ, term t (Γ ++ Γ1) MR1 -> term t (Γ ++ Γ1) MR2) (* a bit suspicious of Γ here*)
           (fvar : forall R, var R MR1 -> var R MR2) (* mfix will work differently, maybe there just needs to be a another function for that*)
           (e : term t2 Γ1 MR2) : term t1 Γ1 MR2 :=
  push_eval_context _ ev_hole f fvar e := e;
  push_eval_context _ (ev_cons_l Eh et) f fvar e :=
    term_cons (push_eval_context _ Eh f fvar e) (f _ [] et); (* need to change the mfix context of et*)
  push_eval_context _ (ev_cons_r v Et) f fvar e :=
    term_cons (term_of_value v) (push_eval_context _ Et f fvar e);
  push_eval_context _ (ev_succ E) f fvar e :=
    term_succ (push_eval_context _ E f fvar e);
  push_eval_context _ (ev_match_nat En eZ eS) f fvar e :=
    term_match_nat (push_eval_context _ En f fvar e) (f _ [] eZ) (f _ [Nat] eS); 
  push_eval_context _ (ev_match_list El enil econs) f fvar e :=
    term_match_list (push_eval_context _ El f fvar e) (f _ [] enil) (f _ [_;_] econs);
  push_eval_context _ (ev_pair_l E1 e2) f fvar e :=
    term_pair (push_eval_context _ E1 f fvar e) (f _ [] e2);
  push_eval_context _ (ev_pair_r v1 E2) f fvar e :=
    term_pair (term_of_value v1) (push_eval_context _ E2 f fvar e);
  push_eval_context _ (ev_split Ep es) f fvar e :=
    term_split (push_eval_context _ Ep f fvar e) (f _ [_ ; _] es );
  (* the problem with app is showing up in a different location now, uggh*)
  push_eval_context _ (ev_app_r (val_abs ebody) E2) f fvar e :=
    term_app (term_abs (f _ [t3] (weaken_r_term _ _ _ _ ebody) )) (push_eval_context _ E2 f fvar e);
  push_eval_context _ (ev_call xR x E) f fvar e := 
    term_call (fvar _ xR) x (push_eval_context _ E f fvar e) ;
  push_eval_context _ (ev_app_l E1 e2) f fvar e := err.
    (* term_app (push_eval_context _ E1 f fvar e) (f _ [] e2) *);
  

Instance option_monad : Monad option :=
  {|
    ret := fun _ x => Some x;
    bind := fun _ _ m k =>
              match m with
              | None => None
              | Some x => k x end;
  |}.

(*
Definition step_eval_context_l {t1 t2 Γ1 Γ2 MR1 MR2} b (br : bredex t2 Γ2 MR2) 
           (E : eval_context t1 Γ1 MR1 (inl br) b ): option (term t1 Γ1 MR1) :=
  Some (subst_eval_context (inl br) E (step_bredex br)).

Equations step_eval_context_r {t1 t2 Γ1 Γ2 MR1 MR2} b (c : call MR2 t2)
           (E : @eval_context t1 Γ1 MR1 t2 Γ2 MR2 (inr c) b) : option (term t1 Γ1 MR1) :=
  step_eval_context_r _ (ev_mfix false x bodies E) := e <- step
  step_eval_context_r _ c E := err.

Equations step_eval_context {t1 t2 Γ1 Γ2 MR1 MR2} b (r : (bredex t2 Γ2 MR2 + call MR2 t2)) 
           (E : eval_context t1 Γ1 MR1 r b) : option (term t1 Γ1 MR1) :=
  step_eval_context b (inl br) E := step_eval_context_l b br E;
  step_eval_context b (inr c) E := step_eval_context_r b c E.
*)

(**)
(* need to rely on var_eq_neq *)
(*
Equations var_eq_
*)
(* Equations is very slow on creating the equations for this function,
   if developing with it, use the #[derive(equations=no)] directive
   to save time
*)
Equations step_eval_context {t1 t2 Γ1 MR1 MR2} b (r : (bredex t2 Γ1 MR2 + call MR2 t2)) 
           (E : eval_context t1 Γ1 MR1 r b) : option (term t1 Γ1 MR1) :=
  step_eval_context _ (inl br) E := ret (subst_eval_context (inl br) E (step_bredex br));

  step_eval_context _ (inr c) (ev_mfix true xR bodies E) := 
      let '( (callv yR x v) && E' ) := normalize_eval_context c E in
      ret 
      match (var_eq_neq _ _ _ xR yR) with
      | inl Heq => 
          let fx := nth_body bodies (var_eq_elim xR yR Heq x) in
          let e := subst_cons fx v in
          term_mfix R1 xR bodies (subst_eval_context (inr (callv yR x v) ) E' e)
      | inr Hneq =>
          let yR' := remove_var _ _ _ xR yR Hneq in
          push_eval_context (inr (callv yR x v)) E' (fun t e => term_mfix R1 xR bodies e)
                            (term_call yR' x (term_of_value v)) end;

  step_eval_context _ (inr c) (ev_mfix false x bodies E) := 
        e <- step_eval_context false (inr c) E;;
        ret (term_mfix _ x bodies e);

  step_eval_context _ (inr c) (ev_perm true Hperm E) :=
          let '((callv yR x v) && E' ) := normalize_eval_context c E in
          ret (
          push_eval_context (inr (callv yR x v)) E' (fun t e => term_perm Hperm e)
                            (term_call (perm_var yR Hperm) x (term_of_value v)));

  step_eval_context _ (inr c) (ev_perm false Hperm E) :=
            e <- step_eval_context false (inr c) E;;
            ret (term_perm Hperm e);

  step_eval_context _ (inr c) (ev_lift true E) :=
          let '((callv yR x v) && E' ) := normalize_eval_context c E in
          ret (
              push_eval_context _ E' (fun t e => term_lift _ _ _ _ e)
                                (term_call (weaken_var_l _ _ _ yR) x (term_of_value v) ));

  step_eval_context _ (inr c) (ev_lift false E) :=
                e <- step_eval_context false (inr c) E;;
                ret (term_lift _ _ _ _ e);

  step_eval_context _ (inr c) _ := None.

    (* here I should use push, relying on Hneq to transform yR into a remove R1 MR1 xR variable*)
    
(*
tomorrow, first use what we currently have to write a step function,
see if any weird issues come up
start with mfix, lift, and perm because those are the werid ones

eval_context -> option term,

then write that lifting function, and finish up the push_eval_context

from there start a new file for relating 
*)

End redex.

Definition halted t MR : Type := (value t + call MR t).


(* unfortunately, I don't know if this will play nicely with the handler idea 
   on second thought, it might, but I think it will require more cases
*)
Inductive term_obs : type -> ctx -> mfix_ctx -> Type := 
(* need to rethink this part for the recursion problem, the *)
| obs_consl t Γ MR (eh : term_obs t Γ MR) (et : term (List t) Γ MR) : term_obs (List t) Γ MR
| obs_consr t Γ MR (vh : halted t MR) (et : term_obs (List t) Γ MR) : term_obs (List t) Γ MR
| obs_cons_calll t Γ MR (c : call MR t) (ht : halted (List t) MR)   : term_obs (List t) Γ MR
| obs_cons_callr t Γ MR (v1 : value t) (ct : call MR (List t)) : term_obs (List t) Γ MR
| obs_succe Γ MR (e : term Nat Γ MR) : term_obs Nat Γ MR
| obs_succh Γ MR (hn : halted Nat MR) : term_obs Nat Γ MR
| obs_match_nate t Γ MR (en : term Nat Γ MR) (eZ : term t Γ MR) (eS : term t (Nat :: Γ) MR ) :
  term_obs t Γ MR
| obs_match_nath t Γ MR (hn : halted Nat MR) (eZ : term t Γ MR) (eS : term t (Nat :: Γ) MR) :
  term_obs t Γ MR
| obs_match_liste t1 t2 Γ MR (el : term (List t1) Γ MR) (enil : term t2 Γ MR) 
                  (econs : term t2 (t1 :: List t1 :: Γ) MR ) :
  term_obs t2 Γ MR
| obs_match_listh t1 t2 Γ MR (hl : halted (List t1) MR) (enil : term t2 Γ MR) 
                  (econs : term t2 (t1 :: List t1 :: Γ) MR ) :
  term_obs t2 Γ MR
| obs_pairl t1 t2 Γ MR (e1 : term t1 Γ MR) (e2 : term t2 Γ MR) :
  term_obs (Pair t1 t2) Γ MR
| obs_pairr t1 t2 Γ MR (h1 : halted t1 MR) (e2 : term t2 Γ MR) : 
  term_obs (Pair t1 t2) Γ MR
| obs_pair_callr t1 t2 Γ MR (v1 : value t1) (c2 : call MR t2) : 
  term_obs (Pair t1 t2) Γ MR
| obs_splite t1 t2 t3 Γ MR (ep : term (Pair t1 t2) Γ MR) (esp : term t3 (t1 :: t2 :: Γ) MR) : 
             term_obs t3 Γ MR
| obs_splith t1 t2 t3 Γ MR (hp : halted (Pair t1 t2) MR) (esp : term t3 (t1 :: t2 :: Γ) MR) : 
             term_obs t3 Γ MR
| obs_appl t1 t2 Γ MR (ef : term (Arrow t1 MR t2) Γ MR) (ex : term t1 Γ MR) : 
  term_obs t2 Γ MR
| obs_appr t1 t2 Γ MR (hf : halted (Arrow t1 MR t2) MR) (ex : term t1 Γ MR) : 
  term_obs t2 Γ MR
(*
| obs_app_callr t1 t2 Γ MR (vf : value (Arrow t1 MR t2) ) (cx : call MR t1) :
  term_obs t2 Γ MR
*)
| obs_calle t1 t2 Γ R MR (xR : var R MR) (x : var (t1,t2) R) (arge : term t1 Γ MR) :
  term_obs t2 Γ MR
| obs_perme t Γ MR1 MR2 (Hperm : perm MR1 MR2)  (e : term t Γ MR1) : 
  term_obs t Γ MR2
| obs_permh t Γ MR1 MR2 (Hperm : perm MR1 MR2)  (he : halted t MR1) : 
  term_obs t Γ MR2
| obs_lifte t Γ MR1 MR2 (e : term t Γ MR2) :
  term_obs t Γ (MR1 ++ MR2)
| obs_lifth t Γ MR1 MR2 (eh : halted t MR2) : 
  term_obs t Γ (MR1 ++ MR2)
| obs_mfixe t Γ R MR x (bodies : mfix_bodies Γ MR R)  (e : term t Γ MR) : 
  term_obs t Γ (TypedVar.remove R MR x)
| obs_mfixh t Γ R MR x (bodies : mfix_bodies Γ MR R)  (eh : halted t MR) : 
  term_obs t Γ (TypedVar.remove R MR x)
.
Arguments obs_consl {t Γ MR}.
Arguments obs_consr {t Γ MR}.
Arguments obs_cons_calll {t Γ MR}.
Arguments obs_cons_callr {t Γ MR}.
Arguments obs_succe {Γ MR}.
Arguments obs_succh {Γ MR}.
Arguments obs_match_nate {t Γ MR}.
Arguments obs_calle {t1 t2 Γ R MR}.
Arguments obs_match_nath {t Γ MR}.
Arguments obs_match_liste {t1 t2 Γ MR}.
Arguments obs_match_listh {t1 t2 Γ MR}.
Arguments obs_pairl {t1 t2 Γ MR}.
Arguments obs_pairr {t1 t2 Γ MR}.
Arguments obs_pair_callr {t1 t2 Γ MR}.
Arguments obs_splite {t1 t2 t3 Γ MR}.
Arguments obs_splith {t1 t2 t3 Γ MR}.
Arguments obs_appl {t1 t2 Γ MR}.
Arguments obs_appr {t1 t2 Γ MR}.
Arguments obs_perme {t Γ MR1 MR2}.
Arguments obs_permh {t Γ MR1 MR2}.
Arguments obs_lifte {t Γ MR1 MR2}.
Arguments obs_lifth {t Γ MR1 MR2}.
Arguments obs_mfixe {t Γ R MR}.
Arguments obs_mfixh {t Γ R MR}.
(* Arguments obs_app_callr {t1 t2 Γ MR}. *)
(* what should it give for (call 0, call 1), 
   right now, I think that should count as a term_obs,
   and should step to call 0

   just to be clear match e ...

   if halted e
   then if value e then do substitution
        else if halted e then e
   else match (step e) ...

maybe call needs to be changed 
maybe it needs to be all of the possible ways a term can get stuck because of a call


*)

Section observe.

Context (err : forall A, A).
Arguments err {A}.
(* actually realizing this does not quite work as I have written it, 
   call (call 0) what should its type be, suggests the call needs some more constructors

   as it is currently written, call MR t objects must have an argument evaluated to a 
   value, this is problematic because the argument might itself evaluate to a call
   how should we design this type then

   what if 
   call MR t :=
   call_intro t1 t2 (cont : value t2 -> call MR t)

   something like that where a call object requires some kind of continuation
   this doesn't seem well founded, needs a base case of some kind or maybe some rethinking
   

*)

(*
Arguments term _ (_ _)%list_scope
Arguments term_const n%nat_scope {Γ MR}%list_scope
Arguments term_nil {t} {Γ MR}%list_scope
Arguments term_cons {t} {Γ MR}%list_scope head tail
Arguments term_var {t} {Γ MR}%list_scope x
Arguments term_succ {Γ MR}%list_scope en
Arguments term_match_nat {t} {Γ MR}%list_scope en eZ eS
Arguments term_match_list {t1 t2} {Γ MR}%list_scope el enil econs
Arguments term_pair {t1 t2} {Γ MR}%list_scope e1 e2
Arguments term_split {t1 t2 t3} {Γ MR}%list_scope ep e
Arguments term_app {t1 t2} {Γ MR}%list_scope e1 e2
Arguments term_abs {t1 t2} {Γ MR MR'}%list_scope e
Arguments term_perm {t} {Γ MR1 MR2}%list_scope Hperm e
Arguments term_lift t (Γ MR1 MR2)%list_scope e
Arguments term_call {t1 t2} {Γ MR R}%list_scope xR x arg
Arguments term_mfix {t} {Γ}%list_scope R%list_scope {MR}%list_scope x bodies e
Arguments mfix_bodies (_ _ _)%list_scope
Arguments mfix_bodies_nil {Γ MR}%list_scope
Arguments mfix_bodies_cons {Γ MR}%list_scope {t1 t2} {R'}%list_scope body bodies
*)
Notation to x := (inl x).
Notation val x := (inr (inl x)).
Notation ca x := (inr (inr x)).
(* processes a closed term into a form where we can, without recursion, easily 
   identify what reduction step should be taken *)
Equations observe {t MR} (e : term t [] MR) : term_obs t [] MR + (value t + call MR t) :=
  (* simple values *)
  observe (term_const n) := val (val_const n);
  observe term_nil := val val_nil;
  observe (term_abs ebody) := val (val_abs ebody);
  (* call *)
  observe (term_call xR x arg) :=
    match observe arg with
    | to eobs => to ((obs_calle xR x arg) )
    | val v => ca (callv xR x v)
    | ca c => ca (calls xR x c) end;
  (* composition expressions *)
  observe (term_cons eh et) :=
    match observe eh, observe et with 
    | to eobs, _ => to (obs_consl eobs et)
    | ca c, inr h => to (obs_cons_calll c h)
    | val v1, val v2 => val (val_cons v1 v2)
    | val v1, ca c => to (obs_cons_callr v1 c)
    | inr h, to eobs => to (obs_consr h eobs) 
    end;
    (*
    match observe eh with
    | to eobs => to (obs_consl eobs et)
    | ca c => to (obs_consr (inr c) et)
    | val v1  => 
        match observe et with
        | to eobs => to (obs_consr (inl v1) eobs )
        | ca c => to (obs_cons_callr v1 c)
        | val v2 => val (val_cons v1 v2) end
    end; *)
  observe (term_succ en) :=
    match observe en with
    | to eobs => to (obs_succe en)
    | inr hn => to (obs_succh hn) end;
  observe (term_match_nat en eZ eS) :=
    match observe en with
    | to _ => to (obs_match_nate en eZ eS)
    | inr hn => to (obs_match_nath hn eZ eS) end;
  observe (term_match_list el enil econs) :=
    match observe el with
    | to _ => to (obs_match_liste el enil econs)
    | inr hl => to (obs_match_listh hl enil econs ) end;
  observe (term_pair e1 e2) :=
    match observe e1 with
    | to eobs => to (obs_pairl e1 e2)
    | ca c => to (obs_pairr (inr c) e2)
    | val v1 =>
        match observe e2 with
        | to _ => to (obs_pairr (inl v1) e2)
        | ca c => to (obs_pair_callr v1 c)
        | val v2 => val (val_pair v1 v2) end
    end;
  observe (term_split ep es) :=
    match observe ep with
    | to _ => to (obs_splite ep es)
    | inr hs => to (obs_splith hs es) end;
  observe (term_app ef ex) :=
    match observe ef with
    | to _ => to (obs_appl ef ex)
    | inr hf => to (obs_appr hf ex) end;
  observe (term_perm Hperm e) :=
    match observe e with
    | to _ => to (obs_perme Hperm e)
    | inr hr => to (obs_permh Hperm hr) end;
  observe (term_lift _ _ _ _ e) :=
    match observe e with
    | to _ => to (obs_lifte e)
    | inr h => to (obs_lifth h) end;
  observe (term_mfix _ x bodies e) :=
    match observe e with
    | to _ => to (obs_mfixe x bodies e)
    | inr h => to (obs_mfixh x bodies h) end.

Definition handlers : Type := unit.

Equations step {t MR} (hs : handlers) (e : term t [] MR) : term t [] MR + value t :=
  step hs (term_const n) := inr (val_const n);


  (* call *)
  step hs (term_call )
  step hs _ := err.


(*
Arguments term_obs _ (_ _)%list_scope
Arguments obs_consl {t} {Γ MR}%list_scope eh et
Arguments obs_consr {t} {Γ MR}%list_scope vh et
Arguments obs_cons_callr {t} {Γ MR}%list_scope v1 ct
Arguments obs_succe {Γ MR}%list_scope e
Arguments obs_succh {Γ MR}%list_scope hn
Arguments obs_match_nate {t} {Γ MR}%list_scope en eZ eS
Arguments obs_match_nath {t} {Γ MR}%list_scope hn eZ eS
Arguments obs_match_liste {t1 t2} {Γ MR}%list_scope el enil econs
Arguments obs_match_listh {t1 t2} {Γ MR}%list_scope hl enil econs
Arguments obs_pairl {t1 t2} {Γ MR}%list_scope e1 e2
Arguments obs_pairr {t1 t2} {Γ MR}%list_scope h1 e2
Arguments obs_pair_callr {t1 t2} {Γ MR}%list_scope v1 c2
Arguments obs_splite {t1 t2 t3} {Γ MR}%list_scope ep esp
Arguments obs_splith {t1 t2 t3} {Γ MR}%list_scope hp esp
Arguments obs_appl {t1 t2} {Γ MR}%list_scope ef ex
Arguments obs_appr {t1 t2} {Γ MR}%list_scope hf ex
Arguments obs_calle {t1 t2} {Γ R MR}%list_scope xR x arge
Arguments obs_perme {t} {Γ MR1 MR2}%list_scope Hperm e
Arguments obs_permh {t} {Γ MR1 MR2}%list_scope Hperm he
Arguments obs_lifte {t} {Γ MR1 MR2}%list_scope e
Arguments obs_lifth {t} {Γ MR1 MR2}%list_scope eh
Arguments obs_mfixe {t} {Γ R MR}%list_scope x bodies e
Arguments obs_mfixh {t} {Γ R MR}%list_scope x bodies eh

*)
Definition term_of {t MR} (x : term t [] MR + (value t + call MR t)) :=
  match x with
  | inl e => e
  | inr (inl v) => term_of_value v
  | inr (inr c) => term_of_call c end.

Definition step_with {t MR} (f : term_obs t [] MR -> term t [] MR + (value t + call MR t)) 
           (e : term t [] MR) : term t [] MR + (value t + call MR t) :=
  match observe e with
  | inl eobs => f eobs
  | inr (inl v) => inr (inl v)
  | inr (inr c) => inr (inr c) end.
(* there is an issue here that I am calling step_obs on observe eh and not on eh itself,
   will need to think carefully about how to circumvent that, hopefully it does not
   ruin this way of doing things

   maybe the solution is obs_consl has an observed expr in the left arg
*)

(* maybe consider big step semantics and make it relational? *)
(* might be a good idea to create a monad for *)
Equations step_obs {t MR} (eo : term_obs t [] MR) : term t [] MR + (value t + call MR t) 
  by struct eo :=
  step_obs (obs_consl eh et) :=
    let eh' := term_of (step_obs eh) in 
    inl (term_cons eh' et);
  step_obs (obs_consr h et) :=
    let et' := term_of (step_obs et) in
    inl (term_cons (term_of (inr h)) et');
  step_obs (obs_cons_calll c _) :=
    (* uncovered another mismatch can't always step to a call because the type won't match,
       need to find the best way to represent this 


       remember that is it very important that mfix and lift and perm go down
       first, I guess perm and lift before mfix

       I am having a hard time seeing how installing these handlers should actually work

       maybe think about it from a evaluation context perspective
     *)
    ca c;
  
  step_obs _ := err.
Admitted.


Definition step {t MR} (e : term t [] MR) : term t [] MR + (value t + call MR t) :=
  match observe e with
  | inl eobs => step_obs eobs
  | inr (inl v) => inr (inl v)
  | inr (inr c) => inr (inr c) end.

End observe.


