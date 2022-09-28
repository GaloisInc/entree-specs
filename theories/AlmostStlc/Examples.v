Require Export Syntax.
Require Export Denotation.
Require Import List.
From EnTree Require Export 
     Core.EnTreeDefinition
     Eq.Eqit
.
Import ListNotations.
From Equations Require Import Equations Signature.


Section fun_lift.
Context {Γ : ctx} {MR1 MR2 MR3 : mfix_ctx}.
Context {t1 t2 : type}.
Definition fun_lift : term (Arrow (Arrow t1 MR2 t2) MR3 (Arrow t1 (MR1 ++ MR2) t2 ))
                           Γ MR3.
apply term_abs. apply term_abs.
apply term_lift. eapply @term_app with (t1 := t1).
apply term_var. apply VarS. apply VarZ.
apply term_var. apply VarZ.
Defined.

End fun_lift.

Section plus.
Context {Γ : ctx}.

Definition plus_call : call_frame := [(Nat, Arrow Nat [] Nat)].

Definition plus : term (Arrow Nat [] (Arrow Nat [] Nat)) Γ [].
apply term_abs. apply term_abs.
apply @term_mfix with (R := plus_call) (MR := [plus_call]) (x := VarZ).
- apply mfix_bodies_cons.
  + eapply term_match_nat.
    * apply term_var. apply VarZ.
    * apply term_abs. apply term_var. apply VarZ.
    * eapply @term_app with (t1 := Arrow Nat [] Nat).
      {
        apply term_abs. apply term_abs.
        apply @term_app with (t1 := Nat).
        - exact (term_var (VarS VarZ)).
        - exact (term_succ (term_var VarZ)).
      }
      {
        exact (term_call VarZ VarZ (term_var VarZ)).
      }
  + apply mfix_bodies_nil.
- eapply @term_app with (t1 := Nat).
  + apply @term_app with (t1 := Arrow Nat [] Nat).
    * apply @fun_lift with (MR1 := [plus_call]).
    * exact (term_call VarZ VarZ (term_var VarZ)).
  + exact (term_var (VarS VarZ)). 
Defined.

End plus.

Section plus'.

Context {Γ : ctx} {MR : mfix_ctx}.

Definition plus_call' : call_frame := [(Pair Nat Nat, Nat) ].

Definition plus' : term (Arrow (Pair Nat Nat) MR Nat) Γ MR.
apply term_abs. 
eapply @term_mfix with (R := plus_call') (MR := plus_call' :: MR) (x := VarZ).
- apply mfix_bodies_cons.
  + eapply term_split.
    * apply term_var. apply VarZ.
    * eapply term_match_nat.
      -- eapply term_var. eapply VarZ.
      -- eapply term_var. eapply VarS. eapply VarZ.
      -- apply term_succ. eapply term_call.
         apply VarZ. apply VarZ.
         apply term_pair.
         apply term_var. apply VarZ.
         apply term_var. apply VarS. apply VarS. apply VarZ.
  + apply mfix_bodies_nil.
- eapply term_call. apply VarZ. apply VarZ.
  apply term_var. apply VarZ.
Defined.
End plus'.

Locate bind_ret_l.

Goal denote_term (term_app (@plus' [] []) (term_pair (term_const 1) (term_const 1))) tt ≈ 
       Ret 2.
simp denote_term. unfold plus'. simp denote_term. 
repeat setoid_rewrite bind_ret_l. unfold plus_call'. simp denote_term.
cbn. simp denote_term. Transparent denote_term. cbn.
(* setoid_rewrite bind_ret_l.
 unfold denote_term.  setoid_rewrite @denote_term_equation_15. *)
Section map_term.
Context (t1 t2 : type) (MR : mfix_ctx).

Definition map_call : call_frame := (List t1, List t2) :: nil.


(* should come up with some notations and   *)
Definition map_body : term (List t2) (List t1 :: List t1 :: (Arrow t1 MR t2 :: nil))%list (map_call :: MR).
eapply term_match_list.
- eapply term_var. eapply VarS. eapply VarZ.
- eapply term_nil.
- eapply term_cons.
  + eapply term_lift with (MR1 := [map_call]).
    eapply term_app.
    * eapply term_var. repeat constructor.
    * eapply term_var. constructor.
  + eapply term_call.
    * apply VarZ.
    * apply VarZ.
    * eapply term_var. apply VarS. apply VarZ.
Defined.


Definition map : term (Arrow (Arrow t1 MR t2) [] (Arrow (List t1) MR (List t2))) [] [].
eapply term_abs. eapply term_abs.
apply @term_mfix with (R := map_call) (MR := map_call :: MR) (x := VarZ).
- apply mfix_bodies_cons.
  + apply map_body.
  + apply mfix_bodies_nil.
- eapply term_call.
  + apply VarZ.
  + apply VarZ.
  + eapply term_var. eapply VarZ.
Defined.
End map_term.

Goal False.
set (denote_term (map Nat Nat []) tt) as e. cbn in e.
simp denote_term in e. cbv in e. simp denote_term in e.
assert (e = EnTree.spin).
cbv. simp denote_term.

Check (denote_term (map Nat Nat []) tt).

(*
\(f : t1 =MR=> t2) (l : List t1) ->_MR  mfix (map_rec :: MR) VarZ 

(rec l => match l with nil => nil | cons h t => cons (lift f h) (call (VarZ) (VarZ) t) ) end  
call... (l)

*)
