Require Export Syntax.
Require Export Denotation.
Require Import List.
Import ListNotations.
From Equations Require Import Equations Signature.


Section fun_lift.
Context {Γ : ctx} {MR1 MR2 MR3 : mfix_ctx}.
Context {t1 t2 : type}.
Definition fun_lift : term (Arrow (Arrow t1 MR2 t2) MR3 (Arrow t1 (MR1 ++ MR2) t2 ))
                           Γ MR3.
apply term_abs. apply term_abs.
apply term_lift. apply term_app with (t1 := t1).
apply term_var. apply VarS. apply VarZ.
apply term_var. apply VarZ.
Defined.

End fun_lift.

Section plus.
Context {Γ : ctx}.

Definition plus_call : call_frame := [(Nat, Arrow Nat [] Nat)].

Definition plus : term (Arrow Nat [] (Arrow Nat [] Nat)) Γ [].
apply term_abs. apply term_abs.
apply term_mfix with (R := plus_call) (MR := [plus_call]) (x := VarZ plus_call []).
- apply mfix_bodies_cons.
  + eapply term_match_nat.
    * apply term_var. apply VarZ.
    * apply term_abs. apply term_var. apply VarZ.
    * eapply term_app with (t1 := Arrow Nat [] Nat).
      {
        apply term_abs. apply term_abs.
        apply term_app with (t1 := Nat).
        - apply term_var. apply VarS. apply VarZ.
        - apply term_succ. apply term_var. apply VarZ.
      }
      {
        eapply term_call. apply VarZ. apply VarZ. 
        apply term_var. apply VarZ.
      }
  + apply mfix_bodies_nil.
- eapply term_app with (t1 := Nat).
  + apply term_app with (t1 := Arrow Nat [] Nat).
    * apply @fun_lift with (MR1 := [plus_call]).
    * eapply term_call.
      -- apply VarZ.
      -- apply VarZ.
      -- apply term_var. apply VarZ.
  + apply term_var. apply VarS. apply VarZ.
Defined.

End plus.

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
apply term_mfix with (R := map_call) (MR := map_call :: MR) (x := VarZ map_call MR).
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
set (denote_term _ _ (map Nat Nat []) tt) as e. cbn in e.
simp denote_term in e.
Check (denote_term _ _ (map Nat Nat []) tt).

(*
\(f : t1 =MR=> t2) (l : List t1) ->_MR  mfix (map_rec :: MR) VarZ 

(rec l => match l with nil => nil | cons h t => cons (lift f h) (call (VarZ) (VarZ) t) ) end  
call... (l)

*)
