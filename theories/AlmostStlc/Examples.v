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

Definition plus : term (Arrow Nat [] (Arrow Nat [] Nat)) Γ [] :=
term_abs
  (term_abs
     (term_mfix plus_call VarZ
        (mfix_bodies_cons
           (term_match_nat (term_var VarZ) (term_abs (term_var VarZ))
              (term_app
                 (term_abs (term_abs (term_app (term_var (VarS VarZ)) (term_succ (term_var VarZ)))))
                 (term_call VarZ VarZ (term_var VarZ)))) mfix_bodies_nil)
        (term_app (term_app (@fun_lift _ [plus_call] _ _ _ _) 
                            (term_call VarZ VarZ (term_var VarZ))) (term_var (VarS VarZ))))).

End plus.

Section plus'.

Context {Γ : ctx} {MR : mfix_ctx}.

Definition plus_call' : call_frame := [(Pair Nat Nat, Nat) ].

Definition plus' : term (Arrow (Pair Nat Nat) MR Nat) Γ MR :=
term_abs
  (term_mfix plus_call' VarZ
     (mfix_bodies_cons
        (term_split (term_var VarZ)
           (term_match_nat (term_var VarZ) (term_var (VarS VarZ))
              (term_succ
                 (term_call VarZ VarZ (term_pair (term_var VarZ) (term_var (VarS (VarS VarZ))))))))
        mfix_bodies_nil) (term_call VarZ VarZ (term_var VarZ))).

End plus'.

Locate bind_ret_l.

Require Import Paco.paco.

Goal denote_term (term_app (@plus' [] []) (term_pair (term_const 1) (term_const 1))) tt ≈ 
       Ret 2.
simp denote_term. repeat setoid_rewrite bind_bind. 
unfold plus'. simp denote_term. do 4 setoid_rewrite bind_ret_l. 
simp term_call. simp denote_term. simp denote_mfix_ctx. unfold plus_call'.
simp denote_var.
match goal with |- mapE ?h (interp_mtree ?MR ?R ?t ?x ?f ?m) ≈ _ => 
                  idtac MR;
                  idtac R;
                  idtac t;
                  idtac x;
                  idtac f;
                  idtac m
end.
(*next thing to do is *)
s
unfold plus
simp denote_call_frame. setoid_rewrite bind_ret_l.

setoid_rewrite bind_ret_l.
setoid_rewrite bind_ret_l.
unfold Monad.ret. cbn. 
simp index_ctx.

 setoid_rewrite index_ctx_equation_1.
setoid_rewrite bind_ret_l.
setoid_rewrite bind_ret_l.
 unfold Monad.ret. cbn. 
unfold plus'. simp denote_term. unfold Monad.ret. cbn. 
match goal with |- EnTree.bind (Ret ?x) ?k ≈ Ret 2 => specialize (bind_ret_l x k) as H end.
cbn in H. apply eq_sub_eutt in H.
Print Instances Proper.
 csetoid_rewrite bind_ret_l in H. (*don't see why this rewrite is not working *) setoid_rewrite H at 1.
(* might need more properness*)
setoid_rewrite bind_ret_l.
 setoid_rewrite bind_ret_l at 2.
setoid_rewrite bind_ret_l.
pstep. red. cbn. simp denote_term. cbn. unfold plus'. simp denote_term.
cbn. unfold observe at 1. unfold EnTree.bind, EnTree.subst, EnTree.subst'.  cbn. cbn. cbn. red.
simp denote_term. unfold plus'. simp denote_term. 
repeat setoid_rewrite bind_ret_l. unfold plus_call'. simp denote_term.
simp remove_denote. 
cbn. simp denote_term. pstep. Transparent denote_term. unfold mapE. cbn. unfold mapE'. cbn.
repeat simp denote_mrec_ctx. simp remove. setoid_rewrite denote_var_equation_1. simp denote_var.
 pfold.
(* setoid_rewrite bind_ret_l.
 unfold denote_term.  setoid_rewrite @denote_term_equation_15. *)
Abort.
Section map_term.
Context (t1 t2 : type) (MR : mfix_ctx).

Definition map_call : call_frame := (List t1, List t2) :: nil.


(* should come up with some notations and   *)
Definition map_body : term (List t2) (List t1 :: List t1 :: (Arrow t1 MR t2 :: nil))%list (map_call :: MR)
                           :=
term_match_list (term_var (VarS VarZ)) term_nil
  (term_cons
     (term_lift [map_call] (term_app (term_var (VarS (VarS (VarS (VarS VarZ))))) (term_var VarZ)))
     (term_call VarZ VarZ (term_var (VarS VarZ)))).


Definition map : term (Arrow (Arrow t1 MR t2) [] (Arrow (List t1) MR (List t2))) [] [] :=
term_abs
  (term_abs
     (term_mfix map_call VarZ (mfix_bodies_cons map_body mfix_bodies_nil)
        (term_call VarZ VarZ (term_var VarZ)))).

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
