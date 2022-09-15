Require Export MrecMonad.
Require Export HeterogeneousRelations.
Require Export EnTreeDefinition.
Require Export Syntax.
From Coq Require Import Lists.List.

From Equations Require Import Equations Signature.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Fixpoint denote_rec_ctx' (R: list (Type * Type) ) : Type@{entree_u} :=
  match R with
  | nil => void
  | cons (T1, _)  R => T1 + denote_rec_ctx' R end.
(*
Definition fold_rec_ctx_inr' (Rt Rc : list (Type * Type)) T1 T2 (arg : denote_rec_ctx' Rt Rc) : denote_rec_ctx' Rt ((T1,T2) :: Rc) :=
  inr arg.
*)
Fixpoint encoded_rec_ctx' (R : list (Type * Type)) : EncodedType (denote_rec_ctx' R) :=
  match R with
  | nil => fun _ => void
  | cons (_, T2) R => fun x => match x with 
                             | inl y => T2
                             | inr y => encoded_rec_ctx' R y end end.

Instance encoded_rec_ctx'' R : EncodedType (denote_rec_ctx' R) :=
  encoded_rec_ctx' R.


(* maybe I wrote this wrong *)
Fixpoint denote_type (t : type) : Type@{entree_u} :=
  match t with
  | Nat => nat
  | List t => list (denote_type t)
  | Arrow t1 R t2 => 
      let R' := List.map (fun '(t1,t2) => (denote_type t1, denote_type t2)) R in
      denote_type t1 -> mtree (denote_rec_ctx' R') (denote_type t2)
  end.
(*need to fix denote *)
(* parameterizing denote_type on a translation doesn't work because the recursion is not well founded*)

Definition denote_rec_ctx (R : rec_ctx) : Type@{entree_u} :=
  denote_rec_ctx' (List.map (fun '(t1,t2) => (denote_type t1, denote_type t2)) R).

Fixpoint denote_ctx (Γ : ctx) : Type@{entree_u} :=
  match Γ with
  | nil => unit
  | t :: Γ' => denote_type t * denote_ctx Γ' end.

Equations index_ctx {t : type} {Γ} (x : var t Γ) (hyps : denote_ctx Γ) : denote_type t :=
  index_ctx (VarZ x Γ') (v, _) := v;
  index_ctx (VarS v1 v2 Γ' y) (_, hyps) := index_ctx y hyps.

(* this part is frustrating, I need some kind of translation between these types
   actually there should not be, args : denote_rec_ctx R
 *)
(*maybe if I do this part without equations it will work better *)
Equations inject_rec_ctx {p : type * type} {R} (x : var p R) (arg : denote_type (fst p)) : denote_rec_ctx R :=
  inject_rec_ctx (VarZ (t1,t2) R') arg := inl arg;
  inject_rec_ctx (VarS _ (t1',t2') R' y) arg := inr (inject_rec_ctx y arg).
(*
Fixpoint inject_rec_ctx' {t1 t2 : type} {R} (x : var (t1,t2) R) : denote_type t1 -> denote_rec_ctx :=
  match x return with
  | VarZ *)

Lemma encodes_inject p R (x : var p R) (arg : denote_type (fst p)) : encodes (inject_rec_ctx x arg) = denote_type (snd p).
revert arg. induction x.
- destruct x. cbn. intros. simp inject_rec_ctx. auto.
- destruct x. destruct y. cbn. intros. simp inject_rec_ctx.
Qed.
Print Assumptions encodes_inject.

Definition decode_inject {p : type * type} {R : rec_ctx} {arg : denote_type (fst p)} (x : var p R) (response : encodes (inject_rec_ctx x arg)) : 
  denote_type (snd p).
revert response. revert arg. induction x.
- intros arg response. destruct x. cbn in *. exact response.
- intros. destruct x. destruct y. exact (IHx arg response).
Defined.
Print Assumptions decode_inject.
(*
(* we still might be able to do better, give it a bit more thought before moving on to another task for today*)
Equations decode_inject {p : type * type} {R : rec_ctx} {arg : denote_type (fst p)} (x : var p R) (response : encodes (inject_rec_ctx x arg)) : 
  denote_type (snd p) :=
  decode_inject (VarZ x Γ') response := _;
  decode_inject (VarS _ v Γ' y) _ := decode_inject y _.
Next Obligation.
  exact response.
Defined.
Next Obligation.
  exact arg.
Defined.

Print Assumptions decode_inject.
*)
(*
Next Obligation.
cbn in response.

  decode_inject (VarZ (t1',t2') Γ') (inl response) := response;
  decode_inject (VarS (t1',t2') (t3,t4) Γ' y) (inr response) := decode_inject y response.

Definition decode_inject {t1 t2 : type} {R : rec_ctx} {arg : denote_type t1} (x : var (t1,t2) R) (response : encodes (inject_rec_ctx x arg)) :  denote_type t2.
revert response. revert arg. induction x. dependent induction x.
- simp inject_rec_ctx. cbn. intros. auto.
- destruct y. simp inject_rec_ctx. cbn. eapply IHx; auto.
Defined.
Print Assumptions decode_inject.
*)
(* Axioms: JMeq_eq, this is a problem for executability*)
(*
Unable to build a covering for:
decode_inject decode_inject t1 t2 R arg x response
*)
(*
Equations decode_inject {t1 t2 : type} {R : rec_ctx} {arg : denote_type t1} (x : var (t1,t2) R) (response : encodes (inject_rec_ctx x arg)) : 
  denote_type t2 :=
  decode_inject (VarZ x Γ') (inl response) := response;
  decode_inject (VarS v1 v2 Γ' y) (inr response) := decode_inject y response.
*)

(* current problem is that is that I can't get the syntax to both put denote_bodies in scope in denote_term mfix
   and realize it is decreasing
 *)
Equations denote_term {t : type} (Γ : ctx) (R : rec_ctx) (e : term t Γ R) (hyps : denote_ctx Γ) : 
  mtree (denote_rec_ctx R) (denote_type t) := 
  denote_term Γ R (term_const n Γ R) hyps := Ret n;
  denote_term Γ R (term_nil t Γ R) hyps := Ret nil;
  denote_term Γ R (term_cons t Γ R eh et) hyps := h' <- denote_term Γ R eh hyps;; 
                                                  t' <- denote_term Γ R et hyps;;
                                                  Ret (h' :: t');
  denote_term Γ R (term_match_nat t _ _ en eZ eS) hyps := EnTree.spin;
  denote_term Γ R (term_match_list t1 t2 _ _ el enil econs) hyps := EnTree.spin;
  denote_term Γ R (term_var t Γ R x) hyps := Ret (index_ctx x hyps);

  denote_term Γ R (term_app t1 t2 Γ R e1 e2) hyps := f <- denote_term Γ R e1 hyps;;
                                                     x <- denote_term Γ R e2 hyps;;
                                                     f x;
  denote_term Γ R (term_abs t1 t2 Γ R R' e) hyps := Ret (fun (x : denote_type t1) => denote_term (t1 :: Γ) R' e (x, hyps) );
  denote_term Γ R (term_call t1 t2 Γ R x e) hyps := arg <- denote_term Γ R e hyps;;
                                                    out <- call (inject_rec_ctx x arg);;
                                                    (* should get decode_inject into a sane def*)
                                                    ret (decode_inject x out);
  denote_term Γ R (term_mfix t Γ R' R bodies e) hyps := interp_mtree (denote_bodies Γ R' R' bodies hyps) (denote_term Γ R' e hyps)
where denote_bodies (Γ : ctx) (R R' : rec_ctx) (bodies : mfix_bodies Γ R R') (hyps : denote_ctx Γ) (arg : denote_rec_ctx R') : 
  mtree (denote_rec_ctx R) (encodes arg) := 
  denote_bodies Γ' R1 (cons (t1,t2) R2) (mfix_bodies_cons Γ' R1 t1 t2 R2 ebody bodies') hyps' (inl arg') := 
    denote_term _ R1 ebody (arg',hyps');
  denote_bodies Γ' R1 (cons (t1,t2) R2) (mfix_bodies_cons Γ' R1 t1 t2 R2 ebody bodies') hyps' (inr arg') := 
    denote_bodies Γ' R1 R2 bodies' hyps' arg'.
Print Assumptions denote_term. (* closed under global context *)

