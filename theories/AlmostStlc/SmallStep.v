Require Export Syntax.
Require Export TypedVar.
From Equations Require Import Equations Signature.

Equations subst_term {Γ R} (t1 t2 : type) (e1 : term t2 Γ R) (e2 : term t1 Γ R) (x : var t1 Γ)

Equations subst_term {Γ R} (t1 t2 : type) (e1 : term t2 (t1 :: Γ) R) (e2 : term t1 Γ R) :
  term t2 Γ R :=
  subst_term t1 Nat (term_const n _ R) e2 := term_const n Γ R;
  subst_term t1 (List tl) (term_nil tl _ R) e2 := term_nil tl Γ R;
  (* this example shows that my type is not general enough, need to be able to go under binders and need *)
  subst_term t1 (List tl) (term_cons tl _ R eh et) e2 := term_cons tl Γ R (subst_term _ _ eh e2) (subst_term _ _ et e2)

.
