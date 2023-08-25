Require Export SyntaxSeq.


Inductive pcf_term :=
  | pcf_const (n : nat) : pcf_term
  | pcf_nil : pcf_term
  | pcf_cons (h t : pcf_term) : pcf_term
  | pcf_pair (l r : pcf_term) : pcf_term
  | pcf_abs (body : pcf_term) : pcf_term
  | pcf_var (n : nat) : pcf_term
.
