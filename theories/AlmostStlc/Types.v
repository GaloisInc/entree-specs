Inductive type : Type :=
  | Nat : type
  | List : type -> type
  | Pair : type -> type -> type
  | Arrow : type -> (list (list (type * type))) -> type -> type
.
Notation ctx := (list type).
Notation call_frame := (list (type * type)).
Notation mfix_ctx := (list call_frame).

Notation vtype := type.
