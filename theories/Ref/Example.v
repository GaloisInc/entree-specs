From ITree Require Import
     Basics.Basics
     Basics.Tacs
     Basics.HeterogeneousRelations
 .
From ITree Require Import Basics.Monad.
From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Core.SubEvent
     Eq.Eqit
     Ref.Padded
     Ref.EnTreeSpecDefinition
     Ref.MRecSpec
     Ref.SpecM
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope list_scope.

Definition halve_specm {Γ : call_stack} {E} `{EncodedType E} 
           (l : list nat) : SpecM E Γ (list nat * list nat) :=
  MrecS (list nat) (fun _ => list nat * list nat)%type
         (fun l => 
           match l with
           | nil => ret (nil, nil)
           | x :: nil => ret (x :: nil, nil)
           | x :: y :: t => '(l1,l2) <- CallS t;;
                         ret (x :: l1, y :: l2) end
        ) l.

Definition merge_specm {Γ : call_stack} {E} `{EncodedType E} 
           (l1 l2 : list nat) : SpecM E Γ (list nat) :=
  MrecS (list nat * list nat) (fun _ => list nat)
        (fun '(l1, l2) => 
           match (l1, l2) with
           | (nil, _) => ret l2
           | (_, nil) => ret l1
           | (x :: tx, y :: ty) =>
               if Nat.leb x y
               then
                 l <- CallS (tx, y :: ty);;
                 ret (x :: l)
               else
                 l <- CallS (x :: tx, ty);;
                 ret (y :: l)
                end

        ) (l1,l2).

Definition sort_specm {Γ : call_stack} {E} `{EncodedType E} 
           (l : list nat) : SpecM E Γ (list nat) :=
  MrecS (list nat) (fun _ => list nat)
        (fun l => 
           match l with
           | nil => ret nil
           | x :: nil => ret (x :: nil)
           | _ => '(l1,l2) <- halve_specm l;;
                 l1s <- CallS l1;;
                 l2s <- CallS l2;;
                 merge_specm l1s l2s 
           end
        ) l.
(* a closed program is parametric in its call stack *)
