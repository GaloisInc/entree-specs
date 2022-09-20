Require Export Syntax.


Section map_term.
Context (t1 t2 : type) (R' : rec_ctx).

Definition map_rec : rec_ctx := (List t1, List t2) :: nil.
(* does this give the flexibility I want with map? 
   what if I want f to be able to make R' calls?
   is that a good idea?
   maybe I should instead prioritize making R calls?
   what is here right now would define map f where 
   f in theory could make calls to map

    


   what if I made a way to merge recursion contexts

   alternatively, I could consider polymorphism for the recursion contexts

   maybe some of those ideas could help solve the issue of defining recursive function that
   can be defined using map of itself
 *)
Definition map_body : term (List t2) (List t1 :: (Arrow t1 map_rec t2 :: nil))%list map_rec.
eapply term_match_list.
- eapply term_var. constructor.
- eapply term_nil.
- eapply term_cons.
  + eapply term_app.
    * eapply term_var. repeat constructor.
    * eapply term_var. constructor.
  + eapply term_call.
    * constructor.
    * eapply term_var. repeat constructor.
Defined.



End map_term.
