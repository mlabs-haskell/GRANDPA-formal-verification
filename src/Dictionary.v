Require Import List.

Definition Dictionary (K' V':Type) : Type.
Admitted.

Section Dictionary.

Context {K V:Type}.

Definition empty : Dictionary K V.
Admitted.

(*
Variant Dictionary K V: Type :=
  | DictionaryC (l : list (K*V)) : Dictionary K V.

Definition empty:= DictionaryC K V nil.



Fixpoint add_aux (element: K*V) (dict:list (K*V)): list (K*V)
  :=
  match dict with
  | nil => (element :: nil)
  | ((k',v'):: remain) => 
      let (k,v) := element 
      in
      if eqb k k' 
      then (k,v) :: remain
      else 
        (k',v'):: add_aux element remain
  end.

 *)

Variables eqb_k: K -> K -> bool.

Definition add (k:K) (v:V) (dict:Dictionary K V): Dictionary K V.
Admitted.
  (*  :=
  match dict with
  | DictionaryC _ _ l=>
      DictionaryC _ _ (add_aux (k,v) l)
  end.
  *)


Definition lookup : K -> Dictionary K V -> option V.
Admitted.

Definition from_list : list (K*V) -> Dictionary K V.
Admitted.

Definition  to_list : Dictionary K V -> list (K*V). 
Admitted.


Definition  update_with : K -> (option V -> V -> V)-> Dictionary K V -> Dictionary K V. 
Admitted.

End Dictionary.

