Require Import List.

Module Type Types.

Parameter K:Type.
Parameter V:Type.
Parameter eqb: K -> K -> bool.

End Types.

Module Functions (Types:Types).

Definition K := Types.K.
Definition V := Types.V.
Definition eqb := Types.eqb.

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


Definition add (element: K*V) (dict:Dictionary K V): Dictionary K V
  :=
  match dict with
  | DictionaryC _ _ l=>
      DictionaryC _ _ (add_aux element l)
  end.


Definition lookup : K -> Dictionary K V -> option V.
Admitted.

Definition from_list : list (K*V) -> Dictionary K V.
Admitted.

Definition  to_list : Dictionary K V -> list (K*V). 
Admitted.


Definition  update_with : K -> (V -> V -> V)-> Dictionary K V -> list (K*V). 
Admitted.

End Functions.
