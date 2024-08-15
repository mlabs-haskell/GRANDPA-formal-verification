Require List.

Lemma fold_left_preserves_property_aux {A B} (P:A->Prop) (f: A -> B -> A)
  (at_f:forall a b, P a -> P (f a b))
  : forall l a0, P a0 -> P (List.fold_left f l a0 ).
Proof.
  induction l.
  - auto.
  - simpl.
    auto using IHl.
Qed.

Lemma fold_left_preserves_property {A B} 
  (P:A->Prop) 
  (f: A -> B -> A) 
  (l:list B) 
  (a0:A) 
  (at_a0:P a0)
  (at_f:forall a b, P a -> P (f a b))
  : P (List.fold_left f l a0).
Proof.
  apply fold_left_preserves_property_aux;auto.
Qed.

Lemma fold_left_same_action_on_element_means_same {A B C} 
  (h: A -> C)
  (f: A -> B -> A)
  (g: A -> B -> A)
  (hf_is_hg:forall a b, h (f a b) = h (g a b) )
  (hyp : forall a1 a2 l, h a1 = h a2 -> List.fold_left g l a1  = List.fold_left g l a2)
  :
  forall l a0,
    h (List.fold_left f l a0)
    =
    h (List.fold_left g l a0).
Proof.
  induction l as [|b1 l IH].
  - auto.
  - Search List.fold_right.
    simpl.
    intro a0.
    rewrite IH.
    rewrite (hyp (f a0 b1) (g a0 b1));auto.
Qed.


