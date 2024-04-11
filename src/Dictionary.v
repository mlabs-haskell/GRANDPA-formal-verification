Require Import List.


Section Dictionary.

Context {K V:Type}.

Variant Dictionary K V: Type :=
  | DictionaryC (l : list (K*V)) : Dictionary K V.

Definition empty:= DictionaryC K V nil.

Variable eqb: K -> K -> bool.

Definition  to_list (dict:Dictionary K V): list (K*V)
  := 
  match dict with
  | DictionaryC _ _ l => l
  end.

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

Definition add (k:K) (v:V) (dict:Dictionary K V): Dictionary K V
 := DictionaryC _ _ (add_aux (k,v) (to_list dict)).

Definition lookup (k:K) (dict: Dictionary K V): option V
  :=
  match find (fun p => eqb k (fst p)) (to_list dict) with
  | Some (_,v)=>Some v
  | None => None
  end.

Definition from_list (l:list (K*V)): Dictionary K V
  :=
  fold_right (fun p dict => add (fst p) (snd p) dict ) empty l.


Definition  update_with (k:K) (v:V) (f:option V -> V -> V) (dict:Dictionary K V): Dictionary K V
  := add k (f (lookup k dict) v) dict.


(*

Definition eq_iff_to_list_eq (eqb_eq:forall k k', eqb k k'=true <-> k=k') (decidable_k:forall k k':K, {k=k'}+{k<>k'})
  (decidable_v:forall v v':V, {v=v'}+{v<>v'})
  (d1 d2:Dictionary K V)
  :  d1 = d2 <-> (to_list d1) = (to_list d2). 
Proof.
  split.
  - intro H.
    destruct d1 as [l1].
    destruct d2 as [l2].
    simpl.
    injection H.
    auto.
  - 
  Admitted.

Definition eq_dec (eqb_eq:forall k k', eqb k k'=true <-> k=k') (decidable_k:forall k k':K, {k=k'}+{k<>k'})
  (decidable_v:forall v v':V, {v=v'}+{v<>v'})
  (d1 d2:Dictionary K V)
  : {d1 = d2} + {d1 <> d2}.
Proof.
  Search ({?l = ?l2} + {?l <> ?l2}).
  assert (forall (k k':K) (v v':V), {(k,v)=(k',v')}+{(k,v)<>(k',v')}) as decidable_pair_aux.
    {
      intros k k' v v'.
      pose (decidable_k k k') as H1.
      pose (decidable_v v v') as H2.
      destruct H1,H2.
      - left.
        rewrite e.
        rewrite e0.
        reflexivity.
      - right.
        unfold not.
        intro H.
        rewrite pair_equal_spec in H.
        destruct H.
        auto.
      - right.
        unfold not.
        intro H.
        rewrite pair_equal_spec in H.
        destruct H.
        auto.
      - right.
        unfold not.
        intro H.
        rewrite pair_equal_spec in H.
        destruct H.
        auto.
    }
    assert (forall p p':K*V, {p=p'}+ {p<>p'}) as decidable_pair.
    {
      intros [k v] [k' v'].
      apply decidable_pair_aux.
      }
  pose (list_eq_dec decidable_pair (to_list d1) (to_list d2)) as H.
  destruct H as [H | H].
  - left.
    apply (eq_iff_to_list_eq eqb_eq  decidable_k decidable_v).
    auto.
  - right.
    unfold not.
    rewrite (eq_iff_to_list_eq eqb_eq  decidable_k decidable_v). 
    auto.
Qed.
*)


End Dictionary.

