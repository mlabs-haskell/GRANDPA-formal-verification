Require Import List.
Require Import ListFacts.

Section Dictionary.

Context {K V:Type}.

Variant Dictionary T1 T2: Type :=
  | DictionaryC (l : list (T1*T2)) : Dictionary T1 T2.

Arguments DictionaryC {T1 T2}.

Definition empty:= @DictionaryC K V nil.

Variable eqb_k: K -> K -> bool.
Axiom eqb_k_reflexive : forall {k:K}, eqb_k k k = true.
Axiom eqb_k_symmetric: forall {k1 k2:K} {b}, eqb_k k1 k2 =b -> eqb_k k2 k1 = b.
Variable eqb_v: V -> V -> bool.
Axiom eqb_v_reflexive : forall v:V, eqb_v v v = true.
Axiom eqb_v_symetric : forall {v1 v2:V} {b}, eqb_v v1 v2 =b -> eqb_v v2 v1 = b.

Definition eqb_kv (p1 p2:K*V):bool
  := eqb_k (fst p1) (fst p2) && eqb_v (snd p1) (snd p2). 

Definition  to_list (dict:Dictionary K V): list (K*V)
  := 
  match dict with
  | DictionaryC l => l
  end.

Fixpoint add_aux (element: K*V) (dict:list (K*V)): list (K*V)
  :=
  match dict with
  | nil => (element :: nil)
  | ((k',v'):: remain) => 
      let (k,v) := element 
      in
      if eqb_k k k' 
      then (k,v) :: remain
      else 
        (k',v'):: add_aux element remain
  end.

Lemma add_aux_adds_new_at_end (k:K) (v:V) (l:list(K*V))
  : (forall k' , In k' (List.map fst l) -> eqb_k k k' = false)
  -> add_aux (k,v) l = l++((k,v)::nil). 
Proof.
  induction l as [|[k3 v3] l HInd];intro Hin.
  - reflexivity.
  - simpl.
    assert (eqb_k k k3 = false) as H.
    {
     + apply Hin.
       simpl.
       left.
       reflexivity.
    }
    + rewrite H.
      rewrite HInd.
      * reflexivity.
      * intros k4 H2.
        apply Hin.
        simpl.
        right.
        apply H2.
Qed.


Definition add (k:K) (v:V) (dict:Dictionary K V): Dictionary K V
 := DictionaryC (add_aux (k,v) (to_list dict)).


Definition lookup (k:K) (dict: Dictionary K V): option V
  :=
  match find (fun p => eqb_k k (fst p)) (to_list dict) with
  | Some (_,v)=>Some v
  | None => None
  end.

Lemma add_really_adds d :
   forall k v, lookup k (add k v d) = Some v.
Proof.
  destruct d as [l].
  unfold lookup.
  simpl.
  induction l as [|[k' v'] remain Hind];intros k v;simpl.
  - rewrite eqb_k_reflexive.
    reflexivity.
  -  destruct (eqb_k k k') eqn:k_eq_k.
    + simpl.
      rewrite eqb_k_reflexive.
      reflexivity.
    + simpl.
      rewrite k_eq_k.
      apply Hind.
Qed.


Definition from_list (l:list (K*V)): Dictionary K V
  :=
  fold_right (fun p dict => add (fst p) (snd p) dict ) empty l.


Definition  update_with (k:K) (v:V) (f:option V -> V -> V) (dict:Dictionary K V): Dictionary K V
  := add k (f (lookup k dict) v) dict.


Inductive WellFormedDict : Dictionary K V -> Prop
  := 
    | WellFormedNil : WellFormedDict (DictionaryC nil)
    | WellFormedAdd k v (d: Dictionary K V) (d_well_formed: WellFormedDict d) : WellFormedDict (add k v d).


Lemma update_of_well_formed k v f d 
  : WellFormedDict d -> WellFormedDict (update_with k v f d).
Proof.
  apply WellFormedAdd.
Qed.

Lemma from_list_well_formed l 
  : WellFormedDict (from_list l).
Proof.
  induction l.
  - apply WellFormedNil.
  - simpl.
    auto using WellFormedAdd.
Qed.


Fixpoint eqb_aux (l: list (K * V)) (d:Dictionary K V) : bool
  :=
  match l with
  | nil => true
  | (k,v)::r1 => 
      match lookup k d with
      | Some v' => eqb_v v v' && eqb_aux r1 d
      | None => false
      end
  end.

Definition  eqb (d1 d2:Dictionary K V) : bool
  := 
  eqb_aux (to_list (from_list (to_list d1))) d2
  && eqb_aux (to_list (from_list (to_list d2))) d1.

(*
Lemma eqb_reflexive_true (d:Dictionary K V) (p: WellFormedDict d)
  : eqb d d = true.
Proof.
  destruct d as [l].
  unfold eqb.
  enough (eqb_aux (to_list (from_list (to_list (DictionaryC K V l)))) (DictionaryC K V l) = true) as H.
  + rewrite H. reflexivity.
  + simpl.
    induction l as [|(k,v)].
    - reflexivity.
    - simpl.
      unfold add_aux.

      unfold lookup.
      simpl.
      rewrite eqb_k_reflexive_true.
      simpl.
      rewrite eqb_v_reflexive_true.
      simpl.
*)



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

