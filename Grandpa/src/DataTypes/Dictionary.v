Require List.
Require Import DataTypes.List.Count.
Require Import DataTypes.Option.

Import List.ListNotations.

Require Import Classes.Eqb.
Require Import Classes.Functor.
Require Import Instances.List.

Section Dictionary.

Open Scope list_scope.
Open Scope eqb_scope.

Context {K V:Type}.

Variant Dictionary T1 T2: Type :=
  | DictionaryC (l : list (T1*T2)) : Dictionary T1 T2.

Arguments DictionaryC {T1 T2}.

Definition empty:= @DictionaryC K V nil.

Context `{eqb_k: Eqb K}.
Context `{eqb_k_laws: @EqbLaws K eqb_k}.
Context `{eqb_v: Eqb V}.
Context `{eqb_v_laws: @EqbLaws V eqb_v}.

Definition to_list (dict:Dictionary K V): list (K*V)
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
      if k =? k'
      then (k,v) :: remain
      else 
        (k',v'):: add_aux element remain
  end.

Lemma add_aux_adds_new_at_end (k:K) (v:V) (l:list(K*V))
  : (forall k' , List.In k' (List.map fst l) -> k =? k' = false)
  -> add_aux (k,v) l = l++((k,v)::nil). 
Proof.
  induction l as [|[k3 v3] l HInd];intro Hin.
  - reflexivity.
  - simpl.
    assert (k =? k3 = false) as H.
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
  match List.find (fun p =>k =? (fst p)) (to_list dict) with
  | Some (_,v)=>Some v
  | None => None
  end.

Lemma lookup_eqb_rewrite {k1 k2} d:
  k1 =? k2 = true -> lookup k1 d = lookup k2 d.
Proof.
  intro eqH.
  destruct d as [l].
  induction l as [| (k3,v) remain].
  - reflexivity.
  - unfold lookup.
    simpl.
    destruct (k1 =? k3) eqn:k1_k3.
    + rewrite eqb_symmetry in eqH.
      rewrite (@eqb_transitivity K eqb_k eqb_k_laws k2 k1 k3 eqH k1_k3).
      reflexivity.
    + enough(
      k2 =? k3 = false
      ) as Hend.
      rewrite Hend.
      assumption.
      destruct (k2 =? k3) eqn:H4.
      * pose (@eqb_transitivity _ _ _ k1 k2 k3 eqH H4) as H5.
        rewrite H5 in k1_k3.
        assumption.
      * reflexivity.
Qed.

Lemma add_really_adds d :
   forall k v, lookup k (add k v d) = Some v.
Proof.
  destruct d as [l].
  unfold lookup.
  simpl.
  induction l as [|[k' v'] remain Hind];intros k v;simpl.
  - rewrite eqb_reflexivity.
    reflexivity.
  -  destruct (k =? k') eqn:k_eq_k.
    + simpl.
      rewrite eqb_reflexivity.
      reflexivity.
    + simpl.
      rewrite k_eq_k.
      apply Hind.
Qed.

Lemma add_really_adds_eqb_k d :
  forall k1 k2 v,
  k1 =? k2 = true ->
   lookup k1 (add k2 v d) = Some v.
Proof.
  destruct d as [l].
  unfold lookup.
  simpl.
  induction l as [|[k v'] remain Hind];intros k1 k2 v H;simpl.
  - rewrite H.
    reflexivity.
  - destruct (k2 =? k) eqn:k2_eq_k.
    + simpl.
      rewrite H.
      reflexivity.
    + simpl.
      destruct (k1 =? k) eqn:k1_eq_k.
      * rewrite (eqb_symmetry) in H.
        apply (eqb_transitivity k2 k1 k H) in k1_eq_k.
        rewrite k2_eq_k in k1_eq_k.
        inversion k1_eq_k.
      * apply Hind.
        assumption.
Qed.

Lemma lookup_add_result d :
  forall k1 k2 v, 
    let result := lookup k1 (add k2 v d) 
    in
      (k1 =? k2 = true /\ result = Some v) \/ (result = lookup k1 d).
Proof.
  intros k1 k2.
  destruct (k1 =? k2) eqn:k_eqb.
  - simpl.
    left.
    split. auto.
    auto using add_really_adds_eqb_k.
  - right.
    destruct d as [l].
    induction l as [|[k' v'] remain Hind].
    + unfold lookup. simpl. rewrite k_eqb. auto. 
    + destruct (k2 =? k') eqn:k2_eq_k'.
      * unfold lookup.
        simpl.
        rewrite k2_eq_k'.
        simpl.
        rewrite k_eqb.
        destruct (k1 =? k') eqn:k1_eq_k'.
        ++ rewrite eqb_symmetry in k1_eq_k'. 
           pose (eqb_transitivity k2 k' k1 k2_eq_k' k1_eq_k') as contra.
           rewrite eqb_symmetry in contra.
           rewrite k_eqb in contra.
           discriminate contra.
        ++ auto.
      * unfold lookup.
        simpl.
        rewrite k2_eq_k'.
        simpl.
        unfold lookup in Hind.
        simpl in Hind.
        destruct (k1 =? k');auto.
Qed.

Definition from_list (l:list (K*V)): Dictionary K V
  :=
  List.fold_right (fun p dict => add (fst p) (snd p) dict ) empty l.


Definition  update_with (k:K) (v:V) (f:option V -> V -> V) (dict:Dictionary K V): Dictionary K V
  := add k (f (lookup k dict) v) dict.


Lemma update_lookup k v f d :
 lookup k (update_with k v f d)= Some (f (lookup k d) v).
Proof.
  unfold update_with.
  rewrite add_really_adds.
  reflexivity.
Qed.

Lemma update_lookup_k_eqb k1 k2 v f d :
 k1 =? k2 = true ->
 lookup k1 (update_with k2 v f d)= Some (f (lookup k2 d) v).
Proof.
  intro H.
  unfold update_with.
  rewrite (add_really_adds_eqb_k).
  reflexivity.
  assumption.
Qed.


Lemma update_lookup_keeps_others_k_eqb k1 v f d  
  :  forall k2, k2 =? k1 = false -> 
  lookup k2 (update_with k1 v f d) = lookup k2 d.
Proof.
  destruct d as [l].
  induction l as [|(k3,v3) remain Hind].
  - intros k2 H.
    unfold update_with.
    unfold lookup.
    simpl.
    rewrite H.
    reflexivity.
  - intros k2 H.
    unfold update_with.
    unfold lookup.
    simpl.
    destruct (k1 =? k3) eqn:k1_k3.
    + assert (k2 =? k3 = false) as k2_k3.
      {
        destruct (k2 =? k3) eqn:k2_k3.
        - rewrite (eqb_symmetry) in k2_k3.
          pose (eqb_transitivity _ _ _ k1_k3 k2_k3) as contra.
          rewrite (eqb_symmetry) in contra.
          rewrite contra in H.
          exact H.
        - reflexivity.
      }
      rewrite k2_k3.
      simpl.
      rewrite H.
      reflexivity.
    + simpl.
      destruct (k2 =? k3) eqn:k2_k3. 
      * reflexivity.
      * unfold lookup in Hind.
        unfold update_with in Hind.
        simpl in Hind.
        unfold lookup in Hind.
        simpl in Hind.
        apply Hind.
        assumption.
Qed.


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

Lemma wellformed_means_unique_elements d (wf:WellFormedDict d) 
  : forall k, 
    count k (map fst (to_list d)) <= 1.
Proof.
  destruct d as [l].
  intro k.
  induction l as [|[k2 v2] l Hind].
  - simpl.
    unfold count.
    auto.
  - simpl.
    rewrite count_cons.
    (*
       proof 
       WellFormedDict (DictionaryC l) -> DictionaryC l = from_list (rev l)
       and use it with ++ in 
       l = l1 ++ (k,v) :: l2 
    *)
    Admitted.

Fixpoint eqb_aux (l: list (K * V)) (d:Dictionary K V) : bool
  :=
  match l with
  | nil => true
  | (k,v)::r1 => 
      match lookup k d with
      | Some v' => (v =? v') && eqb_aux r1 d
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

Definition delete (k:K) (dict:Dictionary K V): Dictionary K V:=
  from_list (List.filter (fun t =>  k =? (fst t))  (to_list dict)).

Lemma delete_works (dict:Dictionary K V) 
  : forall k, lookup k (delete k dict) =None.
Proof.
  intro k.
  destruct dict.
  unfold lookup.
  induction l.
  - auto.
  - Admitted.



Definition PreserveKeys (f: Dictionary K V -> Dictionary K V) 
  := forall d k
    , is_some (Dictionary.lookup k d) = true 
      <-> 
      is_some (Dictionary.lookup k (f d)) = true.


End Dictionary.

