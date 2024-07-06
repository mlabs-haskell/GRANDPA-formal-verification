Require Import Dictionary.
Require Import Functors.
Require Import ListFacts.

Section UnitSection.

End UnitSection.

Variant Unit := | UnitC.

Definition eqb_unit (x y :Unit) := true. 

Lemma eqb_unit_reflexive : forall {x:Unit}, eqb_unit x x = true.
Proof. reflexivity. Qed.

Lemma eqb_unit_symmetric: forall {x y:Unit} {b}, eqb_unit x y =b -> eqb_unit x y = b.
Proof. auto. Qed.

Lemma eqb_unit_transitive: forall {k1 k2 k3:Unit}, eqb_unit k1 k2 =true -> eqb_unit k2 k3 = true -> eqb_unit k1 k3 = true.
Proof. auto. Qed.




Section DictionarySet.

Context {K:Type}.

Variable eqb_k: K -> K -> bool.
Axiom eqb_k_reflexive : forall {k:K}, eqb_k k k = true.
Axiom eqb_k_symmetric: forall {k1 k2:K} {b}, eqb_k k1 k2 =b -> eqb_k k2 k1 = b.
Axiom eqb_k_transitive: forall {k1 k2 k3:K}, eqb_k k1 k2 =true -> eqb_k k2 k3 = true -> eqb_k k1 k3 = true.

Variant DictionarySet (T:Type) : Type
  :=
  | SetC (d: Dictionary.Dictionary T Unit): DictionarySet T.

Arguments SetC {T}.

Definition get_dictionary (d:DictionarySet K) : Dictionary K Unit
  := 
  match d with
  | SetC d => d
  end.

Definition to_list (d:DictionarySet K) : list K
  := map fst (Dictionary.to_list (get_dictionary d)).

Definition from_list (l:list K) 
  :DictionarySet K
  := 
    SetC (Dictionary.from_list eqb_k (map (fun n => (n,UnitC)) l)).

Definition is_empty (d:DictionarySet K) : bool
  := 
  match to_list d with
  | List.nil => true
  | _ => false
  end.



Definition IsSubset (l r : DictionarySet K) : Prop 
  := 
  forall (k: K), 
    (count eqb_k k  (to_list l)
    <= count eqb_k k (to_list r))%nat.

Definition intersection (l r : DictionarySet K) : DictionarySet K.
Admitted.

Definition difference (l r : DictionarySet K) : DictionarySet K.
Admitted.

Lemma is_subset_transitive  
  (S1 S2 S3 : DictionarySet K )
  (s1_s2 : IsSubset S1 S2)
  (s2_s3 : IsSubset S2 S3)
  : IsSubset S1 S3.
Proof.
  unfold IsSubset.
  intro k. 
  pose (s1_s2 k) as ineq1.
  pose (s2_s3 k) as ineq2.
  transitivity (count eqb_k k (to_list S2));auto.
Qed.


End DictionarySet.
