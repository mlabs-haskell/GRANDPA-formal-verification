Require Import Dictionary.
Require Import DataTypes.List.Count.

Require Bool.

Require Import Instances.Unit.
Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Instances.List.




Section DictionarySet.

Open Scope bool_scope.
Open Scope eqb_scope.
Open Scope functor_scope.

Context {K:Type}.
Context `{eqb_k: Eqb K}.
Context `{eqb_k_laws: @EqbLaws K eqb_k}.

Variant DictionarySet (T:Type) : Type
  :=
  | SetC (d: Dictionary.Dictionary T Unit): DictionarySet T.

Arguments SetC {T}.

Definition get_dictionary (d:DictionarySet K) : Dictionary K Unit
  := 
  match d with
  | SetC d => d
  end.

Definition add (k:K) (d:DictionarySet K) : DictionarySet K 
  :=
  SetC (Dictionary.add k UnitC (get_dictionary d)).

Definition to_list (d:DictionarySet K) : list K
  := map  fst (Dictionary.to_list (get_dictionary d)).

Definition from_list (l:list K) 
  :DictionarySet K
  := 
    SetC (Dictionary.from_list (map (fun n => (n,UnitC)) l)).

Definition empty 
  : DictionarySet K
  :=
  SetC Dictionary.empty.

Definition is_empty (d:DictionarySet K) : bool
  := 
  match to_list d with
  | List.nil => true
  | _ => false
  end.



Definition IsSubset (l r : DictionarySet K) : Prop 
  := 
  forall (k: K), 
    (count k  (to_list l)
    <= count k (to_list r))%nat.

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
  transitivity (count k (to_list S2));auto.
Qed.


Definition all (f: K -> bool) (s:DictionarySet K) : bool 
  := 
  List.fold_left (fun acc k => acc && (f k) ) (to_list s) true.

Definition or (f: K -> bool) (s:DictionarySet K) : bool 
  := 
  List.fold_left (fun acc k => acc || (f k) ) (to_list s) true.

End DictionarySet.
