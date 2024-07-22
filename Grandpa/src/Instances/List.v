Require Import Coq.Lists.List.
Import ListNotations.

Require Import Classes.Eqb.
Require Import Classes.Functor.
Require Import Classes.Math.Monoid.




Section Eqb.
Fixpoint eqb_list {A : Type} `{Eqb A} (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: l1', x2 :: l2' => (eqb x1 x2) && (eqb_list l1' l2')
  | _, _ => false
  end.

Lemma eqb_list_reflexivity {A : Type} `{EqbLaws A} : forall (l : list A), eqb_list l l = true.
Proof.
  intros l.
  induction l; simpl.
  - reflexivity.
  - rewrite eqb_reflexivity, IHl. reflexivity.
Qed.

Lemma eqb_list_symmetry {A : Type} `{EqbLaws A} : forall (l1 l2 : list A), eqb_list l1 l2 = eqb_list l2 l1.
Proof.
  intros l1.
  induction l1 as [| x1 l1' IH]; destruct l2 as [| x2 l2']; simpl; try reflexivity.
  - rewrite eqb_symmetry, IH. reflexivity.
Qed.

Lemma eqb_list_transitivity {A : Type} `{EqbLaws A} : forall (l1 l2 l3 : list A), eqb_list l1 l2 = true -> eqb_list l2 l3 = true -> eqb_list l1 l3 = true.
Proof.
  intros l1.
  induction l1 as [| x1 l1' IH]; destruct l2 as [| x2 l2'], l3 as [| x3 l3']; simpl in *; try discriminate.
  - reflexivity.
  - intros H2 H3. apply andb_prop in H2 as [H12_eq H12_list]. apply andb_prop in H3 as [H23_eq H23_list].
    rewrite (eqb_transitivity _ _ _ H12_eq H23_eq), (IH _ _ H12_list H23_list). reflexivity.
Qed.

Instance EqbList {A : Type} `{Eqb A} : Eqb (list A) :=
{
  eqb := eqb_list
}.

#[global]
Existing Instance EqbList.

Instance EqbLawsList {A : Type} {eqb_a:Eqb A} `{@EqbLaws A eqb_a} : EqbLaws (list A) :=
{
  eqb_reflexivity := eqb_list_reflexivity;
  eqb_symmetry := eqb_list_symmetry;
  eqb_transitivity := eqb_list_transitivity
}.

#[global]
Existing Instance EqbLawsList.


Lemma eqb_list_eq {A:Type} `{eqb_a:Eqb A, eqb_a_laws: @EqbLaws A eqb_a, eqb_a_eq : @EqbEq A eqb_a}  (x y : list A) : eqb x y = true <-> x = y.
Proof.
  split.
  - generalize y. 
    induction x; intro y0; destruct y0 as [|y' ys];simpl.
    + auto.
    + intro H. inversion H. 
    + intro H. inversion H. 
    + intro H. apply andb_prop in H. destruct H as [a_eqb x_eqb].
      rewrite eqb_eq in a_eqb.
      apply IHx in x_eqb.
      rewrite a_eqb, x_eqb.
      auto.
  - intro H.
    rewrite H.
    apply eqb_reflexivity.
Qed.

Instance EqbEq_list {A : Type} `{eqb_a:Eqb A} `{@EqbLaws A eqb_a} `{@EqbEq A eqb_a} : EqbEq (list A) :=
{
  eqb_eq := eqb_list_eq;
}.

#[global]
Existing Instance EqbEq_list.
End Eqb.

Section Functor.
Instance Functor_list : Functor list := {
  map := List.map
}.

#[global]
Existing Instance Functor_list.


Instance FunctorLaws_list : FunctorLaws list.
Proof.
  split.
  - apply List.map_id.
  - Admitted.

#[global]
Existing Instance FunctorLaws_list.

End Functor.

Section Math.

Instance SemigroupList {A:Type}: Semigroup (list A) 
:={
  plus := @List.app A
}.

#[global]
Existing Instance SemigroupList.

#[refine]
Instance SemigroupLawsList {A:Type}  : @SemigroupLaws (list A) SemigroupList
:={
}.
Proof.
  intros x y z.
  apply List.app_assoc.
Qed.

#[global]
Existing Instance SemigroupLawsList.

Instance MonoidList {A:Type}: Monoid (list A) 
:={
  neutro:= []
}.

#[global]
Existing Instance MonoidList.

#[refine]
Instance MonoidLawsList {A:Type}  : @MonoidLaws (list A) SemigroupList SemigroupLawsList MonoidList
:={
}.
Proof.
  - intro t.
    reflexivity.
  - intro t.
    apply List.app_nil_r.
Qed.

#[global]
Existing Instance MonoidLawsList.

End Math.
