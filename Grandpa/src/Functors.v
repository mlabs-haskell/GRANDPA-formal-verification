Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.

Class Functor (f : Type -> Type) := {
  map : forall {A B : Type}, (A -> B) -> f A -> f B
}.


Class FunctorLaws (f : Type -> Type) `{Functor f} := {
  map_id : forall (A : Type) (x : f A), map (@id A) x = x;
  map_comp : forall (A B C : Type) (g : B -> C) (h : A -> B) (x : f A),
    map (compose g h) x = map g (map h x)
}.

Instance Functor_option : Functor option := {
  map := fun {A B : Type} (g : A -> B) (o : option A) =>
    match o with
    | Some x => Some (g x)
    | None => None
    end
}.

Instance FunctorLaws_option : FunctorLaws option.
Proof.
  split.
  - intros A [x |]; simpl.
    + reflexivity.
    + reflexivity.
  - intros A B C g h [x |]; simpl.
    + reflexivity.
    + reflexivity.
Qed.

Instance Functor_list : Functor list := {
  map := List.map
}.

Instance FunctorLaws_list : FunctorLaws list.
Proof.
  split.
  - apply List.map_id.
  - Admitted.

