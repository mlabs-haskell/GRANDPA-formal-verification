Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.

Require Coq.Vectors.VectorDef.

Declare Scope functor_scope.
Delimit Scope functor_scope  with functor.


Class Functor (f : Type -> Type) := {
  map : forall {A B : Type}, (A -> B) -> f A -> f B
}.

Infix "<$>" := map (at level 28, left associativity, only parsing) : functor_scope.
Notation "x <$ m" := (map (const x) m )(at level 28, left associativity, only parsing) : functor_scope.

Class FunctorLaws (f : Type -> Type) `{Functor f} := {
  map_id : forall (A : Type) (x : f A), map (@id A) x = x;
  map_comp : forall (A B C : Type) (g : B -> C) (h : A -> B) (x : f A),
    map (compose g h) x = map g (map h x)
}.


(* TODO: Add a proper module for vectors

Definition VectorWrapper (n:nat) (A:Type) 
  :Type
  :=    Coq.Vectors.VectorDef.t A n. 

Definition coerceVector {n:nat} {A:Type} 
  (v:VectorDef.t A n) : VectorWrapper n A 
  := v.

Instance Functor_vector {n} : Functor (VectorWrapper n) := {
  map := fun {A} {B} (f:A -> B) v => VectorDef.map f v
}.
 *)
