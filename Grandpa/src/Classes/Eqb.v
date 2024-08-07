Declare Scope eqb_scope.

Delimit Scope eqb_scope  with eqb.

Global Create HintDb eqb.

Class Eqb (T : Type) := {
  eqb : T -> T -> bool
}.

Infix "=?" := eqb (at level 70) : eqb_scope.


Class EqbLaws (T : Type) `{Eqb T} := {
  eqb_reflexivity : forall x : T, eqb x x = true;
  eqb_symmetry : forall x y : T, eqb x y = eqb y x;
  eqb_transitivity : forall x y z : T, eqb x y = true -> eqb y z = true -> eqb x z = true
}.

Global Hint Resolve eqb_reflexivity:eqb.
Global Hint Resolve eqb_symmetry:eqb. 
Global Hint Resolve eqb_transitivity:eqb.

Class EqbEq (T : Type) `{Eqb T} := {
  eqb_eq : forall x y : T, eqb x y = true <-> x = y
}.

Global Hint Resolve eqb_eq:eqb.
