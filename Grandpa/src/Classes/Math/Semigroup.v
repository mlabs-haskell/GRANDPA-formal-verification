Require Import Classes.Math.Common.

Class Semigroup (T:Type) :={
  plus: T -> T->T;
}.


Class SemigroupLaws (T:Type) `{Semigroup T} :={
  plus_associative: forall x y z, plus x (plus y z) = plus (plus x y) z 
}.

Definition plus_law_operator {T:Type} `{sg:Semigroup T, @SemigroupLaws T sg} := plus.

Infix "+" := plus_law_operator: math_scope .

#[global]
Hint Resolve plus_associative: MathHints.

#[global]
Hint Unfold plus_law_operator: MathHints.

#[global]
Hint Opaque plus: MathHints.
