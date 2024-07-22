Require Import Classes.Math.Semigroup.

Export Semigroup.

Open Scope math_scope.

Class Monoid (T:Type) `{Semigroup T} := {
  neutro: T;
}.

Class MonoidLaws (T:Type) 
  `{
    sg:Semigroup T
    ,sgl:@SemigroupLaws T sg
    ,m:@Monoid T sg
  }
  :={
  left_neutro : forall t, neutro + t = t;
  right_neutro : forall t, t + neutro = t
  }.

Print MonoidLaws.


#[global]
Hint Unfold neutro: MathHints.

#[global]
Hint Resolve left_neutro right_neutro: MathHints.

Close Scope math_scope.
