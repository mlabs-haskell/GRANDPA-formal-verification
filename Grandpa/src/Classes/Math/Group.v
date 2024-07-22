Require Import Classes.Math.Monoid.

Export Monoid.

Open Scope math_scope.


Class Group (T:Type) `{Monoid T} := {
  negate: T -> T;
}.

Class GroupLaws (T:Type) 
  `{
    sg:Semigroup T
    ,sgl:@SemigroupLaws T sg
    ,m:@Monoid T sg
    ,ml:@MonoidLaws T sg sgl m
    ,g:@Group T sg m
  } 
  := 
  {
  left_negate: forall t, t + negate t = neutro;
  right_negate: forall t, negate t + t = neutro
  }.


Definition substraction {T:Type} `{gl:GroupLaws T} (t1 t2 : T)
  : T
  :=
  t1 + (negate t2).


Infix "-" := substraction : math_scope.

#[global]
Hint Unfold substraction: MathHints.

#[global]
Hint Resolve left_negate right_negate: MathHints.

Close Scope math_scope.
