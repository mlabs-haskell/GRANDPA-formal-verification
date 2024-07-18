Require Import Classes.Eqb.

Section Eqb.
Definition eqb_sum {A B : Type} `{Eqb A} `{Eqb B} (s1 s2 : A + B) : bool :=
  match s1, s2 with
  | inl x1, inl x2 => eqb x1 x2
  | inr y1, inr y2 => eqb y1 y2
  | _, _ => false
  end.

Lemma eqb_sum_reflexivity {A B : Type} `{EqbLaws A} `{EqbLaws B} : forall (s : A + B), eqb_sum s s = true.
Proof.
  intros s.
  destruct s; simpl; apply eqb_reflexivity.
Qed.

Lemma eqb_sum_symmetry {A B : Type} `{EqbLaws A} `{EqbLaws B} : forall (s1 s2 : A + B), eqb_sum s1 s2 = eqb_sum s2 s1.
Proof.
  intros s1 s2.
  destruct s1, s2; simpl; try reflexivity.
  - apply eqb_symmetry.
  - apply eqb_symmetry.
Qed.

Lemma eqb_sum_transitivity {A B : Type} `{EqbLaws A} `{EqbLaws B} : forall (s1 s2 s3 : A + B), eqb_sum s1 s2 = true -> eqb_sum s2 s3 = true -> eqb_sum s1 s3 = true.
Proof.
  intros s1 s2 s3 H12 H23.
  destruct s1, s2, s3; simpl in *; try discriminate.
  - apply (eqb_transitivity _ _ _ H12 H23).
  - apply (eqb_transitivity _ _ _ H12 H23).
Qed.

Instance EqbSum {A B : Type} `{Eqb A} `{Eqb B} : Eqb (A + B) :=
{
  eqb := eqb_sum
}.
Global Existing Instance EqbSum.

Instance EqbLawsSum {A B : Type} {eqb_a: Eqb A} {eqb_b: Eqb B} `{@EqbLaws A eqb_a} `{@EqbLaws B eqb_b} : EqbLaws (A + B) :=
{
  eqb_reflexivity := eqb_sum_reflexivity;
  eqb_symmetry := eqb_sum_symmetry;
  eqb_transitivity := eqb_sum_transitivity
}.
Global Existing Instance EqbLawsSum.

Lemma eqb_sum_eq {A B:Type} `{eqb_a:Eqb A, eqb_b:Eqb B, eqb_a_laws: @EqbLaws A eqb_a, eqb_b_laws: @EqbLaws B eqb_b, eqb_a_eq : @EqbEq A eqb_a, eqb_b_eq : @EqbEq B eqb_b}  (x y : A + B) : eqb x y = true <-> x = y.
Proof.
  split.
  - intros H.
    destruct x, y; simpl in H; try congruence.
    + apply eqb_eq in H. rewrite H. reflexivity.
    + apply eqb_eq in H. rewrite H. reflexivity.
  - intros H. rewrite H. apply eqb_reflexivity.
Qed.

Instance EqbEqSum {A B : Type} {eqb_a: Eqb A} {eqb_b: Eqb B} `{@EqbLaws A eqb_a} `{@EqbLaws B eqb_b} `{@EqbEq A eqb_a} `{@EqbEq B eqb_b} : EqbEq (A + B) :=
{
  eqb_eq := eqb_sum_eq;
}.

Global Existing Instance EqbEqSum.

End Eqb.

