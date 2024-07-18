Require Import Classes.Eqb.

Section Eqb.

Definition eqb_tuple {A B : Type} `{Eqb A} `{Eqb B} (t1 t2 : A * B) : bool :=
  match t1, t2 with
  | (x1, y1), (x2, y2) => eqb x1 x2 && eqb y1 y2
  end.

Lemma eqb_tuple_reflexivity {A B : Type} `{EqbLaws A} `{EqbLaws B} : forall (t : A * B), eqb_tuple t t = true.
Proof.
  intros t.
  destruct t as [x y]; simpl.
  rewrite eqb_reflexivity, eqb_reflexivity. reflexivity.
Qed.

Lemma eqb_tuple_symmetry {A B : Type} `{EqbLaws A} `{EqbLaws B} : forall (t1 t2 : A * B), eqb_tuple t1 t2 = eqb_tuple t2 t1.
Proof.
  intros t1 t2.
  destruct t1 as [x1 y1], t2 as [x2 y2]; simpl.
  rewrite eqb_symmetry, (eqb_symmetry y1 y2).
  reflexivity.
Qed.

Lemma eqb_tuple_transitivity {A B : Type} `{EqbLaws A} `{EqbLaws B} : forall (t1 t2 t3 : A * B), eqb_tuple t1 t2 = true -> eqb_tuple t2 t3 = true -> eqb_tuple t1 t3 = true.
Proof.
  intros t1 t2 t3 H12 H23.
  destruct t1 as [x1 y1], t2 as [x2 y2], t3 as [x3 y3]; simpl in *.
  apply andb_prop in H12 as [H12_x H12_y]. apply andb_prop in H23 as [H23_x H23_y].
  rewrite (eqb_transitivity _ _ _ H12_x H23_x), (eqb_transitivity _ _ _ H12_y H23_y). reflexivity.
Qed.

Instance EqbTuple {A B : Type} `{Eqb A} `{Eqb B} : Eqb (A * B) :=
{
  eqb := eqb_tuple
}.
Global Existing Instance EqbTuple.

Instance EqbLawsTuple {A B : Type} {eqb_a: Eqb A} {eqb_b: Eqb B} `{@EqbLaws A eqb_a} `{@EqbLaws B eqb_b} : EqbLaws (A * B) :=
{
  eqb_reflexivity := eqb_tuple_reflexivity;
  eqb_symmetry := eqb_tuple_symmetry;
  eqb_transitivity := eqb_tuple_transitivity
}.
Global Existing Instance EqbLawsTuple.

Lemma eqb_tuple_eq {A B:Type} `{eqb_a:Eqb A, eqb_b:Eqb B, eqb_a_laws: @EqbLaws A eqb_a, eqb_b_laws: @EqbLaws B eqb_b, eqb_a_eq : @EqbEq A eqb_a, eqb_b_eq : @EqbEq B eqb_b}  (x y : A * B) : eqb x y = true <-> x = y.
Proof.
  split.
  - intros H.
    destruct x, y; simpl in H. 
    apply andb_prop in H. destruct H as [H1 H2].
    apply eqb_eq in H1. apply eqb_eq in H2.
    subst. reflexivity.
  - intros H. rewrite H. apply eqb_reflexivity.
Qed.

Instance EqbEqTuple {A B : Type} {eqb_a: Eqb A} {eqb_b: Eqb B} `{@EqbLaws A eqb_a} `{@EqbLaws B eqb_b} `{@EqbEq A eqb_a} `{@EqbEq B eqb_b} : EqbEq (A * B) :=
{
  eqb_eq := eqb_tuple_eq;
}.
Global Existing Instance EqbEqTuple.

End Eqb.
