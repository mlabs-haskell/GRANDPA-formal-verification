Require Import Classes.Eqb.
Require Import Classes.Math.All.

Inductive Unit := UnitC.

Definition eqb_unit (_ _ : Unit) : bool := true.

Lemma eqb_unit_reflexivity : forall (u : Unit), eqb_unit u u = true.
Proof.
  intros u.
  destruct u; reflexivity.
Qed.

Lemma eqb_unit_symmetry : forall (u1 u2 : Unit), eqb_unit u1 u2 = eqb_unit u2 u1.
Proof.
  intros u1 u2.
  destruct u1, u2; reflexivity.
Qed.

Lemma eqb_unit_transitivity : forall (u1 u2 u3 : Unit), eqb_unit u1 u2 = true -> eqb_unit u2 u3 = true -> eqb_unit u1 u3 = true.
Proof.
  intros u1 u2 u3 H12 H23.
  destruct u1, u2, u3; reflexivity.
Qed.

Instance EqbUnit : Eqb Unit :=
{
  eqb := eqb_unit
}.

#[global]
Existing Instance EqbUnit.

Instance EqbLawsUnit : EqbLaws Unit :=
{
  eqb_reflexivity := eqb_unit_reflexivity;
  eqb_symmetry := eqb_unit_symmetry;
  eqb_transitivity := eqb_unit_transitivity
}.

#[global]
Existing Instance EqbLawsUnit.

Lemma eqb_unit_eq : forall (u1 u2 : Unit), eqb_unit u1 u2 = true <-> u1 = u2.
Proof.
  split; intros; destruct u1, u2; simpl in *; try congruence; reflexivity.
Qed.

Instance EqbEqUnit : EqbEq Unit :=
{
  eqb_eq := eqb_unit_eq;
}.

#[global]
Existing Instance EqbEqUnit.

Section Math.

Instance SemigroupUnit : Semigroup Unit 
:={
  plus x y := UnitC
}.

#[global]
Existing Instance SemigroupUnit.

#[refine]
Instance SemigroupLawsUnit : SemigroupLaws Unit 
:={
}.
Proof.
  auto.
Qed.

Instance MonoidUnit : Monoid Unit 
:={
  neutro := UnitC
}.

#[global]
Existing Instance MonoidUnit.

#[refine]
Instance MonoidLawsUnit : MonoidLaws Unit 
:={
}.
Proof.
  - intro t.
    destruct t.
    auto.
  - intro t.
    destruct t.
    auto.
Qed.

#[global]
Existing Instance MonoidLawsUnit.

Instance GroupUnit : Group Unit 
:={
  negate t := UnitC
}.

#[global]
Existing Instance GroupUnit.

#[refine]
Instance GroupLawsUnit : GroupLaws Unit 
:={
}.
Proof.
  - intro t.
    destruct t.
    auto.
  - intro t.
    destruct t.
    auto.
Qed.

#[global]
Existing Instance GroupLawsUnit.

End Math.
