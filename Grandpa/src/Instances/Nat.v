Require Import Classes.Eqb.
Require Import Classes.Math.All.

Require PeanoNat.

Instance EqbNat : Eqb nat :=
{
  eqb := PeanoNat.Nat.eqb
}.

#[global]
Existing Instance EqbNat.

#[refine]Instance EqbLawsNat : EqbLaws nat :=
{
  eqb_reflexivity := PeanoNat.Nat.eqb_refl;
  eqb_symmetry := PeanoNat.Nat.eqb_sym;
}.
Proof.
  intros x y.
  generalize x.
  induction y;destruct x0,z; intros H eq_h; auto. 
  -  inversion H.
  -  unfold eqb.
    simpl.
    auto.
Qed.

#[global]
Existing Instance EqbLawsNat.

Instance EqbEqNat : EqbEq nat :=
{
  eqb_eq := PeanoNat.Nat.eqb_eq;
}.

#[global]
Existing Instance EqbEqNat.

Section Math.

Instance SemigroupNat: Semigroup nat 
:={
  plus := PeanoNat.Nat.add
}.

#[global]
Existing Instance SemigroupNat.

#[refine]
Instance SemigroupLawsNat : SemigroupLaws nat := {
}.
Proof.
  apply PeanoNat.Nat.add_assoc.
Qed.

#[global]
Existing Instance SemigroupLawsNat.


Instance MonoidNat: Monoid nat 
:={
  neutro := 0;
}.

#[global]
Existing Instance MonoidNat.

#[refine]
Instance MonoidLawsNat: MonoidLaws nat 
:={
}.
Proof.
  - intro t.
    simpl.
    reflexivity.
  - intro t.
    apply PeanoNat.Nat.add_0_r.
Qed.

#[global]
Existing Instance MonoidLawsNat.

End Math.

