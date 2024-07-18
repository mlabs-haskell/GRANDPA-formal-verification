Require Import Classes.Eqb.

Require PeanoNat.

Instance EqbNat : Eqb nat :=
{
  eqb := PeanoNat.Nat.eqb
}.

Global Existing Instance EqbNat.

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

Global Existing Instance EqbLawsNat.

Instance EqbEqNat : EqbEq nat :=
{
  eqb_eq := PeanoNat.Nat.eqb_eq;
}.

Global Existing Instance EqbEqNat.
