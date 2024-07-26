Require Import DataTypes.Sets.
Require Import Instances.Nat.
Require Import Classes.Eqb.

(** * Voter
*)

(** 
Some requirements about a type that can represent voters:
   - It must have infinite inhabitants.
   - It must have decidable equality.
This means, we can have any number of voters and we can 
distinguish between them. 
For this reason we choose to use naturals.

Additionally we use the newtype pattern as we would work 
a lot with other types isomorphic to naturals.
*)
Record Voter : Type := VoterC { to_nat:nat }.

Definition from_nat (n:nat) : Voter 
  :=
  VoterC n.

Section VoterInstances.
Open Scope eqb_scope.

Instance EqbVoter : Eqb Voter :={
  eqb v1 v2 := (to_nat v1) =? (to_nat v2);
  }.

Global Existing Instance EqbVoter.

#[refine] 
Instance EqbLawsVoter :EqbLaws Voter :={
  
}.
Proof.
  - intro v.
    apply (eqb_reflexivity (to_nat v)).
  - intros v1 v2.
    apply (eqb_symmetry (to_nat v1)).
  - intros v1 v2 v3.
    apply (eqb_transitivity (to_nat v1) (to_nat v2) (to_nat v3)).
Qed.

Global Existing Instance EqbLawsVoter.

#[refine]
Instance EqbEqVoter: EqbEq Voter :={
  
}.
Proof.
  destruct x, y. unfold eqb. simpl.
  split; intro H.
  - apply PeanoNat.Nat.eqb_eq in H.
    rewrite H.
    reflexivity.
  - injection H.
    intro H2.
    rewrite H2.
    apply PeanoNat.Nat.eqb_refl.
Qed.

Global Existing Instance EqbEqVoter.
End VoterInstances.
