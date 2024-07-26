Require Import DataTypes.NatWrapper.

Export NatWrapper.

Variant RoundNumberPhantom :=  RoundNumberPhantomC.

Definition RoundNumber := NatWrapper RoundNumberPhantom.

Definition from_nat := @NatWrapper.from_nat RoundNumberPhantom.
Definition to_nat := @NatWrapper.to_nat RoundNumberPhantom.
