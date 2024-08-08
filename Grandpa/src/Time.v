Require Import DataTypes.NatWrapper.

Export NatWrapper.

(** 
  See [NatWrapper].
*)

Variant TimePhantom :=  TimePhantomC.

Definition Time := NatWrapper TimePhantom.

Definition from_nat := @NatWrapper.from_nat TimePhantom.
Definition to_nat := @NatWrapper.to_nat TimePhantom.
