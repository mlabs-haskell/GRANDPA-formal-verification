Require Import PeanoNat.
Require Import Instances.Nat.
Require Import Classes.Eqb.
Require Import Classes.Math.All.

#[global]
Declare Scope natWrapper_scope.
Delimit Scope natWrapper_scope with natWrapper.

(** *NatWrapper
Coq doesn't have support for [newtypes], instead we
must create a regular type every time we want to
wrap some type around.

The case of wrapping a natural is a recurrent pattern.

Two important types that use this wrapper are:
  - Time
  - Round
*)


(**
  The type [T] is a phantom type, it's only use is to distinguish two
   different natural wrappers, otherwise we would defeat the entire
   purpose of using a wrapper.

  This means that every time you want to create a natural wrapper you
   need to create a phantom type representing it first.

  A minimal definition of a wrapper in a new module looks like this:

   [
    Require Import NatWrapper.

    Variant CustomCounterPhantom := CustomCounterPhantomC.
    Definition CustomCounter := NatWrapper CustomCounterPhantom
    Definition from_nat n : CustomCounter := NatWrapper.from_nat n
   ]
*)
Record NatWrapper (T:Type) :Type
    := NatWrapperC { to_nat:nat }.

Arguments NatWrapperC {T}.
Arguments to_nat {T}.

Definition from_nat {T:Type} (n:nat) : NatWrapper T
  := NatWrapperC n.


Section Eqb.

Open Scope eqb.

Definition natwrapper_eqb {T} (x y: NatWrapper T):= to_nat x =? to_nat y.

Instance EqbNatWrapper (T:Type) : Eqb (NatWrapper T)  :=
{
  eqb:= natwrapper_eqb
}.

#[global]
Existing Instance EqbNatWrapper.

#[refine]
Instance EqbLawsNatWrapper (T:Type) : EqbLaws (NatWrapper T) :=
{
}.
Proof.
  - intros *.
    simpl.
    apply eqb_reflexivity.
  - intros *.
    simpl.
    apply eqb_symmetry.
  - intros *.
    simpl.
    apply eqb_transitivity.
Qed.

#[global]
Existing Instance EqbLawsNatWrapper.

#[refine]
Instance EqbEqNatWrapper (T:Type) : EqbEq (NatWrapper T):=
{
}.
Proof.
  intros x y.
  destruct x,y.
  simpl.
  unfold natwrapper_eqb.
  Opaque eqb.
  simpl.
  Transparent eqb.
  rewrite eqb_eq.
  split.
  - intro H.
    rewrite H.
    reflexivity.
  - intro H.
    inversion H.
    reflexivity.
Qed.

#[global]
Existing Instance EqbEqNatWrapper.

End Eqb.

Section Math.

Open Scope math_scope.

Instance SemigroupNatWrapper (T:Type) : Semigroup (NatWrapper T) :={
  plus x y := from_nat (to_nat x + to_nat y)
}.

#[global]
Existing Instance SemigroupNatWrapper.

#[refine]
Instance SemigroupLawsNatWrapper (T:Type) : SemigroupLaws (NatWrapper T) :={
}.
Proof.
  intros x y z.
  destruct x,y,z.
  simpl.
  apply f_equal.
  apply PeanoNat.Nat.add_assoc.
Qed.

#[global]
Existing Instance SemigroupLawsNatWrapper.


Instance MonoidNatWrapper (T:Type) : Monoid (NatWrapper T) :={
  neutro:= from_nat 0
}.

#[global]
Existing Instance MonoidNatWrapper.

#[refine]
Instance MonoidLawsNatWrapper (T:Type) : MonoidLaws (NatWrapper T) :={
}.
Proof.
  - intro t.
    destruct t.
    auto.
  - intro t.
    destruct t.
    simpl.
    rewrite PeanoNat.Nat.add_0_r.
    auto.
Qed.

#[global]
Existing Instance MonoidLawsNatWrapper.

End Math.

#[global]
Infix "-" := (fun x y => from_nat ((to_nat x) - (to_nat y))) : natWrapper_scope.

#[global]
Infix "*" := (fun x y => from_nat ((to_nat x) * (to_nat y))) : natWrapper_scope.

(*
TODO: The proper way to adquire this notation must be by defining boolean
ordering classes as we did with Eqb.
*)
#[global]
Infix "<" := (fun x y => ((to_nat x) < (to_nat y)))%nat : natWrapper_scope.

#[global]
Infix "<?" := (fun x y => ((to_nat x) <? (to_nat y)))%nat : natWrapper_scope.

#[global]
Infix "<=" := (fun x y => ((to_nat x) <= (to_nat y)))%nat : natWrapper_scope.

#[global]
Infix "<=?" := (fun x y => ((to_nat x) <=? (to_nat y)))%nat : natWrapper_scope.

#[global]
Infix ">" := (fun x y =>  ((to_nat x) > (to_nat y)))%nat : natWrapper_scope.

#[global]
Infix ">=" := (fun x y => ((to_nat x) >= (to_nat y)))%nat : natWrapper_scope.


Lemma natWrapper_recursion {Phantom}
  (P: NatWrapper Phantom -> Prop)
  (at_0:P (NatWrapperC 0))
  (step:(forall n, P (NatWrapperC n) -> P (NatWrapperC (S n))))
  : forall w, P w :Prop.
Proof.
  intro w.
  destruct w as [n].
  induction n.
  - auto.
  - auto.
Qed.
