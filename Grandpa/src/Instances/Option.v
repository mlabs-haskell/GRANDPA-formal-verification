Require Import Classes.Eqb.
Require Import Classes.Functor.
Require Import Classes.Math.All.

Section Eqb.
Open Scope eqb_scope.

Definition eqb_option {A : Type} `{Eqb A} (o1 o2 : option A) : bool :=
  match o1, o2 with
  | Some x1, Some x2 => eqb x1 x2
  | None, None => true
  | _, _ => false
  end.

Lemma eqb_option_reflexivity {A : Type} `{EqbLaws A} : forall (o : option A), eqb_option o o = true.
Proof.
  intros o.
  destruct o; simpl.
  - apply eqb_reflexivity.
  - reflexivity.
Qed.

Lemma eqb_option_symmetry {A : Type} `{EqbLaws A} : forall (o1 o2 : option A), eqb_option o1 o2 = eqb_option o2 o1.
Proof.
  intros o1 o2.
  destruct o1, o2; simpl; try reflexivity.
  - apply eqb_symmetry.
Qed.

Lemma eqb_option_transitivity {A : Type} `{EqbLaws A} : forall (o1 o2 o3 : option A), eqb_option o1 o2 = true -> eqb_option o2 o3 = true -> eqb_option o1 o3 = true.
Proof.
  intros o1 o2 o3 H12 H23.
  destruct o1, o2, o3; simpl in *; try discriminate.
  - apply (eqb_transitivity _ _ _ H12 H23).
  - reflexivity.
Qed.

Instance EqbOption {A : Type} `{Eqb A} : Eqb (option A) :=
{
  eqb := eqb_option
}.

#[global]
Existing Instance EqbOption.

Instance EqbLawsOption {A : Type} {eqb_a: Eqb A} `{@EqbLaws A eqb_a} : EqbLaws (option A) :=
{
  eqb_reflexivity := eqb_option_reflexivity;
  eqb_symmetry := eqb_option_symmetry;
  eqb_transitivity := eqb_option_transitivity
}.
#[global]
Existing Instance EqbLawsOption.

Lemma eqb_option_eq {A:Type} `{eqb_a:Eqb A, eqb_a_laws: @EqbLaws A eqb_a, eqb_a_eq : @EqbEq A eqb_a}  (x y : option A) : eqb x y = true <-> x = y.
Proof.
  split.
  - destruct x, y; simpl; try congruence.
    + intro H. apply eqb_eq in H. rewrite H. reflexivity.
  - intro H. rewrite H. apply eqb_reflexivity.
Qed.

Instance EqbEqOption {A : Type} {eqb_a: Eqb A} `{@EqbLaws A eqb_a} `{@EqbEq A eqb_a} : EqbEq (option A) :=
{
  eqb_eq := eqb_option_eq;
}.

#[global]
Existing Instance EqbEqOption.
End Eqb.

Section Functor.

Instance Functor_option : Functor option := {
  map := fun {A B : Type} (g : A -> B) (o : option A) =>
    match o with
    | Some x => Some (g x)
    | None => None
    end
}.
#[global]
Existing Instance Functor_option.

Instance FunctorLaws_option : FunctorLaws option.
Proof.
  split.
  - intros A [x |]; simpl.
    + reflexivity.
    + reflexivity.
  - intros A B C g h [x |]; simpl.
    + reflexivity.
    + reflexivity.
Qed.

#[global]
Existing Instance FunctorLaws_option.

End Functor.

Section Math.

Instance SemigroupOption `{A:Type , Semigroup A}: Semigroup (option A) 
:={
  plus x y :=
    match x,y with
    | Some x', Some y' => Some (plus x' y')%math
    | Some x', None => x
    | None, Some y' => y
    | _,_ => None
    end
}.
#[global]
Existing Instance SemigroupOption.

#[refine]
Instance SemigroupLawsOption `{A:Type , sg:Semigroup A, sgl:SemigroupLaws A}: SemigroupLaws (option A) 
:={
}.
Proof.
  intros x y z.
  destruct x, y , z;try reflexivity.
  simpl.
  rewrite plus_associative.
  reflexivity.
Qed.

#[global]
Existing Instance SemigroupLawsOption.

Instance MonoidOption `{A:Type , Semigroup A}: Monoid (option A) 
:={
  neutro:= None
}.
#[global]
Existing Instance MonoidOption.

#[refine]
Instance MonoidLawsOption `{A:Type , sg:Semigroup A, sgl:SemigroupLaws A}:MonoidLaws (option A) 
:={
}.
Proof.
  - intro t.
    destruct t;auto.
  - intro t.
    destruct t;auto.
Qed.

#[global]
Existing Instance MonoidLawsOption.

(*TODO: add group instance*)

End Math.
