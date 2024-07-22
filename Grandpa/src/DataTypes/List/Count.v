Require Import Classes.Eqb.

Require Import List.
Require Coq.Bool.Bool.

Import List.ListNotations.

Section List.

Open Scope list_scope.
Open Scope eqb_scope.

Context {A:Type}.
Context `{eqb_a: Eqb A}.

Definition count x (l: list A) : nat
  := length (List.filter (eqb x) l).

Lemma count_cons x y l:
  count x (y::l) = (if eqb x y then 1 else 0) + count x l.
Proof.
  unfold count.
  simpl.
  destruct (eqb x y) .
  - reflexivity.
  - reflexivity.
Qed.


Lemma count_concat x l1 l2:
  count x (l1 ++ l2) = count x l1 + count x l2.
Proof.
  induction l1.
  - reflexivity.
  - destruct (eqb x a) eqn:H;
    pose (count_cons x a l1) as H2;
    rewrite H2;
    rewrite <- PeanoNat.Nat.add_assoc;
    rewrite <-IHl1;
    unfold count;
    simpl;
    rewrite H;
    reflexivity.
Qed.

Lemma count_after_filter_is_zero x l 
  : count x (List.filter (fun y => negb (eqb x y) ) l ) = 0.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    destruct (eqb x a) eqn:x_eq_a;simpl.
    + assumption.
    + rewrite count_cons.
      rewrite x_eq_a.
      auto.
Qed.

Lemma count_permutation x y z l1 l2
  : count x (l1++y::z::l2)
    = count x (l1++z::y::l2).
Proof.
  induction l1.
  - simpl.
    unfold count.
    simpl.
    destruct (eqb x y);destruct (eqb x z);reflexivity.
  - simpl.
    rewrite count_cons.
    rewrite count_cons.
    auto.
Qed.


End List.
