Require Import Classes.Eqb.

Require Import List.
Require Coq.Bool.Bool.

Import List.ListNotations.


Section Inb.
Open Scope list_scope.
Open Scope eqb_scope.

Context {A:Type}.
Context `{eqb_a: Eqb A}.
Context `{eqb_a_laws: @EqbLaws A eqb_a}.
Context `{eqb_eq : @EqbEq A eqb_a }.

(*TODO: Maybe use this definition? 
Definition in_list `{A:Type,Eqb A} (n:A) (l:list A) :bool := 
  match List.find (fun m => n =? m) l with
  | None => false
  | _ => true
  end.
*)

Fixpoint Inb  (x : A) (l : list A) : bool 
  :=
    match l with
    | [ ] => false
    | y :: ys => if eqb x y then true else Inb x ys
    end.

Lemma Inb_iff_In : forall x l,
    Inb x l = true <-> List.In x l.
  Proof.
    intros x l.
    induction l as [| y ys IH].
    - simpl. split.
      + intros H. discriminate H.
      + intros H. contradiction H.
    - simpl. split.
      + destruct (eqb x y) eqn:Heqb.
        * intros _. left. (* Prove that x = y *)
          apply eqb_eq. 
          rewrite eqb_symmetry.
          assumption.
        * intros H. right. apply IH. assumption.
      + intros [H | H].
        * subst. rewrite eqb_reflexivity. reflexivity.
        * apply IH in H. rewrite H. destruct (eqb x y);auto.
  Qed.

End Inb.

Require Import Program.Equality.

Lemma in_map {A B} (f : A -> B) (l : list A) (y : B)
  : List.In y (List.map f l) -> {x : A & f x = y /\ List.In x l}.
Proof.
Admitted.

Lemma map_in {A B} (f : A -> B) (l : list A) (y : B) (x : A)
  : (f x = y /\ List.In x l) ->List.In y (List.map f l).
Admitted.
