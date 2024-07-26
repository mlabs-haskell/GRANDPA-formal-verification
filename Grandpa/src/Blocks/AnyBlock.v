Require Bool.
Require Import Blocks.Block.

Export Block.

Require Import Classes.Eqb.
Require Import Instances.Nat.
Require Import Instances.Tuple.


(* TODO: Is this useful?
Record Opaque {T:Type} (dependent: T -> Type) 
  := 
  {
  element:T 
  ;value: dependent element
  }.

Arguments element {T} {dependent}.
Arguments value {T} {dependent}.

Definition to_tuple {T:Type} {dependent: T -> Type} (opaque:Opaque dependent)
  := 
  (element opaque, value opaque).


Open Scope bool_scope.
Open Scope eqb_scope.


Instance EqbOpaque `{T:Type, Eqb T,  dependent:T->Type} 
  (eqb_at_all: forall (t:T), Eqb (dependent t) )  
  : Eqb (Opaque dependent)
  :={
    eqb o1 o2 := 
      ((element o1 ) =? (element o2) )
      &&       
      ((value o1) =? (value o2))
    }.

Close Scope bool_scope.
Close Scope eqb_scope.

*)


(** From time to time we need to form a type that can contain 
  blocks of any lenght. In such cases we will use AnyBlock 
   as the type.
*)
Record AnyBlock 
  := 
  AnyBlockC {
  block_number: nat
  ; block : Block block_number
  }.

Definition to_any {n:nat} (b: Block n) : AnyBlock
  := AnyBlockC n b.

Section Instances.

Open Scope eqb_scope.

Definition eqb (b1 b2: AnyBlock) : bool
  :=  Block.eqb b1.(block) b2.(block).

Instance EqbAnyBlock : Eqb AnyBlock :={
  eqb:= eqb
  }.

Global Existing Instance EqbAnyBlock.

Lemma eqb_reflexivity (b1:AnyBlock)
  : (b1 =? b1) =true.
Proof.
  destruct b1 as [n b1'].
  simpl.
  apply eqb_reflexive.
Qed.

Lemma eqb_transitivity (b1 b2 b3:AnyBlock)
  : (b1 =? b2) =true 
    -> (b2 =? b3) =true 
    -> (b1 =? b3)=true.
Proof.
  destruct b1 as [n b1'].
  destruct b2 as [m b2'].
  destruct b3 as [r b3'].
  simpl.
  apply eqb_transitive.
Qed.

Lemma eqb_symmetry (b1 b2:AnyBlock)
  : (b1 =? b2) = (b2 =? b1).
Proof.
  - destruct b1 as [n b1'].
    destruct b2 as [m b2'].
    simpl.
    unfold eqb.
    simpl.
    rewrite eqb_symmetric. 
    reflexivity.
Qed.


Instance EqbLawsAnyBlock : EqbLaws AnyBlock :={
  eqb_reflexivity := eqb_reflexivity
  ;eqb_symmetry := eqb_symmetry
  ;eqb_transitivity := eqb_transitivity
  }.

Global Existing Instance EqbLawsAnyBlock.


End Instances.
