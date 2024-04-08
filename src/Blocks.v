Require Bool.
Require Import Lia.
Require Import Coq.Program.Equality.
Require Import Setoid.

(** 

  In the real implementation is unpractical to have the full
  history of the blockchain and instead a new block stores
  the hash of the last block. In our case storing the hash
  only would lead to complications, as so, we choose to 
  store the full chain of blocks.

  Blocks are indexed by it's index in the chain.

  Originally we used the Vector type in the Coq prelude, 
  but it complicates the requirement of the `Original` block.
*)

Inductive Block : nat -> Type:= 
  | OriginBlock : Block 0
  (** 
     The id only purpose is to bring us the ability to talk about 
   different blocks.
   *)
  | NewBlock {n} (oldBlock : Block n) (id:nat) : Block (S n).

Definition AnyBlock := {n & Block n}.
(** 
Example:
  Definition newBlock_1 : AnyBlock := existT (fun n => Block n) 1 (NewBlock OriginBlock 1).
  Check newBlock_1 : AnyBlock .
*)

Fixpoint eqb {n m} (block1:Block n) (block2:Block m) := 
  match block1, block2 with
  | OriginBlock, OriginBlock => true
  | NewBlock old1 id1, NewBlock old2 id2 => andb (Nat.eqb id1 id2) (eqb old1 old2)
  | _, _ => false
  end.

Definition any_block_eqb (b1 b2: AnyBlock) : bool
  := 
    match b1 , b2 with 
    | (existT _ n1 b1'), (existT _ n2 b2') => eqb b1' b2'
    end.


Lemma eqb_implies_same_nat {n} (block1: Block n): forall {m} (block2: Block m), eqb block1 block2 = true -> n = m .
Proof.
  induction block1 as [|n block1 HInductive id1].
  - intros m block2 Hblock2.
    destruct block2.
    + reflexivity.
    + simpl in Hblock2. 
      discriminate.
  - intros m block2 Hblock2.
    destruct block2 as [| pre_m pre_block2 pre_id] eqn:eq_block2 .
    + simpl in Hblock2. 
      discriminate.
    + simpl in Hblock2.
      apply Bool.andb_true_iff in Hblock2.
      destruct Hblock2 as [_ same_children].
      pose (HInductive pre_m pre_block2 same_children) as same_number .
      rewrite same_number.
      trivial.
Qed.



Lemma eqb_reflexive {n} (block1: Block n)  :  eqb block1 block1 = true.
Proof.
  induction block1.
  - auto. 
  - simpl. 
    apply Bool.andb_true_iff.
    split.
    + apply PeanoNat.Nat.eqb_eq.
      reflexivity.
    + auto.
Qed.

Lemma eqb_symmetric {n} (block1:Block n): forall {m} (block2:Block m) , eqb block1 block2 = true -> eqb block2 block1 = true.
Proof.
  induction block1.
  - intros m block2.
    destruct block2;auto.
  - intros m block2. 
    destruct block2.
    + auto.
    + simpl. 
      intro H.
      simpl in H.
      apply Bool.andb_true_iff in H.
      destruct H as [eqb_id eqb_blocks].
      apply Bool.andb_true_iff.
      split.
      ++ apply PeanoNat.Nat.eqb_eq.
         apply PeanoNat.Nat.eqb_eq in eqb_id.
         auto.
      ++ auto. 
Qed.


Lemma eqb_eq {n} (block1: Block n)  : forall (block2:Block n), eqb block1 block2 = true <-> block1 = block2.
Proof.
  induction block1 as [|n block1 HInductive id].
  - intro block2.
    split.
    + intro Hblock2.
      dependent destruction block2.
      reflexivity.
    + intro Hblock2.
      rewrite Hblock2.
      apply eqb_reflexive.
  - intro block2.  
    split.
    + intro Hblock2. 
      dependent destruction block2.
      simpl in Hblock2.
      apply Bool.andb_true_iff in Hblock2.
      destruct Hblock2 as [same_id same_children].
      rewrite (HInductive _) in same_children.
      rewrite PeanoNat.Nat.eqb_eq in same_id.
      rewrite same_id.
      rewrite same_children.
      trivial.
    + intro H.
      rewrite H.
      apply eqb_reflexive.
Qed.

Definition get_block_number {n : nat} (block : Block n) : nat :=
  match block with
  | OriginBlock => 0
  | NewBlock _ _ => S n
  end.

Print False_rec.
Search (S ?n = 0).
Search (?x = ?y <-> ?y = ?x).

Lemma symmetric_aux {n m:nat} : n=m -> m=n.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Fixpoint cast {n} (block:Block n) {struct block}: forall {m}, m = n -> Block m
  :=
  match block in Block n' return forall m, m = n' -> Block m with 
  | OriginBlock 
      => fun m 
        => match m with 
           | 0 =>fun H => OriginBlock
           | S m' =>fun H 
               => False_rec (Block (S m')) (PeanoNat.Nat.neq_succ_0 _ H)
          end 
  | NewBlock oldBlock id
      => fun m 
        => match m with 
           | 0 =>fun H 
               => False_rec 
                (Block 0) 
                (PeanoNat.Nat.neq_succ_0 _ (symmetric_aux H))
           | S m' => fun H 
               => NewBlock (cast oldBlock (m:=m') (f_equal pred H)) id
          end 
  end.

(* 
   You can define cast with this, but it would mean an opaque function.
Proof.
  intro block.
  induction n.
  - intros m H.
    rewrite H.
    refine OriginBlock.
  - intros m H.
    dependent destruction block.
    rewrite H.
    refine (NewBlock (IHn block n _ ) id).
    reflexivity.
Qed.
*)

Lemma cast_origin_is_origin {m} (eq_n_m:m=0)
  : eqb OriginBlock (cast OriginBlock (m:=m) eq_n_m) = true.
Proof.
  simpl.
  rewrite eq_n_m.
  reflexivity.
Qed.

Lemma cast_are_same {n} (block:Block n) {m} (eq_n_m:m=n) 
  : eqb block (cast block (m:=m) eq_n_m)=true.
Proof.
  dependent induction block.
  - apply cast_origin_is_origin.
  - simpl.
    rewrite eq_n_m.
    simpl.
    apply Bool.andb_true_iff.
    split.
    + apply PeanoNat.Nat.eqb_refl.
    + apply IHblock.
Qed.

Lemma cast_eqb_are_equal {n m} (block1: Block n) (block2:Block m)
  (are_equal:eqb block1 block2 = true) 
  (same_nats: n = m)
  : block1 = cast block2 same_nats.
Proof.
  dependent induction block1 generalizing m.
  - dependent destruction block2. 
    + auto. 
    + discriminate.
  - destruct block2. 
    + discriminate.
    +
    simpl in are_equal.
    apply Bool.andb_true_iff in are_equal.
    destruct are_equal as [eq_id eqb_blocks].
    apply (PeanoNat.Nat.eqb_eq id) in eq_id.
    rewrite <- eq_id.
    pose (IHblock1 n0 block2 eqb_blocks (f_equal Nat.pred same_nats)) as eq_blocks.
    simpl.
    rewrite <- eq_blocks.
    reflexivity.
Qed.

(**  
   [Prefix B B'] in the paper is presented as [B <= B'].
*)
Inductive Prefix : forall {n}, Block n -> forall {m}, Block m -> Type :=
  (** [B <= B']*)
  | Same : forall n (block : Block n), Prefix block block
  (** [B <= B'  ->  B <= (b :: B')] *)
  | IsPrefix {n m} (block1: Block n) (block2: Block m) (block_id : nat) :
      Prefix block1 block2 -> Prefix block1 (NewBlock block2 block_id).

Lemma originBlock_is_always_prefix  {n} (block:Block n):  Prefix OriginBlock block.
Proof.
  induction block.
  - (* Case: block = OriginBlock *)
    apply Same.
  - (* Case: block = NewBlock oldBlock id *)
    apply IsPrefix.
    apply IHblock.
Qed.

Lemma prefix_of_newblock {n m} (block1: Block n) (block2:Block m) {id} 
  : Prefix block1 block2 -> Prefix block1 (NewBlock block2 id).
Proof.
  auto using IsPrefix.
Qed.

Lemma newblock_prefix {n m} (block1: Block n) (block2:Block m) {id} 
  : Prefix (NewBlock block1 id) block2 -> Prefix block1 block2.
Proof.
  Admitted.
  (*  intro H.
  dependent induction H .
  - apply IsPrefix.
    apply Same.
  - dependent destruction block2.
    + inversion H.
    + apply prefix_of_newblock.
      apply IHPrefix.
      apply prefix_of_newblock.
  auto using IsPrefix.
Qed.
  *)

Lemma prefix_height_is_below {n m} (block1: Block n) (block2:Block m)
  : Prefix block1 block2 -> n <= m.
Proof.
  intro H.
  dependent induction block2.
  - destruct block1.
    + auto.
    + inversion H.
  - dependent destruction block1.
    + apply PeanoNat.Nat.le_0_l.
    + dependent destruction H.
      ++ auto.
      ++ apply IHblock2 in H.
         auto using le_S.
Qed.


Lemma eqb_blocks_are_prefix {n} (block1 block2: Block n): eqb block1 block2 = true -> Prefix block1 block2.
Proof.
  intro H.
  rewrite (eqb_eq block1 block2) in H.
  rewrite H.
  refine (Same n block2).
Qed.


Lemma eqb_blocks_are_prefix2 {n m} (block1: Block n) (block2:Block m)
  (are_equal:eqb block1 block2 = true) 
  (same_nats: n = m)
(*: block1 = cast block2 (eqb_implies_same_nat _ _ are_equal).
Proof.
  remember (cast block2 (eqb_implies_same_nat _ _ are_equal)) as block3.
*)

  :  Prefix block1 (cast block2 same_nats ).
Proof.
  assert (block1 = cast block2 same_nats).
    {
    apply cast_eqb_are_equal.
    assumption.
    }
    rewrite <- H.
    refine (Same n block1).
Qed.

Open Scope nat_scope.

Fixpoint is_prefix {n m} (block1 : Block n) (block2: Block m) : option (Prefix block1 block2) 
 :=
  if Nat.leb n  m then
    match block2 with
    | OriginBlock => 
        match block1 with 
        | OriginBlock => Some (Same 0 OriginBlock)
        | _ => None
        end
    | NewBlock old_block id =>
        match is_prefix block1 old_block with
        | Some p => Some (IsPrefix block1 old_block id p)
        | None => None
        end
    end
  else
  None.

Lemma prefix_implies_is_prefix {n m} (block1 : Block n) (block2: Block m) 
  : Prefix block1 block2 -> exists p,   is_prefix block1 block2 = Some p.
Proof.
  intro H.
  dependent induction block2.
  - dependent destruction block1.
    + simpl. eauto.
    + inversion H.
  - destruct (is_prefix block1 block2) eqn:Hr.
  (* 2:{ 
      simpl.
  - destruct (is_prefix block1 (NewBlock block2 id)) eqn:Hr.
    + eauto.
    + simpl in Hr.
  - apply newblock_prefix in H.
    simpl.


  intro H.
  dependent induction block1.
  - dependent induction block2. 
    + simpl.
      exists H.
      dependent destruction H. auto.
    + pose (originBlock_is_always_prefix block2) as origin_prefix_block2.
      apply IHblock2 in origin_prefix_block2.
      destruct origin_prefix_block2 as [prefix_block2 inductive].
      simpl. 
      rewrite inductive.
      exists (IsPrefix OriginBlock block2 id prefix_block2).
      auto.
  - dependent destruction block2.
    + inversion H.
    + simpl.
      pose (prefix_height_is_below _ _ H) as Sn_leq_Sn0.
      pose (PeanoNat.Nat.leb_le (n) (n0)) as leb_iff_le.
      apply le_S_n in Sn_leq_Sn0.
      rewrite <- leb_iff_le in Sn_leq_Sn0.
      rewrite Sn_leq_Sn0.
    *)
    Admitted.

Lemma prefix_of_cast_right {n m} (block1 : Block n) (block2: Block m) {w}
  (eq_w_m: w = m)
  : Prefix block1 (cast block2 eq_w_m)-> Prefix block1 block2.
Proof.
  intros H.
  dependent induction block1.
  - apply originBlock_is_always_prefix.
  - destruct block2.
    Admitted.



 

(**
  [IsChildren B B' = B' < B]
 *)

Variant IsChildren {n m} (block1 :Block n) (block2: Block m) : Type :=
  | IsChildrenC (is_prefix: Prefix block1 block2) (block_number_is_above: n<m) :
      IsChildren block1 block2.


(* 
   Is equivalent to the relation B ~ B' in the paper
   We express it like `(B <= B' ) \/ (B' <= B)` instead 
   of the one in the paper `B<B' /\ B=B! /\ B>B'` .

 *)
Variant Related {n m} (block1:Block n) (block2 :Block m) : Prop :=
  | RelatedAsChildren
    : IsChildren block1 block2 -> Related block1 block2
  | RelatedAsParent
    : IsChildren block2 block1 -> Related block1 block2
  | RelatedAsEquals: eqb block1 block2 = true -> Related block1 block2.

Definition Unrelated {n m} (block1 : Block n) (block2 :Block m) : Prop := not (Related block1 block2).

Lemma related_symmetric : forall n (block1:Block n) m (block2 :Block m)
  , Related block1 block2 -> Related block2 block1.
Proof.
  intros n b1 m b2 H.
  destruct H. 
  - refine (RelatedAsParent _ _ H).
  - refine (RelatedAsChildren _ _ H).
  - apply RelatedAsEquals.
    auto using eqb_symmetric.
Qed.

Lemma prefix_implies_related  {n m} (block1:Block n) (block2:Block m) 
  : Prefix block1 block2 -> Related block1 block2.
Proof.
  intros H.
  dependent destruction H.
  - apply RelatedAsEquals.
    apply eqb_reflexive.
  - apply RelatedAsChildren.
    apply IsChildrenC.
    + auto using prefix_of_newblock.
    + apply prefix_height_is_below in H.
      auto using le_n_S.
Qed.

Lemma decidable_related : forall n (block1:Block n) m (block2 :Block m)
  , {Related block1 block2} + {Unrelated block1 block2}.
Proof.
  intros n b1 m b2.
  remember (is_prefix b1 b2) as maybe_prefix1_2.
  destruct maybe_prefix1_2.
  - left.  apply prefix_implies_related. refine p.
  - remember (is_prefix b2 b1) as maybe_prefix2_1.
    destruct maybe_prefix2_1.
    + left. apply related_symmetric. apply prefix_implies_related. refine p.
    + right.
      unfold Unrelated.
      unfold not.
      intro H.
      destruct H. 
      ++ destruct H.
         apply prefix_implies_is_prefix in is_prefix0. 
         destruct is_prefix0.
         rewrite H in Heqmaybe_prefix1_2.
         inversion Heqmaybe_prefix1_2.
      ++ destruct H.
         apply prefix_implies_is_prefix in is_prefix0. 
         destruct is_prefix0.
         rewrite H in Heqmaybe_prefix2_1.
         inversion Heqmaybe_prefix2_1.
      Print False_rec.
      ++ pose (eqb_implies_same_nat _ _ H) as same_nat.
         pose (eqb_blocks_are_prefix2 _ _ H same_nat) as H2.
         pose (prefix_of_cast_right b1 b2 same_nat H2) as H3.
         pose (prefix_implies_is_prefix _ _ H3) as H4.
         destruct H4 as [p proof_prefix].
         rewrite proof_prefix in Heqmaybe_prefix1_2.
         discriminate Heqmaybe_prefix1_2.
Qed.

Lemma different_blocks_of_same_height_are_unrelated : 
  forall n (block1 block2 :Block n) 
  , block1 <> block2 -> Unrelated block1 block2.
Proof.
  intros n b1 b2 no_eq Hrelated.
  destruct Hrelated as [Hrelated|Hrelated|Hrelated].
  - destruct Hrelated.
    apply (PeanoNat.Nat.lt_irrefl n).
    auto.
  - destruct Hrelated.
    apply (PeanoNat.Nat.lt_irrefl n).
    auto.
  - rewrite eqb_eq in Hrelated.
    contradiction.
Qed.
