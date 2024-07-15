Require Bool.
Require Import Lia.
Require Import Coq.Program.Equality.
Require Import Setoid.

Require Import PeanoNat.

Declare Scope blocks_scope.
Delimit Scope blocks_scope with blocks.
Open Scope blocks_scope.

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


(** From time to time we need to form a type that can contain 
  blocks of any lenght. In such cases we will use AnyBlock 
   as the type.
*)
Definition AnyBlock := {n & Block n}.

Definition to_any {n:nat} (b: Block n) : AnyBlock
  := existT _ n b.

(** 
Example:
  
  [Definition newBlock_1 : AnyBlock := existT (fun n => Block n) 1 (NewBlock OriginBlock 1).]

  [Check newBlock_1 : AnyBlock .]
*)

(** * Block Equality
  In the term
   [block1 = block2]
   we need to already know (syntactically) that both blocks has the same lenght.
  otherwise coq would (rightfully) refuse to construct the term.
   
  This means that either we work with Heterogeneous equality or 
   cast around the types (also called transport).

  As I lack experience with Heterogeneous equality I choose to cast around types.
*)

Fixpoint eqb {n m} (block1:Block n) (block2:Block m) := 
  match block1, block2 with
  | OriginBlock, OriginBlock => true
  | NewBlock old1 id1, NewBlock old2 id2 => andb (id1 =? id2) (eqb old1 old2)
  | _, _ => false
  end.

Notation " b1 =? b2 " := (eqb b1 b2):blocks_scope.

Definition anyblock_eqb (b1 b2: AnyBlock) : bool
  := 
    match b1 , b2 with 
    | (existT _ n1 b1'), (existT _ n2 b2') => b1' =? b2'
    end.

Lemma eqb_implies_same_nat {n} (block1: Block n)
  : forall {m} (block2: Block m), block1 =? block2 = true -> n = m .
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

Lemma eqb_reflexive {n} (block1: Block n)  :  block1 =? block1 = true.
Proof.
  induction block1.
  - auto. 
  - simpl. 
    apply Bool.andb_true_iff.
    split.
    + apply Nat.eqb_eq.
      reflexivity.
    + auto.
Qed.

Lemma eqb_symmetric {n} (block1:Block n)
  : forall {m} (block2:Block m) 
  , block1 =? block2 = true -> block2 =? block1 = true.
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
      ++ apply Nat.eqb_eq.
         apply Nat.eqb_eq in eqb_id.
         auto.
      ++ auto. 
Qed.

Lemma eqb_transitive {n} (b1:Block n)
  :forall {m r}
  (b2:Block m)
  (b3:Block r),
  b1 =? b2 = true -> b2 =? b3 = true -> b1 =? b3 = true.
Proof.
  induction b1.
  - intros m r b2 b3 H1_2 H2_3.
    destruct b3.
    + reflexivity.
    + destruct b2.
      * inversion H2_3.
      * inversion H1_2.
  - intros m r b2 b3 H1_2 H2_3.
    destruct b2.
    + inversion H1_2.
    + simpl in H1_2.
      rewrite Bool.andb_true_iff in H1_2.
      destruct H1_2 as [id1_id0 b1_b2].
      destruct b3.
      * inversion H2_3.
      * simpl in H2_3.
        rewrite Bool.andb_true_iff in H2_3.
        destruct H2_3 as [id0_id1 b2_b3].
        simpl.
        apply Bool.andb_true_iff. 
        split.
        ++ rewrite Nat.eqb_eq in id1_id0.
           rewrite Nat.eqb_eq in id0_id1.
           rewrite Nat.eqb_eq.
           transitivity id0;auto.
        ++ apply (IHb1 _ _ b2 b3);auto.
Qed.


Lemma eqb_eq {n} (block1: Block n)  
  : forall (block2:Block n), block1 =? block2 = true <-> block1 = block2.
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
      rewrite Nat.eqb_eq in same_id.
      rewrite same_id.
      rewrite same_children.
      trivial.
    + intro H.
      rewrite H.
      apply eqb_reflexive.
Qed.

Lemma anyblock_eqb_reflexive (b1:AnyBlock)
  : anyblock_eqb b1 b1 =true.
Proof.
  destruct b1 as [n b1'].
  simpl.
  apply eqb_reflexive.
Qed.

Lemma anyblock_eqb_transitive (b1 b2 b3:AnyBlock)
  : anyblock_eqb b1 b2 =true 
    -> anyblock_eqb b2 b3=true 
    -> anyblock_eqb b1 b3=true.
Proof.
  destruct b1 as [n b1'].
  destruct b2 as [m b2'].
  destruct b3 as [r b3'].
  simpl.
  apply eqb_transitive.
Qed.

Lemma anyblock_eqb_symmetric_true (b1 b2:AnyBlock)
  : anyblock_eqb b1 b2 =true -> anyblock_eqb b2 b1=true.
Proof.
  intro H.
  destruct b1 as [n b1'].
  destruct b2 as [m b2'].
  simpl.
  simpl in H.
  apply eqb_symmetric, H.
Qed.

Lemma anyblock_eqb_symmetric_false (b1 b2:AnyBlock)
  : anyblock_eqb b1 b2 =false -> anyblock_eqb b2 b1=false.
Proof.
  intro H.
  destruct (anyblock_eqb b2 b1) eqn:H2.
  -  apply anyblock_eqb_symmetric_true in H2.
    rewrite H2 in H.
    inversion H.
  - reflexivity.
Qed.

Definition get_block_number {n : nat} (block : Block n) : nat :=
  match block with
  | OriginBlock => 0
  | NewBlock _ _ => S n
  end.


Lemma symmetric_aux {n m:nat} : n=m -> m=n.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

(** * Cast 
  As mentioned before, the comparation of blocks of different lenght
   require us to have a way to tranform a block type.
*)
Fixpoint cast {n} (block:Block n) {struct block}: forall {m}, m = n -> Block m
  :=
  match block in Block n' return forall m, m = n' -> Block m with 
  | OriginBlock 
      => fun m 
        => match m with 
           | 0 =>fun H => OriginBlock
           | S m' =>fun H 
               => False_rec (Block (S m')) (Nat.neq_succ_0 _ H)
          end 
  | NewBlock oldBlock id
      => fun m 
        => match m with 
           | 0 =>fun H 
               => False_rec 
                (Block 0) 
                (Nat.neq_succ_0 _ (symmetric_aux H))
           | S m' => fun H 
               => NewBlock (cast oldBlock (m:=m') (f_equal pred H)) id
          end 
  end.

Lemma cast_origin_is_origin {m} (eq_n_m:m=0)
  : OriginBlock =? (cast OriginBlock (m:=m) eq_n_m) = true.
Proof.
  simpl.
  rewrite eq_n_m.
  reflexivity.
Qed.

Lemma cast_are_same {n} (block:Block n) {m} (eq_n_m:m=n) 
  : block =? (cast block (m:=m) eq_n_m)=true.
Proof.
  dependent induction block.
  - apply cast_origin_is_origin.
  - simpl.
    rewrite eq_n_m.
    simpl.
    apply Bool.andb_true_iff.
    split.
    + apply Nat.eqb_refl.
    + apply IHblock.
Qed.

Lemma cast_eqb_are_equal {n m} (block1: Block n) (block2:Block m)
  (are_equal:block1 =? block2 = true) 
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
    apply (Nat.eqb_eq id) in eq_id.
    rewrite <- eq_id.
    pose (IHblock1 n0 block2 eqb_blocks (f_equal Nat.pred same_nats)) as eq_blocks.
    simpl.
    rewrite <- eq_blocks.
    reflexivity.
Qed.

(**  * Prefix
   [Prefix B B'] in the paper is presented as [B <= B'].
*)
Inductive Prefix : forall {n}, Block n -> forall {m}, Block m -> Type :=
  (** [B <= B']*)
  | Same : forall n (block : Block n), Prefix block block
  (** [B <= B'  ->  B <= (b :: B')] *)
  | IsPrefix {n m} (block1: Block n) (block2: Block m) (block_id : nat) :
      Prefix block1 block2 -> Prefix block1 (NewBlock block2 block_id).

Notation " a <= b " := (Prefix a b):blocks_scope.

Lemma originBlock_is_always_prefix  {n} (block:Block n):  OriginBlock <= block.
Proof.
  induction block.
  - apply Same.
  - apply IsPrefix.
    apply IHblock.
Qed.

Lemma prefix_of_newblock {n m} (block1: Block n) (block2:Block m) {id} 
  : block1 <= block2 -> block1 <= (NewBlock block2 id).
Proof.
  auto using IsPrefix.
Qed.

Lemma newblock_prefix {n m} (block1: Block n) (block2:Block m) {id} 
  : (NewBlock block1 id) <= block2 -> block1 <= block2.
Proof.
  intro H.
  induction block2.
  - dependent destruction block1.
    + apply Same.
    + inversion H.
  - dependent destruction H.
    + apply IsPrefix. apply Same.
    + apply IHblock2 in H.
      auto using IsPrefix.
Qed.


Lemma prefix_transitive {n m r} 
  (block1: Block n) (block2:Block m) (block3: Block r) 
  : block1 <= block2 -> block2 <= block3 -> block1 <= block3.
Proof.
  intros h1_2.
  dependent induction h1_2.
  - auto.
  - intro H.
    apply IHh1_2.
    apply (newblock_prefix block2 block3 H).
Qed.

Lemma prefix_height_is_below {n m} (block1: Block n) (block2:Block m)
  : block1 <= block2 -> (n <= m)%nat.
Proof.
  intro H.
  dependent induction block2.
  - destruct block1.
    + auto.
    + inversion H.
  - dependent destruction block1.
    + apply Nat.le_0_l.
    + dependent destruction H.
      ++ auto.
      ++ apply IHblock2 in H.
         auto using le_S.
Qed.


Lemma eqb_blocks_are_prefix {n} (block1 block2: Block n): block1 =? block2 = true -> block1 <= block2.
Proof.
  intro H.
  rewrite (eqb_eq block1 block2) in H.
  rewrite H.
  refine (Same n block2).
Qed.


Lemma eqb_blocks_are_prefix2 {n m} (block1: Block n) (block2:Block m)
  (are_equal:block1 =? block2 = true) 
  (same_nats: n = m)
(*: block1 = cast block2 (eqb_implies_same_nat _ _ are_equal).
Proof.
  remember (cast block2 (eqb_implies_same_nat _ _ are_equal)) as block3.
*)

  :  block1 <= (cast block2 same_nats ).
Proof.
  assert (block1 = cast block2 same_nats).
    {
    apply cast_eqb_are_equal.
    assumption.
    }
    rewrite <- H.
    refine (Same n block1).
Qed.

Lemma eqb_blocks_are_prefix3 {n m} (block1: Block n) (block2:Block m)
  (are_equal: block1 =? block2 = true) 
  (same_nats: m = n)
  :  (cast block1 same_nats ) <= block2.
Proof.
  assert (block2 = cast block1 same_nats).
    {
    apply cast_eqb_are_equal.
    apply eqb_symmetric.
    assumption.
    }
    rewrite <- H.
    refine (Same m block2).
Qed.


(** ** is_prefix
  Although we already have Prefix, it's definition tell us what a 
   prefix is, not how to take two blocks and find a prefix.
*)


Fixpoint is_prefix {n m} (block1 : Block n) (block2: Block m) {struct block2} : bool 
 :=
  if n <? m then
    match block2 with
    | OriginBlock =>  false (* in this case m =0 -> n<0 -> false *)
    | NewBlock old_block id => is_prefix block1 old_block
    end
  else
    if (n =? m)%nat then
      block1 =? block2 
    else
    false.

Lemma is_prefix_reflexive {n} (block :Block n)
  : is_prefix block block = true.
Proof.
  dependent induction block.
  - auto.
  - simpl.
    rewrite (Nat.ltb_irrefl (S n)).
    rewrite (Nat.eqb_refl n).
    apply andb_true_intro.
    split.
    + apply Nat.eqb_refl.
    + apply eqb_reflexive.
Qed.

Lemma prefix_of_cast_right {n} (block1 : Block n) 
  :forall  {m} (block2: Block m) {w} (eq_w_m: w = m)
    ,block1 <= (cast block2 eq_w_m)-> block1 <= block2.
Proof.
  dependent induction block2.
  - intros w eq_w_m H. 
    dependent destruction H.
    + simpl.
      destruct n.
      ++ apply Same.
      ++ inversion eq_w_m.
  - intros w eq_w_n0 H.
    dependent destruction H.
    2:{
      apply prefix_of_newblock.
      remember (f_equal Nat.pred eq_w_n0) as x.
      simpl in x.
      apply (IHblock2  _ x ).
      auto.
    }
    remember (NewBlock block2 id) as x.
    pose (eqb_blocks_are_prefix3 x x ).
    rewrite eq_w_n0.
    apply p.
    apply eqb_reflexive.
Qed.


Lemma prefix_implies_is_prefix {n} (block1 : Block n)
  : forall {m} (block2: Block m) ,
  block1 <= block2 -> is_prefix block1 block2 = true.
Proof.
  dependent induction block2.
  - intro H.
    simpl.
    dependent destruction block1. 
    + auto.
    + inversion H.
  - intro H.
    dependent destruction H.
    + apply is_prefix_reflexive.
    + apply IHblock2 in H as is_prefix_1_2.
      simpl.
      apply prefix_height_is_below in H as n_leq_n0.
      apply (Nat.leb_le) in n_leq_n0.
      unfold Nat.ltb.
      simpl.
      rewrite n_leq_n0.
      auto.
Qed.

Lemma is_prefix_implies_prefix {n} (block1 : Block n)
  : forall {m} (block2: Block m) ,
  is_prefix block1 block2 = true -> block1 <= block2.
Proof.
  dependent induction block2.
  - intro H.
    dependent destruction block1. 
    + apply Same.
    + inversion H.
  - intro H.
    unfold is_prefix in  H.
    destruct (n <? (S n0)) eqn:Hlet.
    + apply prefix_of_newblock.
      apply IHblock2.
      auto.
    + destruct (n =? (S n0))%nat.
      2:{ inversion H. }
      ++ pose (eqb_implies_same_nat _ _ H) as n_eq_Sn0.
         pose (eqb_blocks_are_prefix2 _ _ H n_eq_Sn0) as Hcast.
         apply (prefix_of_cast_right block1 (NewBlock block2 id) n_eq_Sn0).
         assumption.
Qed.

Definition is_prefix_some {n m} 
  (block1 : Block n) (block2: Block m) 
  : option (block1 <= block2) .
Proof.
  destruct (is_prefix block1 block2) eqn:H.
  - apply Some.
    apply is_prefix_implies_prefix.
    auto.
  - exact None.
Qed.

(** * More blocks relations
*)
 

(**
  [IsChildren B B' = B' < B]
 *)

Variant IsChildren {n m} (block1 :Block n) (block2: Block m) : Type :=
  | IsChildrenC (is_prefix: block1 <= block2) (block_number_is_above: n<m) :
      IsChildren block1 block2.

Notation " a < b " := (IsChildren a b):blocks_scope.

(** 
   The relation B ~ B' in the paper
 *)
Variant Related {n m} (block1:Block n) (block2 :Block m) : Prop :=
  | RelatedAsChildren
    : block1 < block2 -> Related block1 block2
  | RelatedAsParent
    : block2 < block1 -> Related block1 block2
  | RelatedAsEquals: block1 =? block2 = true -> Related block1 block2.

Notation " a ~ b " := (Related a b)(at level 70, right associativity):blocks_scope.

Definition Unrelated {n m} (block1 : Block n) (block2 :Block m) : Prop := not (block1 ~ block2).

Lemma related_symmetric : forall {n} (block1:Block n) {m} (block2 :Block m)
  , block1 ~ block2 -> block2 ~ block1.
Proof.
  intros n b1 m b2 H.
  destruct H. 
  - refine (RelatedAsParent _ _ H).
  - refine (RelatedAsChildren _ _ H).
  - apply RelatedAsEquals.
    auto using eqb_symmetric.
Qed.

Lemma prefix_implies_related  {n m} (block1:Block n) (block2:Block m) 
  : block1 <= block2 -> block1 ~ block2.
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

Definition is_related_some {n m} (block1:Block n) (block2:Block m) 
  : option (block1 ~ block2)
  :=
  match is_prefix_some block1 block2 with
  | Some p => Some (prefix_implies_related block1 block2 p)
  | None 
      => match is_prefix_some block2 block1 with
         | Some p 
             =>Some 
                (related_symmetric _ _ (prefix_implies_related block2 block1 p))
         | None => None
          end
  end.

Definition is_related {n m} (block1:Block n) (block2:Block m) 
  : bool
  := is_prefix block1 block2 || is_prefix block2 block1.


Lemma decidable_related : forall n (block1:Block n) m (block2 :Block m)
  , {block1 ~ block2} + {Unrelated block1 block2}.
Proof.
  intros n b1 m b2.
  remember (is_prefix b1 b2) as maybe_prefix1_2.
  destruct maybe_prefix1_2.
  - left.  
    apply prefix_implies_related. 
    apply (is_prefix_implies_prefix). 
    auto.
  - remember (is_prefix b2 b1) as maybe_prefix2_1.
    destruct maybe_prefix2_1.
    + left.  
      apply related_symmetric.
      apply prefix_implies_related. 
      apply (is_prefix_implies_prefix). 
      auto.
    + right.
      unfold Unrelated.
      unfold not.
      intro H.
      destruct H. 
      ++ destruct H.
         apply prefix_implies_is_prefix in is_prefix0. 
         rewrite is_prefix0 in Heqmaybe_prefix1_2.
         inversion Heqmaybe_prefix1_2.
      ++ destruct H.
         apply prefix_implies_is_prefix in is_prefix0. 
         rewrite is_prefix0 in Heqmaybe_prefix2_1.
         inversion Heqmaybe_prefix2_1.
      ++ pose (eqb_implies_same_nat _ _ H) as same_nat.
         pose (eqb_blocks_are_prefix2 _ _ H same_nat) as H2.
         pose (prefix_of_cast_right b1 b2 same_nat H2) as H3.
         pose (prefix_implies_is_prefix _ _ H3) as H4.
         rewrite H4 in Heqmaybe_prefix1_2.
         discriminate Heqmaybe_prefix1_2.
Qed.

Lemma unrelated_symmetric {n1 n2 :nat} (b1:Block n1) (b2:Block n2) : Unrelated b1 b2 -> Unrelated b2 b1.
Proof.
  intro H.
  destruct (decidable_related n2 b2 n1 b1).
  - exfalso. pose (related_symmetric b2 b1 r) as r2. auto.
  - auto.
Qed.

Lemma different_blocks_of_same_height_are_unrelated : 
  forall n (block1 block2 :Block n) 
  , block1 <> block2 -> Unrelated block1 block2.
Proof.
  intros n b1 b2 no_eq Hrelated.
  destruct Hrelated as [Hrelated|Hrelated|Hrelated].
  - destruct Hrelated.
    apply (Nat.lt_irrefl n).
    auto.
  - destruct Hrelated.
    apply (Nat.lt_irrefl n).
    auto.
  - rewrite eqb_eq in Hrelated.
    contradiction.
Qed.

Lemma same_bound_implies_related {n1 n2 n3} 
  {b1: Block n1}
  {b2: Block n2}
  {b3: Block n3}
  (b1_b2:b1 <= b2)
  (b3_b2:b3 <= b2)
  : b1 ~ b3.
Proof.
  Admitted.

Lemma prefixed_block_of_unrelated_is_unrelated {n1 n2 n3}
  {b1: Block n1}
  {b2: Block n2}
  {b3: Block n3}
  (prefix_proof:b1 <= b2)
  (unrelated: Unrelated b1 b3 )
  : Unrelated b2 b3. 
Proof.
  unfold Unrelated.
  unfold not. 
  intro contra. 
  inversion contra. 
  - destruct H.
    pose (prefix_transitive _ _ _ prefix_proof is_prefix0) as b1_b3.
    pose (prefix_implies_related _ _ b1_b3) as related_contra.
    unfold Unrelated in unrelated.
    contradiction.
  - destruct H as [prefix_proof_b3_b2].
    pose (same_bound_implies_related prefix_proof prefix_proof_b3_b2) as contra2.
    contradiction.
  - pose (eqb_symmetric _ _ H) as b3_b2.
    pose (eqb_implies_same_nat _ _ b3_b2) as same_nat .
    pose  (eqb_blocks_are_prefix2 b3 b2 b3_b2 same_nat) as b3_b2_cast.
    pose (prefix_of_cast_right _ _ same_nat b3_b2_cast) as b3_prefix_b2. 
    pose (same_bound_implies_related prefix_proof b3_prefix_b2) as contra2.
    contradiction.
Qed.

Close Scope blocks_scope.
