Require Import Blocks.AnyBlock.
Require Import Votes.
Require Import Preliminars.
Require Import Round.

Export Round.

Require Import Nat.

Require Import Classes.Eqb.

Open Scope eqb.

Variant Estimate
  {total_voters:nat}
  {prevote_voters : Voters}
  {precommit_voters: Voters}
  {round_time:Time}
  {round_number:RoundNumber}
  {time_increment: Time}
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : AnyBlock -> Type
  :=
    | EstimateOrigin : round_number = RoundNumber.from_nat 0 -> Estimate round_state (AnyBlock.to_any OriginBlock)
    |EstimateC
    {new_block_number : nat}
    (new_block : Block new_block_number)
    {g_block_number: nat}
    (g_prevote: Block g_block_number)
    (g_prevote_is_some : g ( get_prevote_votes round_state) = Some (AnyBlock.to_any g_prevote))
    (new_block_is_ancestor_of_g: Prefix new_block g_prevote)
    : Estimate round_state (AnyBlock.to_any new_block).



Section State2.

Context {total_voters:nat}.
Context {prevote_voters:Voters}.
Context {precommit_voters: Voters}.
Context {round_time : Time}.
Context {round_number: RoundNumber}.
Context {time_increment : Time}.


(* Projection of the type Estimate *)
Definition get_estimate_block
  {round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment}
  {n}
  {block : Block n}
  (estimate :Estimate round_state (AnyBlock.to_any block))
  : Block n
  :=
  match estimate with
    | EstimateOrigin _ _ => OriginBlock
    | EstimateC _ new_block _ _ _ => new_block
  end.

Fixpoint get_estimate_aux_recursive {gv_block_number:nat}
  (gv:Block gv_block_number)
  (precommit_supermajority_blocks: list (AnyBlock*nat))
  : option AnyBlock
  :=
  let find_block any_block :=
    match any_block with
      | (block,_)
        => AnyBlock.to_any gv =? block
    end
  in
  match List.find find_block precommit_supermajority_blocks with
    | None
        => match gv with
            | OriginBlock => None
            | NewBlock old_block _
                =>
                get_estimate_aux_recursive
                  old_block
                  precommit_supermajority_blocks
            end
    | Some (any_block,_)
        => Some any_block
  end.

Definition get_estimate_aux
  (prevote_votes: Votes prevote_voters )
  (precommit_votes: Votes precommit_voters )
  : option AnyBlock
  :=
  match g prevote_votes with
  | None => None
  | Some g_prevote_votes =>
    let precommit_supermajority_blocks :=
      get_supermajority_blocks precommit_votes
    in
      get_estimate_aux_recursive
        (g_prevote_votes.(AnyBlock.block))
        precommit_supermajority_blocks
  end.

Definition get_estimate
  (round_state:
    RoundState total_voters prevote_voters precommit_voters
      round_time  round_number
      time_increment
  )
  : option AnyBlock
  :=
 match round_state  with
  | InitialRoundState _ _ _ _ _ =>
      if (RoundNumber.to_nat round_number) =? 0 then
      Some (AnyBlock.to_any OriginBlock)
      else
      None
  | RoundStateUpdate _ _ _ _ _ _ _ _ _=>
    let all_prevote_votes := get_all_prevote_votes round_state
    in
    let all_precommit_votes := get_all_precommit_votes round_state
    in
    get_estimate_aux all_prevote_votes all_precommit_votes
  end.


End State2.

Section State3.
Context {total_voters: nat}.
Context {prevote_voters:Voters  }.
Context {precommit_voters: Voters }.
Context {round_time : Time}.
Context {round_number: RoundNumber}.
Context {time_increment : Time}.


Lemma get_estimate_aux_recursive_is_none_on_nil :
  forall {n} (block:Block n)
  ,get_estimate_aux_recursive block nil = None.
Proof.
  intro n. induction n as [|n HInductive]
    ;intro block.
    + dependent inversion block.
      simpl. reflexivity.
    + dependent inversion block.
      simpl.
      apply HInductive.
Qed.

Theorem get_estimate_output_is_estimate
  {block:AnyBlock}
  (round_state:
    RoundState total_voters prevote_voters precommit_voters
      round_time  round_number
      time_increment
  )
  (get_estimate_result
    : get_estimate round_state = Some block
  )
  : Estimate round_state block.
Proof.
Admitted.
(*
dependent destruction block.
  - refine (EstimateOrigin round_state _).
*)

Theorem estimate_is_output_of_get_estimate
  {block:AnyBlock}
  (round_state:
    RoundState total_voters prevote_voters precommit_voters
      round_time  round_number
      time_increment
  )
  (is_estimate: Estimate round_state block)
  : get_estimate round_state = Some block.
Proof.
Admitted.
(*
dependent destruction block.
  - refine (EstimateOrigin round_state _).
*)



Variant Completable
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : Type
  :=
  | CompletableBelowPreview {number_and_block}
      (e: Estimate  round_state number_and_block)
      (g_prevote: AnyBlock)
      (g_prevote_is_some
        : g ( get_prevote_votes round_state)
          = Some g_prevote
      )
      (new_block_is_below_g: number_and_block.(AnyBlock.block_number) < g_prevote.(AnyBlock.block_number))
  | CompletableByImpossible
      (g_prevote: AnyBlock)
      (e: Estimate  round_state g_prevote)
      (
        g_prevote_is_some
        : g ( get_prevote_votes round_state)
          = Some g_prevote
      )
      (cant_have_supermajority
        : Preliminars.ImpossibleSupermajorityForAnyChildren (get_prevote_votes round_state) g_prevote
      )
  .

Definition try_to_complete_round
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : option (Completable round_state).
(* needs to define possible and impossible supermajority*)
Admitted.

Definition is_completable
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : bool
  :=
  match try_to_complete_round round_state with
  | None => false
  | _ => true
  end.


Definition get_estimate_from_completable
  {round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment}
  (completable:Completable round_state)
  : {block & Estimate round_state block}.
Proof.
  destruct completable.
  - refine (existT _ number_and_block e).
  - refine (existT _ g_prevote e).
Qed.

End State3.

Close Scope eqb.
