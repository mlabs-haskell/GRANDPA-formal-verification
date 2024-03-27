Require Import Blocks.
Require Import Votes.
Require Import Preliminars.
Require Import List.


Definition Time := nat.

Inductive RoundState 
      {preview_number precommit_number last_block_number}
  (preview_voters:Voters preview_number) 
  (precommit_voters: Voters precommit_number)
  (round_start_time:Time) 
  (last_block: Block last_block_number)
  : nat -> Time ->  Type :=
  | InitialRoundState 
    : RoundState preview_voters precommit_voters round_start_time last_block 0 0
  | RoundStateUpdate 
    {round_number}
    {old_time_increment: Time}
    (old_state: RoundState 
      preview_voters precommit_voters 
      round_start_time last_block round_number old_time_increment)
    (time_increment: Time)
    (new_preview_votes: Votes preview_voters last_block)
    (new_precommit_votes: Votes precommit_voters last_block)
    : RoundState preview_voters precommit_voters round_start_time last_block 
      round_number
      (time_increment+ old_time_increment).

Section State1.

Context {preview_number precommit_number last_block_number : nat}.
Context {preview_voters:Voters preview_number }.
Context {precommit_voters: Voters precommit_number}.
Context {last_block: Block last_block_number}.
Context {round_time : Time}.
Context {round_number: nat}.
Context {time_increment: nat}.




Definition get_preview_votes
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  (Votes preview_voters last_block)
  := 
  match round_state with
  | InitialRoundState _ _ _ _ => VotesC _ _ List.nil 
  | RoundStateUpdate _ _ _ _ _ _ new_preview_votes _ => new_preview_votes
  end.

Definition get_precommit_votes
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  (Votes precommit_voters last_block)
  :=
  match round_state with
  | InitialRoundState _ _ _ _ => VotesC _ _ List.nil (* No votes in initial round state *)
  | RoundStateUpdate _ _ _ _ _ _ _ new_precommit_votes => new_precommit_votes
  end.

End State1.

Fixpoint get_all_preview_votes{preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  {time_increment: Time}
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  (Votes preview_voters last_block)
  := 
  match round_state with
  | InitialRoundState _ _ _ _ => VotesC _ _ List.nil 
  | RoundStateUpdate _ _ _ _ old_state  _ new_preview_votes _ => mergeVotes (get_all_preview_votes old_state) new_preview_votes
  end.

Fixpoint get_all_precommit_votes{preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  {time_increment: Time}
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  (Votes precommit_voters last_block)
  := 
  match round_state with
  | InitialRoundState _ _ _ _ => VotesC _ _ List.nil 
  | RoundStateUpdate _ _ _ _ old_state  _ _ new_precommit_votes => mergeVotes (get_all_precommit_votes old_state) new_precommit_votes
  end.



Variant Estimate {preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  {time_increment: Time}
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : {n & Block n} -> Type
  :=
    | EstimateOrigin : round_number = 0 -> Estimate round_state (existT _ 0 OriginBlock)
    |EstimateC 
    {new_block_number : nat}
    (new_block : Block new_block_number)
    (is_children: IsChildren new_block last_block)
    {g_block_number: nat}
    (g_preview: Block g_block_number)
    (g_preview_is_some : g ( get_preview_votes round_state) = Some (existT _ g_block_number g_preview))
    (new_block_is_ancestor_of_g: Prefix new_block g_preview)
    : Estimate round_state (existT _ new_block_number new_block).



Section State2.

Context {preview_number precommit_number last_block_number : nat}.
Context {preview_voters:Voters preview_number }.
Context {precommit_voters: Voters precommit_number}.
Context {last_block: Block last_block_number}.
Context {round_time : Time}.
Context {round_number: nat}.
Context {time_increment : Time}.


Definition get_estimate_block
  {round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment}
  {n}
  {block : Block n}
  (estimate :Estimate round_state (existT _ n block))
  : Block n
  :=
  match estimate with
    | EstimateOrigin _ _ => OriginBlock
    | EstimateC _ new_block _ _ _ _ => new_block
  end.


Definition get_estimate (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : option {n & { block & Estimate round_state (existT _ n block)}}
  :=
 match round_state  with
  | InitialRoundState _ _ _ _ => 
      Some 
      (existT _ 0 
        (existT _ 
          OriginBlock 
          (EstimateOrigin 
            (InitialRoundState preview_voters precommit_voters round_time
                   last_block 
            ) 
            eq_refl
          )
        )
      )
  | RoundStateUpdate _ _ _ _ _ _ _ _=> 
    let all_preview_votes := get_all_preview_votes round_state
    in
    let all_precommit_votes := get_all_precommit_votes round_state
    in
    None
  end.


Variant Completable 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : Type
  :=
  | CompletableBelowPreview {number_and_block}
      (e: Estimate  round_state number_and_block)
      {g_block_number: nat}
      (g_preview: Block g_block_number)
      (g_preview_is_some 
        : g ( get_preview_votes round_state) 
          = Some (existT _ g_block_number g_preview)
      )
      (new_block_is_below_g: projT1 number_and_block < g_block_number)
  | CompletableByImpossible 
      {g_block_number: nat}
      (g_preview: Block g_block_number)
      (
        g_preview_is_some 
        : g ( get_preview_votes round_state) 
          = Some (existT _ g_block_number g_preview)
      )
      (cant_have_supermajority 
        : forall n (block : Block n) 
          , g_block_number < n 
          -> has_supermajority (get_precommit_votes round_state) 
            = false
      )
  .
End State2.
