Require Import Blocks.
Require Import Votes.
Require Import Preliminars.


Definition Time := nat.

Inductive RoundState 
      {preview_number precommit_number last_block_number}
  (preview_voters:Voters preview_number) 
  (precommit_voters: Voters precommit_number)
  (round_start_time:Time) 
  (last_block: Block last_block_number)
    : Time ->  Type :=
  | InitialRoundState 
    : RoundState preview_voters precommit_voters round_start_time last_block 0
  | RoundStateUpdate 
    {old_time_increment: Time}
    (old_state: RoundState 
      preview_voters precommit_voters 
      round_start_time last_block old_time_increment)
    (time_increment: Time)
    (new_preview_votes: Votes preview_voters last_block)
    (new_precommit_votes: Votes precommit_voters last_block)
    : RoundState preview_voters precommit_voters round_start_time last_block 
      (time_increment+ old_time_increment).

Section State1.

Context {preview_number precommit_number last_block_number : nat}.
Context {preview_voters:Voters preview_number }.
Context {precommit_voters: Voters precommit_number}.
Context {last_block: Block last_block_number}.
Context {round_time : Time}.
Context {round_number: nat}.




Definition get_preview_votes
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number)
  : 
  (Votes preview_voters last_block)
  := 
  match round_state with
  | InitialRoundState _ _ _ _ => VotesC _ _ List.nil (* No votes in initial round state *)
  | RoundStateUpdate _ _ _ _ _ _ new_preview_votes _ => new_preview_votes
  end.

Definition get_precommit_votes
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number)
  : 
  (Votes precommit_voters last_block).
Admitted.

End State1.

Variant Estimate {preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number)
  : nat -> Type
  :=
  (*TODO: add origin block case*)
    |EstimateC 
    {new_block_number : nat}
    (new_block : Block new_block_number)
    (is_children: IsChildren new_block last_block)
    {g_block_number: nat}
    (g_preview: Block g_block_number)
    (g_preview_is_some : g ( get_preview_votes round_state) = Some (existT _ g_block_number g_preview))
    (new_block_is_ancestor_of_g: Prefix new_block g_preview)
    : Estimate round_state new_block_number.



Section State2.

Context {preview_number precommit_number last_block_number : nat}.
Context {preview_voters:Voters preview_number }.
Context {precommit_voters: Voters precommit_number}.
Context {last_block: Block last_block_number}.
Context {round_time : Time}.
Context {round_number: nat}.


Definition get_estimate_block
  {round_state: RoundState preview_voters precommit_voters  round_time last_block round_number}
  {n}
  (e:Estimate round_state n)
  : Block n.
Admitted.

Definition get_estimate 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number)
  : option (sigT (fun n  => Estimate  round_state n)).
Admitted.


Variant Completable 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number)
  : Type
  :=
  | CompletableBelowPreview {estimate_block_number}
      (e: Estimate  round_state estimate_block_number)
      {g_block_number: nat}
      (g_preview: Block g_block_number)
      (g_preview_is_some 
        : g ( get_preview_votes round_state) 
          = Some (existT _ g_block_number g_preview)
      )
      (new_block_is_below_g: estimate_block_number < g_block_number)
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
