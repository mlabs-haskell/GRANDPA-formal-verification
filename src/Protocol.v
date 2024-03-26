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
  (Votes precommit_voters last_block)
  :=
  match round_state with
  | InitialRoundState _ _ _ _ => VotesC _ _ List.nil (* No votes in initial round state *)
  | RoundStateUpdate _ _ _ _ _ _ _ new_precommit_votes => new_precommit_votes
  end.

End State1.

Variant Estimate {preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number)
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


Definition get_estimate_block
  {round_state: RoundState preview_voters precommit_voters  round_time last_block round_number}
  {n}
  {block : Block n}
  (estimate :Estimate round_state (existT _ n block))
  : Block n
  :=
  match estimate with
    | EstimateOrigin _ _ => OriginBlock
    | EstimateC _ new_block _ _ _ _ => new_block
  end.

Print get_preview_votes.

Definition get_round_number
  (round_number2:Time)
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number2)
  : Type
  :=
    match round_state with 
    | InitialRoundState _ _ _ _ => RoundState preview_voters precommit_voters round_time last_block 0
    | _ => RoundState preview_voters precommit_voters round_time last_block round_number2
    end.

Definition get_estimate_case_1
  (round_state: RoundState preview_voters precommit_voters  round_time last_block 0)
  : option (Estimate round_state (existT _ 0 OriginBlock))
  :=
    match round_state with 
    | InitialRoundState _ _ _ _ => Some (EstimateOrigin round_state eq_refl)
    | _ => None
    end.

Require Import Equality.
Print block.
Locate block.

Definition get_estimate (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number)
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
  | _ => None
  end.

Definition get_estimate 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number)
  : option {n & { block & Estimate round_state (existT _ n block)}}.
Proof.
  dependent destruction  round_state.
  - refine (Some (existT _ 0 (existT _ OriginBlock (EstimateOrigin (InitialRoundState preview_voters precommit_voters round_time last_block) eq_refl))) ).
  - refine None.
Qed.


Print get_estimate.
  :=
 match round_state in RoundState _ _ _ _ 0 return option {n & { block & Estimate round_state (existT _ n block)}} with
  | InitialRoundState _ _ _ _ =>None
      (*Some (existT _ 0 (existT _ OriginBlock (EstimateOrigin round_state _)))*)
  | b => False_rect unit
  end.
  match round_number with
  | O =>
    Some (existT _ 0 (existT _ _ OriginBlock, EstimateOrigin eq_refl))
  | _ => g preview_votes

  end.


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
