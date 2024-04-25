Require Import Blocks.                 
Require Import Votes.                  
Require Import Preliminars.
Require List.

Require Import Nat.
Require Arith.Compare_dec.
Require Import Program.Equality.

Definition Time := nat.

Inductive RoundState 
      {preview_number precommit_number last_block_number}
  (preview_voters:Voters preview_number) 
  (precommit_voters: Voters precommit_number)
  (round_start_time:Time) 
  (last_block: Block last_block_number)
  (round_number: nat)
  : Time ->  Type :=
  | InitialRoundState 
    : RoundState preview_voters precommit_voters round_start_time last_block round_number 0
  | RoundStateUpdate 
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
  | InitialRoundState _ _ _ _ _ => VotesC _ _ List.nil 
  | RoundStateUpdate _ _ _ _ _ _ _ new_preview_votes _ => new_preview_votes
  end.

Definition get_precommit_votes
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  (Votes precommit_voters last_block)
  :=
  match round_state with
  | InitialRoundState _ _ _ _ _=> VotesC _ _ List.nil (* No votes in initial round state *)
  | RoundStateUpdate _ _ _ _ _ _ _ _ new_precommit_votes => new_precommit_votes
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
  | InitialRoundState _ _ _ _ _ => VotesC _ _ List.nil 
  | RoundStateUpdate _ _ _ _ _ old_state  _ new_preview_votes _ => mergeVotes (get_all_preview_votes old_state) new_preview_votes
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
  | InitialRoundState _ _ _ _ _=> VotesC _ _ List.nil 
  | RoundStateUpdate _ _ _ _ _ old_state  _ _ new_precommit_votes => mergeVotes (get_all_precommit_votes old_state) new_precommit_votes
  end.

Definition voter_voted_in_preview {preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  {time_increment: Time}
  (voter:Voter)
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  bool
  := 
  let preview_votes := get_all_preview_votes round_state
  in
    if in_Voters_bool voter preview_voters 
    then voter_voted_in_votes voter preview_votes
    else true.

Definition  voter_voted_in_precommit {preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  {time_increment: Time}
  (voter:Voter)
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  bool
  := 
  let precommit_votes := get_all_precommit_votes round_state
  in
    if in_Voters_bool voter precommit_voters 
    then voter_voted_in_votes voter precommit_votes
    else true.



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


(* Projection of the type Estimate *)
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

Fixpoint get_estimate_aux_recursive {gv_block_number block_number:nat} 
  (block:Block block_number)
  (gv:Block gv_block_number)
  (precommit_supermajority_blocks: list (AnyBlock*nat))
  : option AnyBlock
  :=
    if block_number <? gv_block_number
    then 
      let find_block any_block := 
        match any_block with
          | (existT _ block_number block,_)
            => Blocks.eqb gv block
        end
      in
      match List.find find_block precommit_supermajority_blocks with 
        | None 
            => match gv with
                | OriginBlock => None
                | NewBlock old_block _ 
                    =>  
                    get_estimate_aux_recursive 
                      block
                      old_block 
                      precommit_supermajority_blocks
                end
        | Some (any_block,_)
            => Some any_block
      end
    else None.

Definition get_estimate_aux 
  (preview_votes: Votes preview_voters last_block) 
  (precommit_votes: Votes precommit_voters last_block)
  : option AnyBlock
  :=
  match g preview_votes with 
  | None => None
  | Some g_preview_votes =>
    let precommit_supermajority_blocks := 
      get_supermajority_blocks precommit_votes
    in
      get_estimate_aux_recursive 
        last_block
        (projT2 g_preview_votes) 
        precommit_supermajority_blocks
  end.

Definition get_estimate 
  (round_state: 
    RoundState preview_voters precommit_voters  
      round_time last_block round_number 
      time_increment
  )
  : option AnyBlock
  :=
 match round_state  with
  | InitialRoundState _ _ _ _ _ => 
      if Nat.eqb round_number 0 then
      Some (existT _ 0 OriginBlock)
      else
      None
  | RoundStateUpdate _ _ _ _ _ _ _ _ _=> 
    let all_preview_votes := get_all_preview_votes round_state
    in
    let all_precommit_votes := get_all_precommit_votes round_state
    in
    get_estimate_aux all_preview_votes all_precommit_votes
  end.


End State2.

Section State3.
Context {preview_number precommit_number last_block_number : nat}.
Context {preview_voters:Voters preview_number }.
Context {precommit_voters: Voters precommit_number}.
Context {last_block: Block last_block_number}.
Context {round_time : Time}.
Context {round_number: nat}.
Context {time_increment : Time}.


Lemma get_estimate_aux_recursive_is_none_on_nil : 
  forall {m} (last_block_lemma:Block m) 
         {n} (block:Block n) ,   
                    get_estimate_aux_recursive 
                      last_block
                      block
                      nil = None.
Proof.
  intros m last_block_lemma. 
  - intro n. induction n as [|n HInductive]
    ;intro block. 
    + dependent inversion block.
      simpl. reflexivity.
    + dependent inversion block. 
      simpl. 
      destruct (last_block_number <? S n).
      ++  apply HInductive.
      ++  reflexivity.
Qed.
      


Lemma get_estimate_result_is_children  
  {block_number:nat}
  {block:Block block_number}
  (round_state: 
    RoundState preview_voters precommit_voters  
      round_time last_block round_number 
      time_increment
  )
  (round_is_not_zero: round_number <> 0)
  (get_estimate_result
    : get_estimate round_state = Some (existT _ block_number block)
  )
  : Prefix block last_block.
Proof.
  unfold get_estimate in get_estimate_result.
  destruct round_state eqn:H_state.
  - destruct round_number eqn:H_round_number.
    + contradiction.
    + simpl in get_estimate_result.
      discriminate get_estimate_result.
  - simpl in get_estimate_result.
    unfold get_estimate_aux in get_estimate_result.
    destruct (g (mergeVotes (get_all_preview_votes r) new_preview_votes)) 
      as [g_preview|] eqn:g_preview_eq.
    2: 
      discriminate get_estimate_result.
    + destruct 
        (get_supermajority_blocks
          (mergeVotes (get_all_precommit_votes r) new_precommit_votes)
        ) eqn:precommit_supermajority_blocks_eq.
      ++ assert (get_estimate_aux_recursive last_block (projT2 g_preview) nil = None) as is_nil.
         {
            apply (get_estimate_aux_recursive_is_none_on_nil last_block (projT2 g_preview) ).
          }
         rewrite is_nil in get_estimate_result.
         discriminate.
      ++ unfold get_estimate_aux_recursive in get_estimate_result.
         simpl in get_estimate_result.
         Admitted.
(* TODO: Finish it *)


Theorem get_estimate_output_is_estimate 
  {block_number:nat}
  {block:Block block_number}
  (round_state: 
    RoundState preview_voters precommit_voters  
      round_time last_block round_number 
      time_increment
  )
  (get_estimate_result
    : get_estimate round_state = Some (existT _ block_number block)
  )
  : Estimate round_state (existT _ block_number block).
Proof.
Admitted.
(*  
dependent destruction block.
  - refine (EstimateOrigin round_state _).
*)



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

Definition try_to_complete_round
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : option (Completable round_state).
(* needs to define possible and impossible supermajority*)
Admitted.

Definition is_completable 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : bool
  :=
  match try_to_complete_round round_state with
  | None => false
  | _ => true
  end.



End State3.


Definition Source (X:Type) := forall (t:Time) (r:nat) (v:Voter), X.

Definition const_source {X:Type} (x:X) : Source X := fun t r v => x.

Definition Voters_source (s_bizantine:Source nat) := forall t r v, Voters (s_bizantine t r v).

Definition Block_source (s:Source nat) := forall t r v, Block (s t r v).

Definition Vote_source (t:Time) (r:nat) (v:Voter) {s_voters_nat: Source nat} 
  (s_voters: forall t r v, Voters (s_voters_nat t r v)) 
  {s_blocks_nat: Source nat} (s_blocks : Block_source s_blocks_nat)
  :=  
    Vote (s_voters t r v) (s_blocks t r v).

Definition Votes_source  (t:Time) (r:nat) (v:Voter) {s_voters_nat: Source nat} 
  (s_voters: forall t r v, Voters (s_voters_nat t r v)) 
  {s_blocks_nat: Source nat} (s_blocks : Block_source s_blocks_nat)
  := Votes (s_voters t r v) (s_blocks t r v).

Definition RoundState_source (t:Time) (r:nat) (v:Voter) {s_preview_voters_nat s_precommit_voters_nat: Source nat} 
  (s_preview_voters: forall t r v, Voters (s_preview_voters_nat t r v)) 
  (s_precommit_voters: forall t r v, Voters (s_precommit_voters_nat t r v)) 
  {s_round_start_time:Source Time }
  {s_last_block_nat: Source nat} (s_last_block : Block_source s_last_block_nat)
  {s_time_increment:Source Time }
  := 
  RoundState
    (preview_number:= s_preview_voters_nat t r v)
    (precommit_number:= s_precommit_voters_nat t r v)
    (last_block_number:=s_last_block_nat t r v)
    (s_preview_voters t r v) 
    (s_precommit_voters t r v) 
    (s_round_start_time t r v) 
    (s_last_block t r v) 
    r
    (s_time_increment t r v).

Definition Estimate_source (t:Time) (r:nat) (v:Voter) 
  {s_preview_voters_nat s_precommit_voters_nat: Source nat} 
  {s_preview_voters: forall t r v, Voters (s_preview_voters_nat t r v)}
  {s_precommit_voters: forall t r v, Voters (s_precommit_voters_nat t r v)}
  {s_round_start_time:Source Time }
  {s_last_block_nat: Source nat} {s_last_block : Block_source s_last_block_nat}
  {s_time_increment:Source Time}
  (s_roundstate:
      RoundState
        (preview_number:= s_preview_voters_nat t r v)
        (precommit_number:= s_precommit_voters_nat t r v)
        (last_block_number:=s_last_block_nat t r v)
        (s_preview_voters t r v) 
        (s_precommit_voters t r v) 
        (s_round_start_time t r v) 
        (s_last_block t r v) 
        r 
        (s_time_increment t r v)
  )
  := Estimate
        (preview_number:= s_preview_voters_nat t r v)
        (precommit_number:= s_precommit_voters_nat t r v)
        (preview_voters:=s_preview_voters t r v) 
        (precommit_voters:=s_precommit_voters t r v) 
        (round_time:=s_round_start_time t r v) 
        (round_number:=r) 
        (last_block_number:=s_last_block_nat t r v)
        (last_block:=s_last_block t r v) 
        (time_increment:=s_time_increment t r v)
        s_roundstate.


Definition Completable_source (t:Time) (r:nat) (v:Voter) 
  {s_preview_voters_nat s_precommit_voters_nat: Source nat} 
  {s_preview_voters: forall t r v, Voters (s_preview_voters_nat t r v)}
  {s_precommit_voters: forall t r v, Voters (s_precommit_voters_nat t r v)}
  {s_round_start_time:Source Time }
  {s_last_block_nat: Source nat} {s_last_block : Block_source s_last_block_nat}
  {s_time_increment:Source Time}
  (s_roundstate: forall t r v,
      RoundState
        (preview_number:= s_preview_voters_nat t r v)
        (precommit_number:= s_precommit_voters_nat t r v)
        (last_block_number:=s_last_block_nat t r v)
        (s_preview_voters t r v) 
        (s_precommit_voters t r v) 
        (s_round_start_time t r v) 
        (s_last_block t r v) 
        r
        (s_time_increment t r v)
  )
  := Completable (s_roundstate t r v).



Fixpoint voter_already_votes_in_all (t:Time) (r:nat) (v:Voter)
  {s_preview_voters_nat s_precommit_voters_nat: Source nat} 
  {s_preview_voters: forall t r v, Voters (s_preview_voters_nat t r v)}
  {s_precommit_voters: forall t r v, Voters (s_precommit_voters_nat t r v)}
  {s_round_start_time:Source Time }
  {s_last_block_nat: Source nat} {s_last_block : Block_source s_last_block_nat}
  {s_time_increment:Source Time}
  (s_roundstate: forall t r v,
      RoundState
        (preview_number:= s_preview_voters_nat t r v)
        (precommit_number:= s_precommit_voters_nat t r v)
        (last_block_number:=s_last_block_nat t r v)
        (s_preview_voters t r v) 
        (s_precommit_voters t r v) 
        (s_round_start_time t r v) 
        (s_last_block t r v) 
        r
        (s_time_increment t r v)
  )
  {struct r}
  :bool
:= 
  match r with 
  | 0 => true
  | S r' => 
      voter_voted_in_preview v (s_roundstate t r v)
      && voter_voted_in_precommit v (s_roundstate t r v)
      && voter_already_votes_in_all t r' v s_roundstate
  end.

Definition can_start_round (t:Time) (r:nat) (v:Voter) 
  {s_preview_voters_nat s_precommit_voters_nat: Source nat} 
  {s_preview_voters: forall t r v, Voters (s_preview_voters_nat t r v)}
  {s_precommit_voters: forall t r v, Voters (s_precommit_voters_nat t r v)}
  {s_round_start_time:Source Time }
  {s_last_block_nat: Source nat} {s_last_block : Block_source s_last_block_nat}
  {s_time_increment:Source Time}
  (s_roundstate: forall t r v,
      RoundState
        (preview_number:= s_preview_voters_nat t r v)
        (precommit_number:= s_precommit_voters_nat t r v)
        (last_block_number:=s_last_block_nat t r v)
        (s_preview_voters t r v) 
        (s_precommit_voters t r v) 
        (s_round_start_time t r v) 
        (s_last_block t r v) 
        r
        (s_time_increment t r v)
  ):bool
  :=
  match r with
    | 0 => true
    | S r' 
      =>is_completable (s_roundstate t r' v) 
        && voter_already_votes_in_all t r' v s_roundstate
  end.

 
CoFixpoint decision 
  :=
  if can_start_round t r v s_round then 
    let t_initial := t 
    in
    if is_primary t_initial r v v s_round then
      if not_finalized estimate_last_round then
        propagate estimate_last_round 
      else 
        if finalized estimate_last_round then 
          propagate estimate_last_round
        else 
          real_round t_initial r v s_round
    else 
      real_round t_initial r v s_round
  else 
    decision (t+1) r v s_round.
    
Fixpoint prevoter_round t_initial t r v s_round {measure (t -t_initial - (2*GlobalTime)) <}
  := 
    if is_completable (s_roundstate t r v) || t_initial + 2 * GlobalTime <= t then
      let maybe_block := got_block_from_primary v t r s_round 
      in
      match maybe_block with
      | Some block => 
          match g V_previous with
            Some V => if is_prefix block V_previous && is_prefix estimate_previous block then 
              lookup_best_chain_for block 
              else 
                lookup_best_chain_for estimate_previous
            _ => 
                lookup_best_chain_for estimate_previous
      | _ => lookup_best_chain_for estimate_previous
    else 
      real_round t_initial t r v s_round.


Definition real_round t_initial t r v s_round
  :=
  if is_prevoter v t r s_round then 
    let prevote_result:= prevoter_round t_initial t r v s_round
    in
    if is_precommitvoter v t r s_round then 
      let precommit_result := precommit_round t r v s_round
      in
        update_round t r v s_round (Some prevote_result) (Some precommit_result)
    else

  (* We asume that every particiapant in a round is either a prevoter or precommit voter. *)
  else 
      let result := precommit_round t r v s_round 
      in 
        update_round t r v  s_round None (Some result)
    
