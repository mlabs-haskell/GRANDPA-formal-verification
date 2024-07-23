Require Import Blocks.AnyBlock.
Require Import Voters.
Require Import Preliminars.
Require Estimate.
Require OpaqueRound.
Require Round.
Require Import Time.
Require Import RoundNumber.
Require Import VoterState.
Require Import Vectors.
Require Import Sets.
Require Import Message.
Require Import DataTypes.List.Count.
Require Import Protocol.State.
Require Import Protocol.StateMessages.
Require Import Protocol.FinalizedBlock.

Require Import Program.Equality.
Require Import PeanoNat.

Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Classes.Math.All.
Require Import Instances.List.

Require Import Protocol.Io.

(*Require Arith.Compare_dec.
 *)

Require Import Lia.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.


Definition look_for_best_chain_for_block `{Io} (t:Time) (v:Voter) (ablock:AnyBlock)
  : AnyBlock
  :=
  let (block_number,block) := ablock
  in
  let available_blocks := block_producer t v
  in
    List.fold_left 
      (fun x y => if (x.(AnyBlock.block_number) <? y.(AnyBlock.block_number))%nat then y else x)
      (
        List.filter 
        (fun x => Block.is_prefix block  x.(AnyBlock.block)) 
        (Sets.to_list available_blocks)
      )
      (AnyBlock.to_any OriginBlock).


Definition build_and_send_prevote
  (t:Time)
  (state:State) 
  (voter:Voter) 
  (vs:VoterState)
  (b:AnyBlock)
  :State
  :=
      let new_message : Message.Message 
        :=
        {| 
          id:= Message.from_nat (1 + state.(message_count))
          ;Message.block:=b
          ;kind:=Message.PreVoteMessage
          ;round:=vs.(VoterState.round_number)
          ;Message.time:=t
          ;voter:=voter
          ;processed_by:=Sets.from_list (voter::List.nil)
        |}
      in
        let 
          up_prevote := VoterState.update_prevoted vs (Some b)
        in
        let up_round := VoterState.update_votes_with_msg up_prevote new_message
        in 
        advance_count
          (update_voter_state (update_message state new_message) voter up_round).

Definition build_and_send_precommit
  (t:Time)
  (state:State) 
  (voter:Voter) 
  (vs:VoterState)
  (b:AnyBlock)
  :State
  :=
      let new_message : Message.Message 
        :=
        {| 
          id:= Message.from_nat (S state.(message_count))
          ;Message.block:=b
          ;kind:=Message.PreCommitMessage
          ;round:=vs.(VoterState.round_number)
          ;Message.time:=t
          ;voter:=voter
          ;processed_by:=Sets.from_list (voter::List.nil)
        |}
      in
        let 
          up_precommit := VoterState.update_precommit vs (Some b)
        in
        let up_round := VoterState.update_votes_with_msg up_precommit new_message
        in 
        advance_count
          (update_voter_state (update_message state new_message) voter up_round).

Definition build_and_send_primary_estimate
  (t:Time)
  (state:State) 
  (voter:Voter) 
  (vs:VoterState)
  (b:AnyBlock)
  :State
  :=
      let new_message : Message.Message 
        :=
        {| 
          id:= Message.from_nat (S state.(message_count))
          ;Message.block:=b
          ;kind:=Message.EstimateMessage
          ;round:=vs.(VoterState.round_number)
          ;Message.time:=t
          ;voter:=voter
          ;processed_by:=Sets.from_list (voter::List.nil)
        |}
      in
      let updated_voter_state
        := 
        VoterState.update_last_block vs b
      in
        advance_count
          (update_voter_state 
            (update_message state new_message) 
            voter updated_voter_state
          ).

Definition build_and_send_finalized_block
  (t:Time)
  (state:State) 
  (voter:Voter) 
  (vs:VoterState)
  (b:AnyBlock)
  (votes:Message.FinalizeBlock)
  :State
  :=
      let new_message : Message.Message 
        :=
        {| 
          id:= Message.from_nat (S state.(message_count))
          ;Message.block:=b
          ;kind:=Message.FinalizationMessage votes
          ;round:=vs.(VoterState.round_number)
          ;Message.time:=t
          ;voter:=voter
          ;processed_by:=Sets.from_list (voter::List.nil)
        |}
      in
      let updated_voter_state
        := 
        VoterState.update_add_finalized_block vs b
      in
        advance_count
          (update_voter_state 
            (update_message state new_message) 
            voter updated_voter_state
          ).


Definition prevoter_step_aux `{Io} (t:Time) (state:State) (voter:Voter) (vs:VoterState)
  :State
  :=
  let tower := vs.(VoterState.rounds)
  in
  match Vectors.get tower (RoundNumber.to_nat vs.(VoterState.round_number)-1) with
  |Some (OpaqueRound.OpaqueRoundStateC previous_round)
    => 
    let ref_block := 
      match vs.(last_brodcasted_block) with
      | Some b => 
          match 
            (g (Round.get_all_prevote_votes previous_round)
              ,Estimate.get_estimate previous_round
            )
          with
          | (Some g_prev, Some estimate_prev)
              =>
              if 
                is_prefix estimate_prev.(AnyBlock.block) b.(AnyBlock.block) 
                && is_prefix b.(AnyBlock.block) g_prev.(AnyBlock.block)
              then Some b
              else Estimate.get_estimate previous_round
          | _ => Estimate.get_estimate previous_round
          end
      | None => Estimate.get_estimate previous_round
      end
    in 
    match map (look_for_best_chain_for_block t voter) ref_block with 
    | Some b => build_and_send_prevote t state voter vs b
    | None => state
    end
  | None => state
  end.

Definition prevoter_step_legit `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter) 
  (category:VoterCategory)
  (vs:VoterState)
  : State
  :=
  match vs.(prevoted_block) with 
  | Some _ => state 
  | None =>
    let tower := vs.(VoterState.rounds)
    in
    match Vectors.get tower (RoundNumber.to_nat vs.(VoterState.round_number)) with
    | Some (OpaqueRound.OpaqueRoundStateC round_) =>
      match Estimate.try_to_complete_round round_  with
      | Some _ => 
          prevoter_step_aux t state voter vs
      | None=>
          if t<=? Round.get_start_time round_ + (Time.from_nat 2)*global_time_constant 
          then 
            prevoter_step_aux t state voter vs
          else
            state
      end
    (*This shouldn't happen!*)
    | None => state
    end
  end.

Definition prevoter_step `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter) 
  (category:VoterCategory)
  (vs:VoterState)
  : State
  :=
  match category with 
  | VoterState.Bizantine 
    =>
    match io_bizantine_vote t voter with 
    | Some b => build_and_send_prevote t state voter vs b
    | None => state
    end
  | VoterState.Honest 
    => 
    prevoter_step_legit t state voter category vs
  end.

Definition precommit_step_legit `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter) 
  (category:VoterCategory)
  (vs:VoterState)
  : State
  :=
  let tower := vs.(VoterState.rounds)
  in
  match vs.(precommited_block) with 
  | Some _ => state
  | None =>
    match Vectors.get tower (RoundNumber.to_nat vs.(VoterState.round_number)) with
    | Some (OpaqueRound.OpaqueRoundStateC r) =>
      match Vectors.get tower (RoundNumber.to_nat vs.(VoterState.round_number) - 1) with
      | Some (OpaqueRound.OpaqueRoundStateC r_prev) =>
        match (g (Round.get_all_prevote_votes r), Estimate.get_estimate r_prev) with 
        | (Some g_r,Some estimate_prev)
          => 
          (* TODO: add third condition of precommit *)
          if (t <? Round.get_start_time r + (Time.from_nat 4)*global_time_constant)
            || Estimate.is_completable r 
          then
            build_and_send_precommit t state voter vs g_r 
          else 
            state 
        | _ => state
        end
      | None => state
      end
    (*This shouldn't happen!*)
    | None => state
    end
  end.

Definition precommit_step `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter) 
  (category:VoterCategory)
  (vs:VoterState)
  : State
  :=
  match category with 
  | VoterState.Bizantine 
    =>
    match io_bizantine_vote t voter with 
    | Some b => 
        build_and_send_precommit t state voter vs b
    | None => state
    end
  | VoterState.Honest 
    => 
    precommit_step_legit t state voter category vs
  end.

Definition get_last_finalized_block_number
  (finalized_blocks:Sets.DictionarySet AnyBlock)  
  : nat
  := 
  List.fold_left 
    (fun acc y => max acc y.(AnyBlock.block_number)) 
    (Sets.to_list finalized_blocks)
    0.

Definition should_finalize
  (finalized_blocks:Sets.DictionarySet AnyBlock)  
  (opaque:OpaqueRound.OpaqueRoundState) 
  : option AnyBlock
  :=
  let max_block_number := get_last_finalized_block_number finalized_blocks
  in
  match opaque with 
  | OpaqueRound.OpaqueRoundStateC r 
    =>
    match g (Round.get_all_precommit_votes r) with
    | None => None
    | Some b => 
      if negb 
        (Sets.or
          (fun b2 
            => 
            (b.(AnyBlock.block_number) <? max_block_number)%nat
            ||
            is_prefix b.(AnyBlock.block) b2.(AnyBlock.block)
          ) 
          finalized_blocks
        )
      then 
        Some b 
      else None
    end
  end.


Definition is_some {A} (o:option A) : bool
  := 
  match o with 
  | Some _ => true
  | _ => false
  end.

Definition get_voter_kind_for_round `{Io} (v:Voter) (round_number:RoundNumber)
  :option VoterKind
  :=
  Dictionary.lookup  v (io_get_round_voters round_number).

Definition get_voter_state (v:Voter) (state:State)
  :option VoterState
  :=
  Dictionary.lookup  v state.(voters_state) .

Definition is_voter_for_round `{Io} (v:Voter) (round_number:RoundNumber)
  : bool
  := 
  is_some (get_voter_kind_for_round v round_number).

Program Definition get_blocks_to_finalize `{Io} (voter:Voter) (vs:VoterState) 
  : list (OpaqueRound.OpaqueRoundState * AnyBlock)
  := 
  let finalizeds := vs.(VoterState.finalized_blocks)
  in
  let all_previous_rounds 
    : list OpaqueRound.OpaqueRoundState
    := 
    (
      VectorDef.to_list 
        (
          VectorDef.take 
            (RoundNumber.to_nat vs.(VoterState.round_number)-1) 
            _ 
            vs.(VoterState.rounds)
        )
    )
  in
  let predicate
    : OpaqueRound.OpaqueRoundState -> bool
    :=fun opaque => is_voter_for_round voter (OpaqueRound.get_round_number opaque)
  in
  let filtered_rounds 
    : list OpaqueRound.OpaqueRoundState
    := List.filter predicate all_previous_rounds
  in
  List.fold_left 
    (fun acc opaque => 
      match should_finalize finalizeds opaque  with 
      | Some b => (opaque,b)::acc 
      | None => acc end
    ) 
    filtered_rounds
    List.nil.
Next Obligation.
  transitivity (RoundNumber.to_nat (VoterState.round_number vs)).
  rewrite PeanoNat.Nat.sub_1_r.
  apply PeanoNat.Nat.le_pred_l.
  apply PeanoNat.Nat.le_succ_diag_r.
Qed.

Definition finalize_block (t:Time) 
  (voter:Voter) 
  (state:State) 
  (opaque_and_block:OpaqueRound.OpaqueRoundState * AnyBlock)
  : State
  :=
  match get_voter_state voter state with
  | Some vs 
    => 
    let (opaque,b) := opaque_and_block
    in
    let fin_msg
      :Message.FinalizeBlock
      :={|
        prevoters:= OpaqueRound.get_prevote_voters opaque
        ;precommiters:= OpaqueRound.get_precommit_voters opaque
        ;prevotes:= OpaqueRound.get_all_prevote_votes opaque
        ;precommits:= OpaqueRound.get_all_precommit_votes opaque
      |}
    in
    build_and_send_finalized_block t state voter vs b fin_msg
  | None => state
  end.
 

Definition finalization `{Io} (t:Time) (state:State) 
  (voter:Voter) (vs:VoterState) 
  :State 
  := 
  List.fold_left 
    (finalize_block t voter) 
    (get_blocks_to_finalize voter vs) 
    state.


Definition wait_step_for_new_round `{Io}
  (t:Time) 
  (voter:Voter) 
  (vs:VoterState)
  (state:State)
  : State
  :=
  let tower := vs.(VoterState.rounds)
  in
  match Vectors.get tower (RoundNumber.to_nat vs.(VoterState.round_number)) with
  |Some (OpaqueRound.OpaqueRoundStateC r)
    =>
    match Estimate.try_to_complete_round r with
    | Some _ => 
        let new_vs := 
          State.init_next_round_voter_state_from 
            (io_get_round_voters 
              (
                (RoundNumber.from_nat 1)
                + 
                vs.(VoterState.round_number)
              )
            ) 
            t 
            vs
        in
        let updated_state := update_voter_state state voter new_vs 
        in
        if voter_is_primary_for_round voter vs.(VoterState.round_number)
        then
          match Estimate.get_estimate r with 
          | Some b => build_and_send_primary_estimate t state voter vs b
          | None => updated_state
          end
        else
          updated_state
    | None => state
    end
  | None => state
  end.

Definition should_wait_for_next_round `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter)
  (vs:VoterState)
  : bool
  :=
  match get_voter_kind_for_round voter vs.(VoterState.round_number) with
  | Some (VoterKindC Bizantine _) => 
      io_bizantine_advance_round t voter vs.(VoterState.round_number)
  | Some (VoterKindC _ vote_right) 
      =>
      match vote_right with 
      | VotePrevote
          => is_some vs.(VoterState.prevoted_block)
      | VotePrecommit
          => is_some vs.(VoterState.precommited_block)
      | VoteBoth
          => is_some vs.(VoterState.prevoted_block)
              &&
              is_some vs.(VoterState.precommited_block)
      end
  | None => true
  end.

Definition voter_round_step_aux `{Io} (t:Time) (state:State) (voter:Voter): State :=
  match get_voter_state voter state with
  | Some voter_state_ =>  
      if should_wait_for_next_round t state voter voter_state_ 
      then wait_step_for_new_round t voter voter_state_ state
      else
        match 
          get_voter_kind_for_round voter voter_state_.(VoterState.round_number)
        with
        | Some(VoterKindC category kind_) => 
            match kind_ with
            | VotePrevote 
                => 
                prevoter_step t state voter category voter_state_
            | VotePrecommit 
                =>  
                precommit_step t state voter category voter_state_
            | VoteBoth => 
                match voter_state_.(VoterState.prevoted_block) with
                | Some _ => 
                  match voter_state_.(VoterState.precommited_block) with
                  (* this shouldn't happen! thanks to the first check *)
                  |Some _ => state
                  |None =>
                    precommit_step t state voter category voter_state_
                  end
                | None => 
                  prevoter_step t state voter category voter_state_
                end
            end
        | _ => state 
        end
  (*This shouldn't happen, we set all participants at the begining!*)
  | _ => state
  end.

Definition voter_round_step `{Io} (t:Time) (state:State) (voter:Voter): State :=
  match Dictionary.lookup voter state.(voters_state)with
  | Some vs =>  
    voter_round_step_aux 
      t 
      (finalization t state voter vs)
      voter
  | None => state
  end.

Definition voters_round_step `{Io} (t:Time) (state:State): State :=
  let voters := List.map fst (Dictionary.to_list state.(voters_state))
  in 
    List.fold_left (voter_round_step t) voters state .



CoInductive CoList (T:Type) :Type :=
  | CoCons : T -> CoList T -> CoList T.

Fixpoint get_last_nat_aux {T} (n:nat) (colist:CoList T): T
  := 
  match n with 
  | 0 => match colist  with 
         | CoCons _ element _ =>
             element
          end
  | S m => match colist with 
          | CoCons _ _ remain => get_last_nat_aux m remain
          end
  end.

Definition get_last {T} (t:Time) (colist:CoList T): T
  := get_last_nat_aux (Time.to_nat t) colist.


CoFixpoint produce_states `{Io} (t:Time) (state:State): CoList State :=
  let new_state := voters_round_step t (update_votes t state)
  in
  CoCons State new_state  (produce_states (Time.from_nat 1 +t) new_state).


Definition get_state_up_to `{Io} (t:Time): State :=   
  let 
    zero_round_dict := io_get_round_voters (RoundNumber.from_nat 0)
  in
  let 
    one_round_dict := io_get_round_voters (RoundNumber.from_nat 0)
  in
  get_last t 
  (
    produce_states 
      (Time.from_nat 0) 
      (State.make_initial_state_from zero_round_dict one_round_dict )
  ). 

(* Compute get_state_up_to 0. *)


Lemma get_global_finalized_blocks_are_related (state:State)
  (b1 b2 : AnyBlock) 
  (b1_in 
    : List.In b1 (List.map (FinalizedBlock.block) state.(global_finalized_blocks)))
  (b2_in 
    : List.In b2 (List.map (FinalizedBlock.block) state.(global_finalized_blocks)))
  : Related b1.(AnyBlock.block) b2.(AnyBlock.block).
Admitted.


(* for some reason /\ is disabled as notation *)

Section ProtocolConsistency.



Lemma voter_state_continuos_existence `{Io}
  (v:Voter)
  (t: Time)
  (r_n:nat)
  (
    is_some_at_t
    : exists vs1
      , Dictionary.lookup 
        v 
        (voters_state (get_state_up_to t)) = Some vs1
  )
  (t_increment:Time)
    : exists vs2
      , Dictionary.lookup 
        v 
        (voters_state (get_state_up_to (t_increment+t)%natWrapper )) = Some vs2.
Proof.
  Admitted.

Lemma round_continuos_existence `{Io}
  (v:Voter)
  (t: Time)
  (r_n:RoundNumber)
  (r1:OpaqueRound.OpaqueRoundState)
  (
    is_some_at_t
    : State.get_voter_opaque_round (get_state_up_to t) v r_n = Some r1
  )
  (t_increment:Time)
    : exists r2
    , State.get_voter_opaque_round (get_state_up_to (t_increment+t)) v r_n = Some r2.
Proof.
  Admitted.

Lemma round_prevoters_consistent_over_time `{Io}
  (v:Voter)
  (t:Time)
  (r_n:RoundNumber)
  (r1:OpaqueRound.OpaqueRoundState)
  (
    is_some_at_t
    :State.get_voter_opaque_round (get_state_up_to t) v r_n = Some r1
  )
  (t_increment:Time)
  :exists r2,
  State.get_voter_opaque_round 
    (get_state_up_to (t_increment+t))
    v 
    r_n 
    = Some r2 
  /\ (OpaqueRound.get_prevote_voters r2 = OpaqueRound.get_prevote_voters r1).
Proof.
  destruct (round_continuos_existence v t r_n r1 is_some_at_t t_increment)
    as [r2 is_some].
  exists r2.
  split.
  apply is_some.
  induction t_increment.
  Admitted.
  (*
  - simpl in is_some.
    rewrite is_some in is_some_at_t.
    injection is_some_at_t.
    intro eq_r.
    rewrite  eq_r.
    reflexivity.
  - Admitted.
  *)

Lemma round_precommiters_consistent_over_time `{Io}
  (v:Voter)
  (t:Time)
  (r_n:RoundNumber)
  (r1:OpaqueRound.OpaqueRoundState)
  (
    is_some_at_t
    :State.get_voter_opaque_round (get_state_up_to t) v r_n = Some r1
  )
  (t_increment:Time)
  :exists r2,
  State.get_voter_opaque_round 
    (get_state_up_to (t_increment+t))
    v 
    r_n 
    = Some r2 
  /\ (OpaqueRound.get_precommit_voters r2 = OpaqueRound.get_precommit_voters r1).
Admitted.

Lemma round_precomits_consistent_over_time `{Io}
  (v:Voter)
  (t:Time)
  (r_n:RoundNumber)
  (r1:OpaqueRound.OpaqueRoundState)
  (
    is_some_at_t
    :State.get_voter_opaque_round (get_state_up_to t) v r_n = Some r1
  )
  (t_increment:Time)
  (r2:OpaqueRound.OpaqueRoundState)
  (is_some_at_t_increment: 
    State.get_voter_opaque_round 
      (get_state_up_to (t_increment+t))
      v 
      r_n 
      = Some r2
  )
  (voters_are_equal: (OpaqueRound.get_precommit_voters r1) = (OpaqueRound.get_precommit_voters r2))
  : (Votes.castVotes voters_are_equal (OpaqueRound.get_all_precommit_votes r1) = OpaqueRound.get_all_precommit_votes r2).
Admitted.

Lemma finalized_blocks_monotone_over_time `{Io}
  (t:Time)
  (t_increment:Time)
  : exists  l, 
  (global_finalized_blocks (get_state_up_to (t_increment + t)))
  =
  l ++ (global_finalized_blocks (get_state_up_to t)).
Proof.
  Admitted.

Lemma finalized_blocks_monotone_over_time2 `{Io}
  (t:Time)
  (t_increment:Time)
  : forall b, List.In b (global_finalized_blocks (get_state_up_to t))
  ->
  List.In b (global_finalized_blocks (get_state_up_to (t_increment + t))).
Proof.
  Admitted.

(*
Lemma votes_are_monotone_over_time `{Io}
  (v:Voter)
  (t1 t2:Time)
  (r_n:nat)
  (related_t:t1 <= t2)
  (state_is_from_protocol: get_state_up_to t)
  (b_in
    :List.In 
      (to_any b) 
      (List.map ( fun x => fst (fst x)) (global_finalized_blocks state))
  )
  .
*)

Lemma finalized_block_time_leq
  (t:Time)
  (fb: FinalizedBlock.FinalizedBlock)
  `{Io}
  (b_in
    :List.In 
      fb
      (global_finalized_blocks (get_state_up_to t))
  )
  : fb.(FinalizedBlock.time) <= t.
Admitted.

Lemma finalized_block_came_from_voter
  (t:Time)
  (fb: FinalizedBlock.FinalizedBlock)
  `{Io}
  (b_in
    :List.In 
      fb
      (global_finalized_blocks (get_state_up_to t))
  )
  :exists (r:OpaqueRound.OpaqueRoundState)
    , State.get_voter_opaque_round (get_state_up_to fb.(FinalizedBlock.time)) fb.(FinalizedBlock.submitter_voter) fb.(FinalizedBlock.round_number)
      = Some r
    /\ 
      g 
        (OpaqueRound.get_all_precommit_votes 
          r
        ) = Some fb.(FinalizedBlock.block) .
Proof.
  Admitted.


(*TODO: add consistency of total_number_of_voters param
  that is passed to both prevote and precommit set of voters for every round
*)
  
End ProtocolConsistency.


Definition VoterVotedInRound (v:Voter) (opaque:OpaqueRound.OpaqueRoundState)
  :Prop
  :=
    (Votes.voter_voted_in_votes v (OpaqueRound.get_all_prevote_votes opaque) = true)
    \/
    (Votes.voter_voted_in_votes v (OpaqueRound.get_all_precommit_votes opaque) = true).

Lemma theorem_4_1_eq_aux `{Io} 
  (t:Time)
  (fb: FinalizedBlock)
  (b1_in:List.In fb (global_finalized_blocks (get_state_up_to t)))
  : exists (v:Voter) (vr:OpaqueRound.OpaqueRoundState) (vr2:OpaqueRound.OpaqueRoundState)
  ,
    (
      State.get_voter_opaque_round (get_state_up_to fb.(FinalizedBlock.time) ) v fb.(FinalizedBlock.round_number)
      =
      Some vr
    )
    /\
    (g (OpaqueRound.get_all_precommit_votes vr) = Some fb.(FinalizedBlock.block))
    /\
    (
      State.get_voter_opaque_round (get_state_up_to (t+(Time.from_nat 2)*global_time_constant)) v fb.(FinalizedBlock.round_number)
      = 
      Some vr2
    ).
Proof.
  Admitted.
  (*
  pose (finalized_block_time_leq b1 round_finalized t1 t b1_in) as t1_leq_t.
  remember (t+(Time.from_nat 2)*global_time_constant) as new_t eqn:new_t_eq.
  assert (List.In (to_any b1,t1, round_finalized) (global_finalized_blocks (get_state_up_to new_t))) as b1_in_new_t.
  {
    pose (finalized_blocks_monotone_over_time2 t (new_t - t) (to_any b1, t1,round_finalized) b1_in).
    enough ((new_t - t +t) = new_t) as H0.
    rewrite <- H0.
    assumption.
    admit.
    (* lia. *)
    }
  destruct (finalized_block_came_from_voter b1 round_finalized t1 new_t  b1_in_new_t) as [v [vr [is_some_vr g_vr]]].
  exists v.
  pose (round_continuos_existence v t1 round_finalized vr is_some_vr (new_t - t1)) as vr_exists_at_new_t.
  assert (new_t - t1 +t1 = new_t) as is_new_t. admit. (* lia. *) 
  Admitted.
  *)
  (*
  rewrite is_new_t in vr_exists_at_new_t.
  simpl in vr_exists_at_new_t.
  destruct vr_exists_at_new_t as [vr2 is_some_vr2].
  exists vr.
  exists vr2.
  auto.
Qed.
   *)


Lemma theorem_4_1_eq `{Io} 
  (t:Time)
  (fb1 fb2 : FinalizedBlock)
  (un_related:Unrelated fb1.(FinalizedBlock.block).(AnyBlock.block) fb2.(FinalizedBlock.block).(AnyBlock.block))
  (fb1_in:List.In fb1 (global_finalized_blocks (get_state_up_to t)))
  (fb2_in:List.In fb2 (global_finalized_blocks (get_state_up_to t)))
  (finalized_same_round : fb1.(FinalizedBlock.round_number) = fb2.(FinalizedBlock.round_number))
  : exists (t3:Time) (v:Voter) (r:OpaqueRound.OpaqueRoundState) (s:Sets.DictionarySet Voter), 
    (
      (
        State.get_voter_opaque_round (get_state_up_to t3) v fb1.(FinalizedBlock.round_number) = Some r
      )
      /\
      (
        List.length (Sets.to_list s) 
        >= 
        1+ Voters.calculate_max_bizantiners (OpaqueRound.get_prevote_voters r)
      )%nat 
      /\
      (forall v2, List.In v2 (Sets.to_list s) -> VoterVotedInRound v2 r)
      /\ 
      (forall v3, List.In v3 (Sets.to_list s) -> List.In v3 (get_round_bizantine_voters fb1.(FinalizedBlock.round_number) ))
    ).
Proof.
  (*
  remember (t + (Time.from_nat 2) * global_time_constant) as new_t eqn:new_t_eq.
  exists new_t.
  destruct (theorem_4_1_eq_aux b1 round_finalized t1 t b1_in) as [v [v1r [v1r2 [is_some_v1r [g_v1r is_some_v1r2]]]]].
  exists v.
  exists v1r2.
  remember (List.filter (fun v3 => Votes.voter_voted_in_votes v3 (OpaqueRound.get_all_precommit_votes v1r2)) (get_round_bizantine_voters round_finalized)) as s_as_list eqn:s_as_list_eq.
  remember (Sets.from_list s_as_list) as s.
  exists s.
  rewrite <- new_t_eq in is_some_v1r2.
  split.
  assumption.
  split.
  - destruct (theorem_4_1_eq_aux b2 round_finalized t2 t b2_in) as [v2 [v2r [v2r2 [is_some_v2r [g_v2r is_some_v2r2]]]]].
  *)
    (*
       TODO in 3.8 : 
       we need to show that after t+2*global_time_constant v has got all the votes on v2r, and as such we have 
       a supermajority for both blocks in this round (b1 and b2) at this time. 
       Then we destruct the Votes.is_safe predicate applied in the precommits at time t + 2*global_time_constant 
       In the False case, we end this sub-proof.
       In the True case, b_1 and b_2 are related by a lemma in the Votes.v about supermajority on safe sets, contra with un_related
    *)
  (*
    The other two parts to be proved, are a consequency of the construction of the list (literally they are in the predicate that build the list).
   *)
    Admitted.
  


Lemma theorem_4_1_lt `{Io} 
  (t:Time)
  (fb1 fb2 : FinalizedBlock)
  (un_related:Unrelated fb1.(FinalizedBlock.block).(AnyBlock.block) fb2.(FinalizedBlock.block).(AnyBlock.block))
  (fb1_in:List.In fb1 (global_finalized_blocks (get_state_up_to t)))
  (fb2_in:List.In fb2 (global_finalized_blocks (get_state_up_to t)))
  (symmetry_hipotesis: fb1.(FinalizedBlock.round_number) < fb2.(FinalizedBlock.round_number))
  : exists (t3:Time) (v:Voter) (r_n:RoundNumber) (r:OpaqueRound.OpaqueRoundState) (s:Sets.DictionarySet Voter), 
    (
      (
        State.get_voter_opaque_round (get_state_up_to t3) v r_n = Some r
      )
      /\
      (
        List.length (Sets.to_list s) 
        >= 
        1+ Voters.calculate_max_bizantiners (OpaqueRound.get_prevote_voters r)
      )%nat 
      /\
      (forall v2, List.In v2 (Sets.to_list s) -> VoterVotedInRound v2 r)
      /\ 
      (forall v3, List.In v3 (Sets.to_list s) -> List.In v3 (get_round_bizantine_voters r_n))
    ).
Proof.
  (*
  dependent induction b1. 
  - pose (originBlock_is_always_prefix b2) as contra.
    apply (prefix_implies_related _ _) in contra.
    contradiction.
  - dependent destruction b2.
    +  pose (originBlock_is_always_prefix (NewBlock b1 id)) as contra.  
       apply (prefix_implies_related _ _) in contra.
       apply related_symmetric in contra.
       contradiction.
    +
      (*TODO in 3.8 *)
  *)
Admitted.


Theorem theorem_4_1 `{Io} 
  (t:Time)
  (fb1 fb2 : FinalizedBlock)
  (un_related:Unrelated fb1.(FinalizedBlock.block).(AnyBlock.block) fb2.(FinalizedBlock.block).(AnyBlock.block))
  (fb1_in:List.In fb1 (global_finalized_blocks (get_state_up_to t)))
  (fb2_in:List.In fb2 (global_finalized_blocks (get_state_up_to t)))
  : exists (t3:Time) (v:Voter) (r_n:RoundNumber) (r:OpaqueRound.OpaqueRoundState) (s:Sets.DictionarySet Voter), 
    (
      (
        State.get_voter_opaque_round (get_state_up_to t3) v r_n = Some r
      )
      /\
      (
        List.length (Sets.to_list s) 
        >= 
        1+ Voters.calculate_max_bizantiners (OpaqueRound.get_prevote_voters r)
      )%nat
      /\
      (forall v2, List.In v2 (Sets.to_list s) -> VoterVotedInRound v2 r)
      /\ 
      (forall v3, List.In v3 (Sets.to_list s) -> List.In v3 (get_round_bizantine_voters r_n))
    ).
Proof.
  Admitted.

    (*
  pose (Arith.Compare_dec.lt_eq_lt_dec (RoundNumber.to_nat round_finalized_1) (RoundNumber.to_nat round_finalized_2) ) as trico.
  destruct trico as [[trico4 | trico2]| trico3].
  - apply (theorem_4_1_lt b1 b2 round_finalized_1 round_finalized_2 t1 t2 un_related state t state_is_from_protocol b1_in b2_in);try assumption.  
  - rewrite state_is_from_protocol in b1_in.
    rewrite state_is_from_protocol in b2_in.
    Admitted.
    rewrite <- trico2 in b2_in.
    destruct (theorem_4_1_eq b1 b2 round_finalized_1 t1 t2 un_related  t b1_in b2_in) as [t3 [v3 [r [s remain]]]].
    exists t3.
    exists v3.
    exists round_finalized_1. 
    exists r.
    exists s.
    assumption.
  - pose (Blocks.unrelated_symmetric b1 b2 un_related) as un_related2.
    apply (theorem_4_1_lt b2 b1 round_finalized_2 round_finalized_1 t2 t1 un_related2 state t state_is_from_protocol b2_in b1_in);try assumption.  
Qed.
     *)

Definition voter_is_hones_at_round `{Io} (v:Voter) (r:RoundNumber) : bool
  := 
  (0 <? count v (get_round_honest_voters r))%nat.


Corollary corollary_4_3 
  `{Io}
  (round_finalized_number:RoundNumber)
  (time_finalied:Time)
  (b_finalized:AnyBlock)
  (v:Voter)
  (r_n:RoundNumber)
  (is_honest: voter_is_hones_at_round v r_n = true)
  (t_increment:Time)
  (r_n_geq: r_n >= round_finalized_number)
  (opaque_r_n : OpaqueRound.OpaqueRoundState)
  (opaque_from_state
    : 
    State.get_voter_opaque_round (get_state_up_to (t_increment + time_finalied) ) v r_n 
    = Some opaque_r_n
  )
  (r_n_completable:
   OpaqueRound.is_completable opaque_r_n = true
  )
  :exists (eb:AnyBlock),
    (
      OpaqueRound.get_estimate opaque_r_n
      = 
      Some eb 
    )
    /\ 
    (
      Block.is_prefix b_finalized.(AnyBlock.block) eb.(AnyBlock.block) = true
    ).
Proof.
  (*TODO: delayed until 3.8
   *)
  Admitted.

