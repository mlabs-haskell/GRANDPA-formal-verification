Require Import DataTypes.Dictionary.
Require Import Message.
Require Import Votes.
Require Import VoterState.
Require Import Time.
Require Import RoundNumber.
Require Import Protocol.FinalizedBlock.

Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Classes.Math.All.
Require Import State.
Require Import Io.

Open Scope natWrapper.
Open Scope bool.
Open Scope eqb.
Open Scope math.

Definition set_message_as_processed_by (v:Voter) (msg:Message) (state:State): State :=
  State.update_message state (Message.update_message_proccessed msg v).

Definition is_message_processed_by(state:State) (msg:Message) (v:Voter) : bool:= 
  match Dictionary.lookup msg.(id) state.(pending_messages) with
  | Some _ => true
  | None => false
  end.

Definition accept_vote (state:State) (voter:Voter) (msg:Message): State :=
  match Dictionary.lookup voter state.(voters_state)with
  | Some voter_state_ => 
    update_voter_state 
    state 
    voter 
    (VoterState.update_with_msg voter_state_ msg)
  (* None means that a message for participant outside of the simulation is tried *)
  (* we expect this to never happend*)
  | _ => state
  end.

Definition update_vote_for_voter `{Io} (t:Time) (voter:Voter) (state:State) (msg:Message) : State :=
  if is_message_processed_by state msg voter then  
    state 
  else 
    if io_accept_vote t msg  voter
    then
      accept_vote state voter msg
    else
        if (t <=? (msg.(Message.time)+ global_time_constant)%math ) || (voter =? msg.(Message.voter))
        then accept_vote state voter msg else state.

Definition upate_votes_for_voter `{Io} (t:Time) (state:State) (voter:Voter) : State :=
  let messages := List.map snd (Dictionary.to_list (pending_messages state))
  in
  let f := update_vote_for_voter t voter 
  in
    List.fold_left f messages state.


(*
TODO: Critial, this must check for all the voters that participate ever! not only the round ones!
Or not?
*)
Definition prune_message `{Io} (state:State) (msg:Message) : State := 
  let round_participants := io_get_round_voters (Message.round msg)
  in
  if 
      List.fold_left 
        (fun acc v => andb acc (is_message_processed_by state msg v) ) 
        (List.map fst (Dictionary.to_list round_participants))
        true
  then
    remove_message state msg 
  else 
    state .

Definition prune_messages `{Io} (state:State): State:=
  List.fold_left prune_message (List.map snd (Dictionary.to_list state.(pending_messages)) ) state.

Definition update_votes `{Io} (t:Time) (state:State) : State:=
  let state_votes_updated
    := 
    List.fold_left 
      (upate_votes_for_voter t ) 
      (List.map fst (Dictionary.to_list state.(voters_state)))
      state 
  in
  prune_messages state_votes_updated.

Close Scope math.
Close Scope eqb.
Close Scope bool.
Close Scope natWrapper.
