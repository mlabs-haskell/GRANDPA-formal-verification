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
Admitted.

Definition is_completable 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : bool
  :=
  match try_to_complete_round round_state with
  | None => false
  | _ => true
  end.


Definition Source (X:Type) := forall (t:Time) (new_round_number:nat) round_number , round_number < new_round_number -> X.

Definition parameterize {X:Type} {F:Type->Type} (P: X -> F X ) (source:  Source X)
  : Source (F X)
  := 
  fun (t : Time) (new_round_number : nat) (n : nat) (pf : n < new_round_number) =>
    P (source t new_round_number n pf).

Definition parameterizeDependent {X:Type} {F:X->Type} (P: forall x, F x ) (source:  Source X)
  : forall t nr n pf , (F (source t nr n pf))
  := 
  fun (t : Time) (new_round_number : nat) (n : nat) (pf : n < new_round_number) =>
    P (source t new_round_number n pf).

Print parameterize .

End State3.

Definition parameterize_bizantine := parameterize (F:=fun _ => nat) (fun _ => 1) (fun t => fun nr => fun n => fun pr => n).

Definition parameterize_block_number := parameterize (F:=fun _ => nat) (fun _ => 1) (fun t => fun nr => fun n => fun pr => n).

Definition parameterize_block (p_block_nummber:Source nat) := parameterizeDependent Block p_block_nummber.

Print parameterize_block.

Definition p_voter (s:Source nat) := parameterize (F:=fun x => x) (fun x => x) s.

Definition p_Voters (s_bizantine:Source nat)  := parameterizeDependent Voters s_bizantine.
 
Definition ProtocolView (t:Time) (voter:Voter) (current_round:nat) :
  preview_number_s : forall t -> preview_number_s.
  RoundState (preview_voters: p_Voters ) .



Definition p2 := parameterize (fun _ => (fun  _ => nat)).

Definition p_last_block_number := parameterize (fun _ => (fun  _ => nat )).
Definition p_last_block (m_last_block_number:p_last_block_number) : parameterize () := (fun t => (fun  n => fun proof => Block (m_last_block_number t n proof) )).
Definition parameterize_voters := parameterize (fun _ => (fun  _ => Voters ))


Check ( (fun t => fun n => fun z => fun _ => Some (t+n+z)) :p2).

Check ((fun t => fun n => fun z => fun _ => (t+n+z)) : parameterize_bizantine ).

Definition can_start_round (old_round_number:nat) (round_source: parameterize (fun )) 

Definition parameterized_voters := forall .

Definition get_previous_rounds (t:Time) (new_round_number: nat) : forall n , n < new_round_number -> option
  ({t_init & { round_last_block & RoundState preview_votes precommit_votes t_init round_number ).
