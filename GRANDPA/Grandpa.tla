------------------------------ MODULE Grandpa ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT N, T, V\* N is the number of voters, T is the 
ASSUME N \in Nat

  
(*--algorithm GrandpaProtocol
(* Delcaration of global variables *)
variables 
    LastFinalizedBlock \in Blocks, 
    BestFinalCandidate \in Blocks, 
    GrandpaGhost \in Blocks, 
    r \in Int,
    LastCompletedRound \in Int;
(* Operator definitions *)
VoteID == {1..N}
VoterType == {"normal", "byzantine"}
Voter == [Vid : VoterID, Vtype : VoterType]
VoterList == [
(* macro definitions *)
macro Mod(x, y) \* Define a macro for modular operation
  /\ y # 0 \* Ensure y is not zero
  /\ x >= 0 \* Ensure x is a natural number
  /\ result := x % y
end define;
(* procedures *)
procedure InitiateGradpa (r0, B0 ) 
{
Init:
        LastFinaizedBlock := B0
        BestFinalCandidate := B0
        GrandpaGhost := B0
        r := r0
        PlayGrandpaRound(r)
 }
(* algorithm body or process declaration *)

  
    
begin

end algorithm; *)
=============================================================================
\* Modification History
\* Last modified Mon Jan 15 11:24:38 IST 2024 by sparsa
\* Created Sun Jan 14 13:55:38 IST 2024 by sparsa
