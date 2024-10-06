------------------------------ MODULE BitSnark ------------------------------
(***************************************************************************)
(* This module specifies the transaction flow in the BitSNARK protocol.    *)
(***************************************************************************)

EXTENDS Naturals

CONSTANTS
    (* The size of the verification program. *)
    PROGRAM_SIZE,
    (* Size of the prover stake. *)
    PROVER_STAKE,
    (* Size of the verifier payment. *)
    VERIFIER_PAYMENT

StartingBalances == [prover |-> PROVER_STAKE, verifier |-> VERIFIER_PAYMENT, locked |-> 0]

AllowedTransactions == {
    "Proof", "Uncontested Proof", "Challenge", "Uncontested Challenge",
    "State", "Uncontested State", "Select", "Uncontested Select",
    "Argument", "Uncontested Argument", "Proof Refuted"}
    
IsProofValid == CHOOSE v \in {TRUE, FALSE} : TRUE

VARIABLES
    (* The number of contentioned instructions. *)
    contentioned,
    (* Balances of the protocol - "prover", "verifier" and "locked". *)
    balances,
    (* The set of all currently spendable transactions. *)
    blockchain
 
Init ==
    /\ contentioned = PROGRAM_SIZE  
    /\ balances = StartingBalances
    /\ blockchain = {}

(* Transaction Functions - the Flow of States. *)

Proof ==
    /\ blockchain = {}
    /\ balances' = [balances EXCEPT
        !["prover"] = @ - PROVER_STAKE,
        !["locked"] = @ + PROVER_STAKE]
    /\ blockchain' = blockchain \union {"Proof"}
    /\ UNCHANGED contentioned
    
UncontestedProof ==
    /\ "Proof" \in blockchain
    /\ {"Challenge"} \intersect blockchain = {}
    /\ balances' = [balances EXCEPT
        !["locked"] = @ - PROVER_STAKE,
        !["prover"] = @ + PROVER_STAKE]
    /\ blockchain' = (blockchain \ {"Proof"}) \union {"Uncontested Proof"}
    /\ UNCHANGED contentioned

Challenge ==
    /\ "Proof" \in blockchain
    /\ {"Challenge"} \intersect blockchain = {}
    /\ balances' = [balances EXCEPT
        !["verifier"] = @ - VERIFIER_PAYMENT,
        !["prover"] = @ + VERIFIER_PAYMENT]
    /\ blockchain' = blockchain \union {"Challenge"}
    /\ UNCHANGED contentioned

UncontestedChallenge ==
    /\ "Proof" \in blockchain
    /\ "Challenge" \in blockchain
    /\ {"State", "Uncontested Challenge"} \intersect blockchain = {}
    /\ balances' = [balances EXCEPT
        !["locked"] = @ - PROVER_STAKE,
        !["verifier"] = @ + PROVER_STAKE]
    /\ blockchain' = (blockchain \ {"Proof"})
    /\ UNCHANGED contentioned

State ==
    /\ "Proof" \in blockchain
    (* A smart prover will test that there actually is a challenge on the blockchain, but smart provers aren't a part of the spec. *)
    /\ blockchain' = (blockchain \ {"Proof"}) \union {"State"}
    /\ UNCHANGED contentioned
    /\ UNCHANGED balances

UncontestedState ==
    /\ "State" \in blockchain
    /\ balances' = [balances EXCEPT
        !["locked"] = @ - PROVER_STAKE,
        !["prover"] = @ + PROVER_STAKE]
    /\ blockchain' = (blockchain \ {"State"}) \union {"Uncontested State"}
    /\ UNCHANGED contentioned

Select ==
    /\ "State" \in blockchain
    /\ blockchain' = (blockchain \ {"State"}) \union {"Select"}
    /\ UNCHANGED contentioned
    /\ UNCHANGED balances

UncontestedSelect ==
    /\ "Select" \in blockchain
    /\ balances' = [balances EXCEPT
        !["locked"] = @ - PROVER_STAKE,
        !["verifier"] = @ + PROVER_STAKE]
    /\ blockchain' = (blockchain \ {"Select"}) \union {"Uncontested Select"}
    /\ UNCHANGED contentioned

Argument ==
    /\ "Select" \in blockchain
    /\ blockchain' = (blockchain \ {"Select"}) \union {"Argument"}
    /\ UNCHANGED contentioned
    /\ UNCHANGED balances

UncontestedArgument ==
    /\ "Argument" \in blockchain
    /\ balances' = [balances EXCEPT
        !["locked"] = @ - PROVER_STAKE,
        !["prover"] = @ + PROVER_STAKE]
    /\ blockchain' = (blockchain \ {"Argument"}) \union {"Uncontested Argument"}
    /\ UNCHANGED contentioned

ProofRefuted ==
    /\ "Argument" \in blockchain
    /\ balances' = [balances EXCEPT
        !["locked"] = @ - PROVER_STAKE,
        !["verifier"] = @ + PROVER_STAKE]
    /\ blockchain' = (blockchain \ {"Argument"}) \union {"Proof Refuted"}
    /\ UNCHANGED contentioned

Next ==
  \/ Proof
  \/ UncontestedProof
  \/ Challenge
  \/ UncontestedChallenge
  \/ State
  \/ UncontestedState
  \/ Select
  \/ UncontestedSelect
  \/ Argument
  \/ UncontestedArgument
  \/ ProofRefuted


(* Safety Properties. *)

TypeOK ==
    /\ blockchain \subseteq AllowedTransactions
    /\ DOMAIN balances = {"prover", "verifier", "locked"}

Sum(bs) == bs["prover"] + bs["verifier"] + bs["locked"]
ValueOK == Sum(balances) = Sum(StartingBalances)

IncentiveOK ==
    /\ "Proof Refuted" \in blockchain =>
       balances["verifier"] >= StartingBalances["verifier"]
    /\ "Uncontested Argument" \in blockchain =>
       balances["prover"] >= StartingBalances["prover"]

AllOK ==
    /\ TypeOK
    /\ ValueOK
    /\ IncentiveOK



 ============================================================================
