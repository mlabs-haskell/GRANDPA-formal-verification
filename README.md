# Formal Guarantees for GRANDPA Finality Gadget

Consensus layers are the backbones of blockchains. Any vulnerability in the consensus mechanism can have far-reaching consequences on the integrity and security of the whole system. Polkadot’s Relay Chain uses  [GRANDPA](https://research.web3.foundation/en/latest/polkadot/finality.html)  (a deterministic finality gadget) to achieve consensus in the network.

This project aims to provide formal guarantees of GRANDPA’s correctness and security by modelling the consensus mechanism and verifying it against formal specifications.

## The proof approach

When mathematicians write proofs with 'pen and paper', they need to review them by themselves multiple times before they share them with the mathematical community. Even then they need to pass the scrutiny of multiple pairs before the proofs can be accepted. Although this process exists and is followed rigorously, mistakes can happen, and invalid results can reach the public, in those cases, mathematicians usually offer new proofs of statements and in very rare cases they retract the results.

Proof assistants are more rigorous than people in the sense that unless we explicitly request for exculpation of proof, the proof assistant would reject to accept a non-rigorous proof.

  

## 1.2 Details

The proof assistants have the weakness that the validity of the proof is tied to various assumptions:

-   The implementation of the 'minimal kernel' of the proof assistants is done right.
    
-   The language of implementation and its compiler/interpreter are right.
    
-   The previous tools used to create the compiler/interpreter do a correct translation of them.
    

In that direction, we can go back in time across multiple languages and compilers/interpreters, but even summing that all of them are correctly implemented, we also need to ensure that:

-   The machine that is running is in good condition and results are reproducible In this aspect, we can go as far as to ensure that the machine can’t be a victim of cosmic rays or other rare cases that can cause the hardware fault.
    

It is for this reason that although the '4 colors theorem' has been proven with the help of COQ, there is a controversy in the mathematical/logic community about its validity as a formal proof. With this in mind, we propose an approach to the proofs that we hope can minimize the risks of faults by the mix of both the human procedure and the machine verification.

The method consists of writing down two kinds of proofs, one the traditional 'pen and paper' proof, and the other implemented in the proof assistant. The idea is to do first the pen and paper proof and then iterate over the proof attempts in the proof assistant to refine the 'pen and paper' proof until we can convince the proof assistant that our proof is right. This way, we would end with two proofs that are closely related and verified by both humans and computers.

An example of the successful application of a similar approach can be found in the paper [https://www.tandfonline.com/doi/full/10.1080/11663081.2019.1647653](https://www.tandfonline.com/doi/full/10.1080/11663081.2019.1647653)

As a consequence of this method, we can end with a large portion of 'technical lemmas', those are statements that aren’t needed for us humans but that the proof assistant needs, or otherwise it would reject the proof. This is an inevitable result to the best of our knowledge, and the growth of those 'technical lemmas' can be exponential over time.

For this reason, we present a plan of work in which we try to discover as many of the required 'technical lemmas' as possible in the shortest amount of time possible. This way, after the discovery of the 'technical lemmas', we can review the plan and adjust it. A possible outcome of this is that we may discover that the approach of formal verification of the GRANDPA protocol can’t be made in a reasonable time or an established budget. The early discovery of 'technical lemmas' would allow us to stop the work before spending too many resources.

We can split the plan into three main sections:

-   Preamble, which corresponds to sections 2 and 3 of the GRANDPA paper.
    
-   Safety, corresponds to section 4.1.
    
-   Liveness, corresponds to section 4.2.
    

Every section can also be divided into:

-   Search for required abstractions
    
-   Modification of proofs and discovery of 'technical lemmas'
    
-   Writing of the statements in the proof assistant without proofs
    
-   Proofs of the statements However, the 'Search of required abstractions' would happen mainly in the 'Preamble section'. A detailed list of the required steps for every section is presented below.
    

### Preamble

1.  Sketch proofs of section 2 lemmas
    
2.  Split of section 2 proofs in more elemental lemmas
    
3.  Formal proofs of the lemmas and formal definition of the g function outside the proof assistant
    
4.  Proofs refactorization in a way that can be followed in COQ code
    
5.  List all the required structures to define the g function and to express the GRANDPA algorithm
    
6.  Split the list of required structures in implementable ones and those with only interfaces
    
7.  Write the interface of all the structures in the list
    
8.  Write the statements of all the lemmas and the principal conclusions
    
9.  Implementation of the g function using only the interfaces
    
10.  Implementation of the GRANDPA protocol using only the interfaces
    
11.  Proofs of section 2 lemmas
    

### Safety

12.  Refactor of proof sketches in section 4.1 using the developed abstractions.
    
13.  Split the proofs of section 4.1 in more elemental lemmas.
    
14.  Formal proofs of section 4.1 lemmas.
    
15.  Refine proofs to make them as close to COQ reasoning as possible.
    
16.  Write the statements to be proved in COQ.
    
17.  Proof of the lemma 4.2
    
18.  Proof of Theorem 4.1
    
19.  Proof of Corollary 4.3
    
20.  Proof of intermediate lemmas.
    

### Liveness

21.  Refactor of proof sketches of section 4.2
    
22.  Split of proofs of section 4.2 in more elemental lemmas.
    
23.  Formal proofs of section 4.2 lemmas.
    
24.  Refine proofs to make them as close to COQ reasoning as possible.
    
25.  Write statements to be proved in COQ.
    
26.  Proof of lemma 4.4.
    
27.  Proof of lemma 4.5.
    
28.  Proof of lemma 4.6.
    
29.  Proof of lemma 4.7.
    
30.  Proof of lemma 4.8.
    
31.  Proof of lemma 4.9.
    
32.  Proof of intermediate lemmas.


## Build

For commodity there is a `nix.flake` file defined. 
After `nix develop` you can just run `make` inside the `Grandpa` folder.
