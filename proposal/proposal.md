% Formally Verifying the Stellar Consensus Protocol
% Eli Gafni and Giuliano Losa

# Introduction

Stellar is new implementation of an open distributed ledger based on trust.
Open-membership distributed ledgers will likely become critical global infrastructure for payments, notary services, identity and trust management, etc. with bugs in their design or implementation having potentially catastrophic consequences. Testing these protocols is ineffective or too expensive since bugs occur only under malicious attack or in global-scale deployments. Therefore distributed ledgers should be held to the highest standards of correctness, namely formal verification. 

Full end-to-end verification of an open distributed ledger is beyond the reach of established verification methods, which are too labor-intensive to scale to the complexity of distributed ledgers. One reason is that the automatic solvers used to relieve the user from tedious manual proofs fail unpredictably or for reasons obscure to the user.

We have recently made a leap forward, reducing the verification effort needed to verify Paxos-style algorithms by an order of magnitude using the novel concept of decidable verification. Alas, Paxos cannot scale to a global infrastructure. Open ledgers that scale to global size are built on the same principles but are significantly more intricate than Paxos.

The basis of this proposal is the hope that, like the Paxos family, the new algorithms for global-scale open ledgers will lend themselves to decidable verification. Informally, we were successful with the Paxos family because those algorithms, even though quite difference in features, rely on the same core invariants, whose correctness is expressible in a decidable logic. We expect SCP to satisfy similar invariants; hence our hope.

<!--on it being optimizations of an underlying Commit-Adopt version. Not surprisingly the Stellar ballot protocol is based on neutralizable statements which is essentially a Commit-Adopt. Hence our hope.-->

## Preliminary Results in Developing the Tools to be Used

Using decidable verification, we have verified the safety of protocols such as Multi-Paxos, Vertical Paxos, Stoppable Paxos, and Raft, Byzantine Paxos, as well as some aspects of Ethereum’s Casper Proof-of-Stake protocol. Remarkably, each proof consists of at most a few dozen lines [@PadonPaxosMadeEPR2017].
This is in stark contrast with previous work: Lamport’s machine-checked proof in TLA+ of Byzantine Paxos [@lamport_byzantizing_2011] is about 3000 lines long. Yoichi Ira’s original proof [] of the same property of the Casper protocol is 50 times larger than ours [].

We have also recently used decidable verification to verify the safety of implementations of Raft and Multi-Paxos written in the IVy language, which is then translated to C++. These proofs reuse the protocol proofs as lemmas which embody the core algorithmic properties of those algorithms. This enables separating implementation concerns from core algorithmic concerns.

On top of that, we have also devised a technique to reduce liveness verification, which is notoriously complex, to decidable safety verification [@padon_reducing_2018]. This allowed us to prove liveness of Multi-Paxos and Stoppable Paxos using our methods for decidable safety verification.


# Proposed Approach

We propose to apply decidable verification to verify SCP and its implementation. Our approach is based on interactive verification using automated invariant checking with the IVy verifier[?]. Below we highlight the main aspects of our verification approach.

Modeling and programming in IVy
The IVy language allows developing both protocol specifications and their implementation in one language. It is an imperative programming and specification language based on first-order logic, which allows a high degree of proof automation. Domain-specific concepts such as quorums are abstracted in first-order logic (using axioms) for the purpose of proving protocols. Concrete implementations can later be provided (and must proved correct) using the modularity features of IVy.

Deployable Implementations
Protocol implementations are developed in the IVy language, which is then translated to C++. Standard modules provide access to Operating System API such as UDP and TCP networking. The end result is a conventional C++ binary that can be deployed in a distributed system and linked to client applications or other system components.

Safety Verification
The user expresses safety properties using state predicates, possibly adding ghost state to record past behavior, and then proves the properties by providing suitable inductive invariants. The candidate invariants are checked by the Z3 solver and, should the invariant not be inductive, a concrete counter-example is displayed graphically to help troubleshooting. The user may then change the candidate invariant and/or his code.

Decidable Verification
IVy checks that every verification condition (VC) sent to the Z3 solver can be solved with one of the  decision procedures implemented by Z3. This guarantees that Z3 does not rely on heuristics and performs reliably, and that it can present concrete counter-examples to help the user debug. If a VC is not in Z3’s decidable fragments, IVy gives an explanation that helps the user diagnose the problem (e.g. IVy displays the quantifier alternation graph of the VC). The user can then use one of two methods to make the VCs decidable: (a) rewriting guided by the quantifier alternation graph [OOPSLA 2017], or (b) modular decomposition using assume-guarantee reasoning [PLDI 2018].

Liveness Verification
The user expresses liveness properties in Linear Temporal Logic. Then, IVy automatically adds a ghost monitor to the system with the property that the monitor enters an error state if and only if a liveness property is violated [POPL 2018]. The user can then verify that no liveness property is violated by proving that the monitor never enters its error state, which is a safety property and can be handled as any other safety verification problem.

Separation of Concerns
The high-level protocol design can be verified independently of an implementation, proved correct, and then its properties can be used as lemmas to verify its implementation. This allows separating core algorithmic concerns from implementation concerns and optimizations.

# Challenges

Expressing verification problems in decidable logics can be tricky. 
We have shown that modular decomposition using assume-guarantee reasoning enables expressing complex systems with decidable logics. Expressing a property or code module in a decidable logic can be tricky. To address this challenge we plan to develop decidable-verification design patterns and libraries to guide the user.

Implementations require large invariants. 
Invariants in implementations can be tedious to come up with as they contain many details. However they are usually not conceptually difficult. To address this challenge we plan to employ invariant synthesis using both decision procedures when possible [Padon POPL 2016] and heuristic search otherwise [Todd paper].

Decidable logics have limited expressivity. 
What should we do when a property fundamentally falls outside any fragment that the solver can realistically handle? To address this challenge we plan to implement a bridge between IVy and the Isabelle/HOL interactive theorem prover for occasionally discharging undecidable verification conditions. This will allow use to handle high-level properties of protocols which depend on mathematical reasoning not expressible in decidable logics. Since first-order logic, the logic used in IVy, is a subset of the Isabelle/HOL logic, IVy verification conditions should be easily transferable to be solved in Isabelle/HOL. This will ensure that decidability does not become a roadblock in practical applications.

Ensuring models are faithful to reality
Models of low-level APIs such as networking or file-system APIs are complex and hard to get right since no formal specification usually exist. This is an issue for verifying implementations only. To address this challenge we plan to adapt specification testing techniques from the NetSem and SybilFS projects [?].

Liveness of implementations
Our liveness to safety reduction has been so far applied only to protocol, and not implementations. We expect scalability issues to arise when proving implementations live, and we plan to explore new modularity techniques tailored to liveness verification once we have a clearer picture of the issues.

# Expected Results

* Formalization and formal verification of the safety and liveness properties of SCP.
* Formal model of protocol and properties
* Safety proof
* Liveness proof
* IETF RFC based on the machine-checked formalization
* A verified safe C++ implementation produced with IVy of the core functionality of SCP.
* New features implemented in the IVy verification tool
    * Invariant synthesis
    * Bridge to Isabelle/HOL (optional; if needed)
    * Generation of test-cases for API models.
* We expect clear specifications of the requirements and protocols to lead to new algorithmic improvements to SCP and better characterization of its guarantees.
    * Reconfiguration and protocol updates
    * Liveness properties
    * Modeling dynamic participants and slices

# Budget

* Salary 70578.9
* 3 international trips to IETF meetings and visits to Stellar: 10K
* Hardware: 3K
* 6.5% University: 89389.2

# Old 

Over the last year we have developed new methods [@padon_reducing_2018, @PadonPaxosMadeEPR2017, @TaubeModularityDecidabilityImplementing2018], implemented in the IVy verifier[@padon_ivy:_2016], that drastically reduce the effort needed to verify distributed protocols and their implementations. As mentioned, we have no characterization of the algorithms that can be verified using our methods, but we have many encouraging successes.

Using our methods, we have verified the safety of State-Machine Replication protocols such as Multi-Paxos, Stoppable Paxos, Raft, a Byzantine version of Multi-Paxos, as well as some aspects of Ethereum’s Casper Proof-of-Stake protocol. We have also verified the safety of implementations of Raft and Multi-Paxos.

On top of that, we have also devised a technique to reduce liveness verification, which is notoriously complex, to decidable safety verification. This allowed us to prove liveness of the examples above using our methods for decidable safety verification.

The resulting proofs are an order of magnitude shorter than in previous work, and verification conditions reliably result in validation or a counter-example within few seconds both when verifying protocols and at larger scale when verifying implementations. 
