% Formally Verifying the Stellar Consensus Protocol
% Eli Gafni and Giuliano Losa

# Introduction

Open-membership distributed ledgers like Stellar will likely become critical global infrastructure for payments, notary services, identity and trust management, etc. Consequently, bugs in their design or implementation may have potentially catastrophic consequences. Testing these protocols is ineffective or too expensive since bugs may occur only under malicious attack or in global-scale deployments. Therefore distributed ledgers should be held to the highest standard of correctness, namely formal verification. 

Formally verifying an open distributed ledger is beyond the reach of established verification methods, which are too labor-intensive to scale to systems of such complexity. One reason is that the automatic solvers that should relieve the engineer from tedious manual proofs fail unpredictably or for obscure reasons.

Recently, we have made a leap forward, reducing the verification effort needed to verify Paxos-style algorithms by an order of magnitude using the novel concept of *decidable verification*. Alas, Paxos does not scale beyond a handful of nodes. Nevertheless, open ledgers that scale to global size are also built on some of the same principles as Paxos, but they are significantly more intricate.

The basis of this proposal is the hope that, like with the Paxos family, global-scale open ledgers will lend themselves to decidable verification. Informally speaking, we were successful with the Paxos family because those algorithms, though quite different from each other in terms of features, rely on common core invariants whose correctness is expressible in a decidable logic. We expect the Stellar Consensus Protocol (SCP) to satisfy similar invariants; hence our hope.

<!--on it being optimizations of an underlying Commit-Adopt version. Not surprisingly the Stellar ballot protocol is based on neutralizable statements which is essentially a Commit-Adopt. Hence our hope.-->
# Proposed Work

We propose to apply decidable verification to formally model and verify both the safety and liveness properties of the Stellar Consensus Protocol, and to use the formalization to guide the writing of an IETF standard.
Moreover, we propose to build a verified implementation, in C++, of the core functionality of the Stellar Consensus Protocol.

# Preliminary Results

We have implemented decidable verification methods in the IVy verifier[@padon_ivy:_2016] and we have demonstrated their effectiveness by verifying the safety and liveness of multiple intricate protocols, as well as the safety of protocol implementations.
<!-- Roughly speaking, our verification approach consists in reducing verification problems to checking state invariants expressed in a decidable logic.
Decidability means that we can rely on *decision procedures*, which are guaranteed to terminate, to automatically check invariants; in contrast, the heuristic search procedures used for verification with undecidable logics often diverge for obscure reasons, making tools based on them hard to use.
The challenge in using decidable verification is to overcome the limited expressivity of decidable logics. 
Indeed, it is not immediately clear that such logics can be applied to proving complex protocols or systems. 
Despite this, we have been able to develop proof strategies that make it possible. -->

**Safety of Protocols.** 
We have verified the safety properties of specifications of protocols such as Multi-Paxos, Vertical Paxos, and Stoppable Paxos [@PadonPaxosMadeEPR2017], Raft, Byzantine Paxos (Ref TODO), as well as some aspects of Ethereum’s Casper Proof-of-Stake protocol [@LosaCasperthy2017]. Remarkably, each proof consists of at most a few dozen lines.
This is in stark contrast with previous work: Lamport’s machine-checked proof in TLA+ of Byzantine Paxos [@lamport_byzantizing_2011] is several thousand lines long. 
Yoichi Hirai’s original proof [@HiraiMinimumAlgothy2017] of the Casper protocol is at least 10 times larger than ours.

**Verified Implementations.**
We have recently used decidable verification to verify the safety of implementations of Raft and Multi-Paxos [@TaubeModularityDecidabilityImplementing2018] written in the IVy language, which is then translated to C++. 
We achieved a proof to code ratio (in lines) of 0.5. Compared to the IronFleet project [@hawblitzel_ironfleet:_2015], which verified similar implementations with a ratio of 4, this is almost an order of magnitude improvement. 
<!--Our implementation proofs reuse the protocol proofs as lemmas which embody the core algorithmic properties of those algorithms; this enables separating implementation concerns from core algorithmic concerns.-->

**Liveness Verification.**
On top of that, we have also devised a new technique to reduce liveness verification, which is notoriously complex, to decidable safety verification [@padon_reducing_2018]. This allowed us to prove liveness of the Multi-Paxos and Stoppable Paxos protocols by first reducing the liveness verification problem to a safety problem and then using our methods for decidable safety verification.

<!--**Reliable Automation.**
Those formal verification efforts were successful in part because decidable verification enables powerful and reliable automation: invariants are checked automatically without any hints to the solver, and solver queries return in a few seconds with a positive answer or, to help debugging, a concrete counter-example displayed graphically.-->


# Challenges

<!--Applying decidable verification to the Stellar Consensus Protocol will come with some challenges.-->
The main challenge is that decidable logics may not be expressive enough to model and verify SCP. 
Should we encounter a fundamentally undecidable property, we plan to isolate this property thanks to IVy's modularity features and transfer the verification to the Isabelle/HOL interactive theorem prover, which is less automated than IVy but can check proofs of statements falling outside any decidable logic (Dr. Losa has extensive experience working with Isabelle/HOL, see e.g. [@Abortable_Linearizable_Modules-AFP]).
<!-- IVy's logic is a subset of the Isabelle/HOL logic, therefore we can naturally transfer a verification problem from IVy to Isabelle/HOL.-->

Moreover, developing a verified safe implementation of SCP will test the scalability limits of decidable verification. 
We will use IVy's modularity features, notably assume-guarantee reasoning, to separate the verification problem into tractable sub-problems.
This may require the implementation of new modular proof rules and other improvements to IVy.

Finally, the verification of implementations relies on models, built by us, of the underlying OS APIs.
However, since no formal specification usually exists, models of low-level APIs such as networking or file-system APIs are hard to get right. 
To address this challenge we plan to integrate specification testing techniques (e.g. [@BishopRigorousSpecificationConformance2005]) with IVy.

# Collaborations

Preliminary work described in this proposal was conducted in collaboration with Marcelo Taube, Oded Padon, Sharon Shoham, and Mooly Sagiv at Tel-Aviv University, James R. Wilcox and Doug Woos at the University of Washington, Kenneth McMillan at Microsoft Research, and Jochen Hoenicke and Andreas Podelski at the University of Freiburg.
We expect to continue our collaboration with those groups, as well as to work with other researchers.

# Budget

To accomplish the proposed work, we ask for the support of Giuliano Losa as a post-doctoral scholar at UCLA for one year.

The expected costs are as follows:

* Salary: \$4462.50 x 12 months: \$53,550.00
* Benefits (31.8%) x 12 months: \$17,028.90
* Total with benefits: \$70,578.9
* Travel (attendance to 2 or 3 IETF meetings and visits to the Stellar Foundation) \$10,000.00
* Hardware \$4,000.00
Net total: \$84,578.9

If funded as an unrestricted gift, UCLA will take 6.5% of the awarded amount.
This brings the requested funds to \$90,548.90

# Bibliography
