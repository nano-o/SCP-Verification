% Formally Verifying the Stellar Consensus Protocol
% Eli Gafni and Giuliano Losa

# Introduction

Open-membership distributed ledgers like Stellar will likely become critical global infrastructure for payments, notary services, identity and trust management, etc. Consequently, bugs in their design or implementation having potentially catastrophic consequences. Testing these protocols is ineffective or too expensive since bugs occur only under malicious attack or in global-scale deployments. Therefore distributed ledgers should be held to the highest standard of correctness, namely formal verification. 

Full end-to-end verification of an open distributed ledger is beyond the reach of established verification methods, which are too labor-intensive to scale to the complexity of distributed ledgers. One reason is that the automatic solvers used to relieve the user from tedious manual proofs fail unpredictably or for reasons obscure to the user.

Recently, we have made a leap forward, reducing the verification effort needed to verify Paxos-style algorithms by an order of magnitude, using the novel concept of *decidable verification*. Alas, Paxos does not scale beyond a handful of nodes. Nevertheless, open ledgers that scale to global size are also built on some of the same principles as Paxos, but they are significantly more intricate.

The basis of this proposal is the hope that, like the Paxos family, the new algorithms for global-scale open ledgers will lend themselves to decidable verification. Informally speaking, we were successful with the Paxos family because those algorithms, even though quite difference in features, rely on the same core invariants, whose correctness is expressible in a decidable logic. We expect SCP to satisfy similar invariants; hence our hope.

<!--on it being optimizations of an underlying Commit-Adopt version. Not surprisingly the Stellar ballot protocol is based on neutralizable statements which is essentially a Commit-Adopt. Hence our hope.-->

## Preliminary Results

We have implemented decidable verification in the IVy verifier[@padon_ivy:_2016] and we have demonstrated its effectiveness by verifying the safety and liveness of multiple intricate protocols, as well as the safety of implementations.

We have verified the safety of protocols such as Multi-Paxos, Vertical Paxos, Stoppable Paxos, and Raft, Byzantine Paxos, as well as some aspects of Ethereum’s Casper Proof-of-Stake protocol[@LosaCasperthy2017]. Remarkably, each proof consists of at most a few dozen lines [@PadonPaxosMadeEPR2017].
This is in stark contrast with previous work: Lamport’s machine-checked proof in TLA+ of Byzantine Paxos [@lamport_byzantizing_2011] is about 3000 lines long. 
Yoichi Hirai’s original proof [@HiraiMinimumAlgothy2017] of the same property of the Casper protocol is at least 10 times larger than ours.

We have also recently used decidable verification to verify the safety of implementations of Raft and Multi-Paxos [@TaubeModularityDecidabilityImplementing2018] written in the IVy language (the IVy sources consists of around 1000 lines of code), which is then translated to C++. These proofs reuse the protocol proofs as lemmas which embody the core algorithmic properties of those algorithms. This enables separating implementation concerns from core algorithmic concerns.

On top of that, we have also devised a technique to reduce liveness verification, which is notoriously complex, to decidable safety verification [@padon_reducing_2018]. This allowed us to prove liveness of Multi-Paxos and Stoppable Paxos using our methods for decidable safety verification.

Those formal verification efforts were successful largely because decidable verification enables powerful and reliable automation: invariants are checked automatically without any hints to the solver, and solver queries return in a few seconds with a positive answer or a concrete counter-example, displayed graphically, that helps debugging.

# Proposed Work

We propose to apply decidable verification to formally verify both the safety and liveness properties of the Stellar Consensus Protocol.
This formalization should also result in a machine-checked IETF standard.
Moreover, we propose to build a verified implementation, in C++, of the core functionality of the Stellar Consensus Protocol.

# Challenges

Applying decidable verification to the Stellar Consensus Protocol will come with some challenges.
One potential challenge is that decidable logics may not be expressive enough to model some of the domain-specific concepts use in SCP, such as its notion of quorum, and SCP may intrinsically exhibit some undecidable verification conditions. 
Should this issue arise, we plan to prove the properties that fall outside any decidable fragment using the Isabelle/HOL interactive theorem prover.
Proving in Isabelle/HOL is labor intensive but is occasionally feasible. 
Moreover, IVy's logic a subset of the Isabelle/HOL logic, which should enable a straightforward mapping between the two.
This will ensure that decidability does not become a roadblock in practice.

Producing a verified safe implementation of SCP will test the scalability limits of decidable verification. 
Will will use IVy's modularity features, notably assume-guarantee reasoning, to separate the verification problem into tractable sub-problems.
This may require the implementation of new modular proof rules and other improvements to IVy.

One particular challenge may be that implementations require the user to come up with large invariants.
Those can be tedious to come up with as they contain many details. However they are usually not conceptually difficult and can likely be inferred automatically. 
To address this challenge we plan to add invariant synthesis to IVy, using both decision procedures when possible [@padon_decidability_2016] and heuristic search otherwise [@PadhiDatadrivenpreconditioninference2016].

Proving the liveness of an SCP implementation will break new ground, as we have not applied our liveness verification method (i.e. the reduction safety) to verify the liveness of implementations. We expect scalability issues to arise when proving implementations live, and we plan to explore new modularity techniques tailored to liveness verification once we have a clearer picture of the issues.

Finally, the verification of implementations rely on models of the underlying OS APIs.
However, since no formal specification usually exists, models of low-level APIs such as networking or file-system APIs are hard to get right. 
To address this challenge we plan to adapt specification testing techniques from the NetSem[@BishopRigorousSpecificationConformance2005] and SybilFS[@RidgeSibylFSFormalSpecification2015] projects.

# Budget

To accomplish the proposed work, we ask for the support of Giuliano Losa as a post-doctoral scholar at UCLA for one year.
The expected costs are as follows:

* on year salary: 70578.90\$
* travel, including attendance to 2 or 3 IETF meetings and visits to the Stellar Foundation: 10K
* Hardware: 3K

If funded as an unrestricted gift, UCLA will take 6.5% of the awarded amount.
This brings the requested funds to 89389.20\$.

# Bibliography
