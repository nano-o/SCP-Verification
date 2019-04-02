-------------------------- MODULE SynchronousAlgo5 --------------------------
EXTENDS FBAS
        
CONSTANT Epoch

Phase == {1,2,3,4,5}

(*
--algorithm Consensus {             
    variables 
        value = [p \in P |-> [e \in Epoch |-> [i \in Phase |-> 
            IF e = 1 /\ i = 1 THEN InitVal[p] ELSE <<>> ]]],
        epoch = 1;
        (*starDisplay*)                  
    define {            
    (*enDisplay*)        
        NumToProc == CHOOSE f \in [1..Cardinality(WellBehaved) -> WellBehaved] : 
            \A p \in WellBehaved : \E i \in DOMAIN f : f[i] = p
        ProcToNum(p) == CHOOSE n \in 1..Cardinality(WellBehaved) : NumToProc[n] = p
                         
       (*starDisplay*)
        Max(S, LessEq(_,_)) == CHOOSE e \in S : \A e1 \in S : LessEq(e1,e)
        LessEqLexico(x,y) ==
                \/  x.epoch < y.epoch
                \/  x.epoch = y.epoch /\ x.grade < y.grade
                \/  x.epoch = y.epoch /\ x.grade = y.grade
        MaxLexico(S) ==  Max(S, LessEqLexico)
        MaxVal(p) == 
            LET egvs == {egv \in [epoch : Epoch, grade : Phase, value : V] :
                    /\  value[p][egv.epoch][egv.grade] = egv.value}
            IN MaxLexico(egvs)
        QuorumsWithin(p, H) == {Q \in SUBSET H : Q \in Quorums(p)}
        BlockingWithin(p, H) == {B \in SUBSET H : B \in Blocking(p)}
        Above(i) == {g \in {1,2,3,4,5} : g >= i} 
        MaxBlocking(p, i, H) ==
            LET blocking == {b \in [epoch : Epoch, value : V, grade : Above(i)] : 
                    \E B \in BlockingWithin(p, H) : \A q \in B :
                        value[q][b.epoch][b.grade] = b.value }
            IN  IF blocking = {} THEN MaxVal(p) ELSE MaxLexico(blocking)
        GotQuorum(p, H, i) == {v \in V :
            \E Q \in QuorumsWithin(p, H) : 
                \A q \in Q : value[q][epoch][i] = v }
        (*enDisplay*)
                    
        Safety == \A p,q \in Intact : \A e1,e2 \in Epoch :
            /\  value[p][e1][5] # <<>>
            /\  value[p][e2][5] # <<>>
            =>  value[p][e1][5] = value[p][e2][5]
            
        Inv1 == \A p \in P : \A v \in V : \A e \in Epoch :
            value[p][e][5] = v => \E Q \in Quorums(p) : \A q \in Q : 
                /\  value[q][e][4] = v \/ value[q][e][5] = v 
                /\  \A e2 \in Epoch, g \in Phase : e2 > e => 
                        \/  value[q][e2][g] = <<>>
                        \/  value[q][e2][g] = v
            
        HeardFrom == {H \in SUBSET P \ P : Cardinality(H) # 1}
            (*starDisplay*)
    }            
    (*enDisplay*)
(* startDisplay *) 
    procedure receive(proc, phase, H) {
       with (mb = MaxBlocking(proc,2,H))
        if (MaxVal(proc).grade = 4 /\ MaxVal(proc).epoch < mb.epoch)
            value[proc][mb.epoch][mb.grade] := mb.value;
        if (phase = 1) {
            with (leader \in P, v \in V) {
                if (leader \in H 
                        /\  value[leader][epoch][1] = v
                        /\  \/ MaxVal(proc).grade < 4 
                            \/ MaxVal(proc).value = v)
                    value[proc][epoch][1] := v;
            }
        }
        else if (phase \in {2,3,4}) {
            if (GotQuorum(proc, H, phase-1) # {})
                with (v \in GotQuorum(proc, H, phase-1))
                value[proc][epoch][phase] := v;
        }
        else if (phase = 5) {
            if (GotQuorum(proc, H, 4) # {})
                with (v \in GotQuorum(proc, H, 4))
                value[proc][epoch][5] := v; \* decision!
            if (MaxVal(proc).grade < 4 /\ epoch+1 \in Epoch)
                value[proc][epoch+1][1] := MaxBlocking(proc, 3, H).value
        };
        return
    }
(* endDisplay *)    
    
    process (scheduler = "sched") 
        variables procNum = 1, phase = 1;
    {
l5:     while (epoch \in Epoch) {
l6:         while (phase <= 5) {
l7:             while (procNum \in DOMAIN NumToProc) {
ll:                with (Heard \in HeardFrom) 
                        call receive(NumToProc[procNum], phase, Heard);
l8:                procNum := procNum+1
                };
                phase := phase+1;
                procNum := 1;
            };
            epoch := epoch + 1;
            phase := 1
        }
    }
}
*)
\* BEGIN TRANSLATION
\* Process variable phase of process scheduler at line 92 col 32 changed to phase_
CONSTANT defaultInitValue
VARIABLES value, epoch, pc, stack

(* define statement *)
NumToProc == CHOOSE f \in [1..Cardinality(WellBehaved) -> WellBehaved] :
    \A p \in WellBehaved : \E i \in DOMAIN f : f[i] = p
ProcToNum(p) == CHOOSE n \in 1..Cardinality(WellBehaved) : NumToProc[n] = p


Max(S, LessEq(_,_)) == CHOOSE e \in S : \A e1 \in S : LessEq(e1,e)
LessEqLexico(x,y) ==
        \/  x.epoch < y.epoch
        \/  x.epoch = y.epoch /\ x.grade < y.grade
        \/  x.epoch = y.epoch /\ x.grade = y.grade
MaxLexico(S) ==  Max(S, LessEqLexico)
MaxVal(p) ==
    LET egvs == {egv \in [epoch : Epoch, grade : Phase, value : V] :
            /\  value[p][egv.epoch][egv.grade] = egv.value}
    IN MaxLexico(egvs)
QuorumsWithin(p, H) == {Q \in SUBSET H : Q \in Quorums(p)}
BlockingWithin(p, H) == {B \in SUBSET H : B \in Blocking(p)}
Above(i) == {g \in {1,2,3,4,5} : g >= i}
MaxBlocking(p, i, H) ==
    LET blocking == {b \in [epoch : Epoch, value : V, grade : Above(i)] :
            \E B \in BlockingWithin(p, H) : \A q \in B :
                value[q][b.epoch][b.grade] = b.value }
    IN  IF blocking = {} THEN MaxVal(p) ELSE MaxLexico(blocking)
GotQuorum(p, H, i) == {v \in V :
    \E Q \in QuorumsWithin(p, H) :
        \A q \in Q : value[q][epoch][i] = v }


Safety == \A p,q \in Intact : \A e1,e2 \in Epoch :
    /\  value[p][e1][5] # <<>>
    /\  value[p][e2][5] # <<>>
    =>  value[p][e1][5] = value[p][e2][5]

Inv1 == \A p \in P : \A v \in V : \A e \in Epoch :
    value[p][e][5] = v => \E Q \in Quorums(p) : \A q \in Q :
        /\  value[q][e][4] = v \/ value[q][e][5] = v
        /\  \A e2 \in Epoch, g \in Phase : e2 > e =>
                \/  value[q][e2][g] = <<>>
                \/  value[q][e2][g] = v

HeardFrom == {H \in SUBSET P \ P : Cardinality(H) # 1}

VARIABLES proc, phase, H, procNum, phase_

vars == << value, epoch, pc, stack, proc, phase, H, procNum, phase_ >>

ProcSet == {"sched"}

Init == (* Global variables *)
        /\ value =     [p \in P |-> [e \in Epoch |-> [i \in Phase |->
                   IF e = 1 /\ i = 1 THEN InitVal[p] ELSE <<>> ]]]
        /\ epoch = 1
        (* Procedure receive *)
        /\ proc = [ self \in ProcSet |-> defaultInitValue]
        /\ phase = [ self \in ProcSet |-> defaultInitValue]
        /\ H = [ self \in ProcSet |-> defaultInitValue]
        (* Process scheduler *)
        /\ procNum = 1
        /\ phase_ = 1
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "l5"]

l0(self) == /\ pc[self] = "l0"
            /\ LET mb == MaxBlocking(proc[self],2,H[self]) IN
                 IF MaxVal(proc[self]).grade = 4 /\ MaxVal(proc[self]).epoch < mb.epoch
                    THEN /\ value' = [value EXCEPT ![proc[self]][mb.epoch][mb.grade] = mb.value]
                    ELSE /\ TRUE
                         /\ value' = value
            /\ IF phase[self] = 1
                  THEN /\ pc' = [pc EXCEPT ![self] = "l1"]
                  ELSE /\ IF phase[self] \in {2,3,4}
                             THEN /\ IF GotQuorum(proc[self], H[self], phase[self]-1) # {}
                                        THEN /\ pc' = [pc EXCEPT ![self] = "l2"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "ret"]
                             ELSE /\ IF phase[self] = 5
                                        THEN /\ IF GotQuorum(proc[self], H[self], 4) # {}
                                                   THEN /\ pc' = [pc EXCEPT ![self] = "l3"]
                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "ret"]
            /\ UNCHANGED << epoch, stack, proc, phase, H, procNum, phase_ >>

l1(self) == /\ pc[self] = "l1"
            /\ \E leader \in P:
                 \E v \in V:
                   IF leader \in H[self]
                          /\  value[leader][epoch][1] = v
                          /\  \/ MaxVal(proc[self]).grade < 4
                              \/ MaxVal(proc[self]).value = v
                      THEN /\ value' = [value EXCEPT ![proc[self]][epoch][1] = v]
                      ELSE /\ TRUE
                           /\ value' = value
            /\ pc' = [pc EXCEPT ![self] = "ret"]
            /\ UNCHANGED << epoch, stack, proc, phase, H, procNum, phase_ >>

l2(self) == /\ pc[self] = "l2"
            /\ \E v \in GotQuorum(proc[self], H[self], phase[self]-1):
                 value' = [value EXCEPT ![proc[self]][epoch][phase[self]] = v]
            /\ pc' = [pc EXCEPT ![self] = "ret"]
            /\ UNCHANGED << epoch, stack, proc, phase, H, procNum, phase_ >>

l4(self) == /\ pc[self] = "l4"
            /\ IF MaxVal(proc[self]).grade < 4 /\ epoch+1 \in Epoch
                  THEN /\ value' = [value EXCEPT ![proc[self]][epoch+1][1] = MaxBlocking(proc[self], 3, H[self]).value]
                  ELSE /\ TRUE
                       /\ value' = value
            /\ pc' = [pc EXCEPT ![self] = "ret"]
            /\ UNCHANGED << epoch, stack, proc, phase, H, procNum, phase_ >>

l3(self) == /\ pc[self] = "l3"
            /\ \E v \in GotQuorum(proc[self], H[self], 4):
                 value' = [value EXCEPT ![proc[self]][epoch][5] = v]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << epoch, stack, proc, phase, H, procNum, phase_ >>

ret(self) == /\ pc[self] = "ret"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ proc' = [proc EXCEPT ![self] = Head(stack[self]).proc]
             /\ phase' = [phase EXCEPT ![self] = Head(stack[self]).phase]
             /\ H' = [H EXCEPT ![self] = Head(stack[self]).H]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << value, epoch, procNum, phase_ >>

receive(self) == l0(self) \/ l1(self) \/ l2(self) \/ l4(self) \/ l3(self)
                    \/ ret(self)

l5 == /\ pc["sched"] = "l5"
      /\ IF epoch \in Epoch
            THEN /\ pc' = [pc EXCEPT !["sched"] = "l6"]
            ELSE /\ pc' = [pc EXCEPT !["sched"] = "Done"]
      /\ UNCHANGED << value, epoch, stack, proc, phase, H, procNum, phase_ >>

l6 == /\ pc["sched"] = "l6"
      /\ IF phase_ <= 5
            THEN /\ pc' = [pc EXCEPT !["sched"] = "l7"]
                 /\ UNCHANGED << epoch, phase_ >>
            ELSE /\ epoch' = epoch + 1
                 /\ phase_' = 1
                 /\ pc' = [pc EXCEPT !["sched"] = "l5"]
      /\ UNCHANGED << value, stack, proc, phase, H, procNum >>

l7 == /\ pc["sched"] = "l7"
      /\ IF procNum \in DOMAIN NumToProc
            THEN /\ pc' = [pc EXCEPT !["sched"] = "ll"]
                 /\ UNCHANGED << procNum, phase_ >>
            ELSE /\ phase_' = phase_+1
                 /\ procNum' = 1
                 /\ pc' = [pc EXCEPT !["sched"] = "l6"]
      /\ UNCHANGED << value, epoch, stack, proc, phase, H >>

ll == /\ pc["sched"] = "ll"
      /\ \E Heard \in HeardFrom:
           /\ /\ H' = [H EXCEPT !["sched"] = Heard]
              /\ phase' = [phase EXCEPT !["sched"] = phase_]
              /\ proc' = [proc EXCEPT !["sched"] = NumToProc[procNum]]
              /\ stack' = [stack EXCEPT !["sched"] = << [ procedure |->  "receive",
                                                          pc        |->  "l8",
                                                          proc      |->  proc["sched"],
                                                          phase     |->  phase["sched"],
                                                          H         |->  H["sched"] ] >>
                                                      \o stack["sched"]]
           /\ pc' = [pc EXCEPT !["sched"] = "l0"]
      /\ UNCHANGED << value, epoch, procNum, phase_ >>

l8 == /\ pc["sched"] = "l8"
      /\ procNum' = procNum+1
      /\ pc' = [pc EXCEPT !["sched"] = "l7"]
      /\ UNCHANGED << value, epoch, stack, proc, phase, H, phase_ >>

scheduler == l5 \/ l6 \/ l7 \/ ll \/ l8

Next == scheduler
           \/ (\E self \in ProcSet: receive(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu Nov 01 12:43:26 PDT 2018 by nano
\* Created Thu Nov 01 10:46:36 PDT 2018 by nano
