---- MODULE model_value_compare ----
\* Regression test for #280: Invalid successor state with model values
\* Reproduces MCInnerSequential pattern

EXTENDS Naturals, Sequences

CONSTANTS Proc, Reg

VARIABLES regFile, opQ

Done == CHOOSE v : v \notin Reg

Init ==
    /\ regFile = [p \in Proc |-> [r \in Reg |-> [op |-> "Free"]]]
    /\ opQ = [p \in Proc |-> <<>>]

\* Issue a request - set regFile[proc][reg].op to "Rd"
IssueRequest(proc, reg) ==
    /\ regFile[proc][reg].op = "Free"
    /\ regFile' = [regFile EXCEPT ![proc][reg].op = "Rd"]
    /\ opQ' = [opQ EXCEPT ![proc] = Append(@, [reg |-> reg])]

\* Respond - set regFile[proc][reg].op back to "Free" AND update opQ[proc][idx].reg to Done
RespondToRd(proc, reg) ==
    /\ regFile[proc][reg].op = "Rd"
    /\ regFile' = [regFile EXCEPT ![proc][reg].op = "Free"]
    /\ opQ' = LET idx == CHOOSE i \in DOMAIN opQ[proc] : opQ[proc][i].reg = reg
              IN [opQ EXCEPT ![proc][idx].reg = Done]

\* Remove completed operation - REQUIRES Head(opQ[proc]).reg = Done
RemoveOp(proc) ==
    /\ opQ[proc] # <<>>
    /\ Head(opQ[proc]).reg = Done
    /\ opQ' = [opQ EXCEPT ![proc] = Tail(@)]
    /\ UNCHANGED regFile

Next == \E proc \in Proc, reg \in Reg : IssueRequest(proc, reg) \/ RespondToRd(proc, reg) \/ RemoveOp(proc)

\* CRITICAL INVARIANT: If opQ is empty, regFile.op must be "Free"
\* This catches the bug where RemoveOp fires without RespondToRd completing
Inv == \A p \in Proc, r \in Reg : (opQ[p] = <<>>) => (regFile[p][r].op = "Free")

Spec == Init /\ [][Next]_<<regFile, opQ>>
====
