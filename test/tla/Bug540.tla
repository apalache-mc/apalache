------------------------------- MODULE Bug540 -------------------------------
\* Module used in https://github.com/informalsystems/apalache/issues/540
\* Test to see issue has been resolved

EXTENDS Integers, FiniteSets

CONSTANTS 
\* @type: Set(Str);
ChainIds,
\* @type: Int;
MaxClientsPerChain,
\* @type: Int;
MaxClientHeight

VARIABLE 
\* @type: Str -> [clientIdCounter: Int, clients: Int->Int];
chains

CInit == /\ ChainIds = {"chain-A", "chain-B"}
         /\ MaxClientsPerChain = 4
         /\ MaxClientHeight = 4

ClientIds == 0..(MaxClientsPerChain - 1)
ClientHeights == 1..MaxClientHeight
NullHeight == 0

Clients == [
    ClientIds -> ClientHeights \union {NullHeight}
]
Chain == [
    clientIdCounter: 0..MaxClientsPerChain,
    clients: Clients
]

Init ==
    LET emptyChain == [
        clients |-> [clientId \in ClientIds |-> NullHeight],
        clientIdCounter |-> 0
    ] IN
    /\ chains = [chainId \in ChainIds |-> emptyChain]

Next == UNCHANGED <<chains>>

TypeOK == chains \in [ChainIds -> Chain]
Inv == TRUE
===============================================================================