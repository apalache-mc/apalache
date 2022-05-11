----------------------------- MODULE PizzaOrder -------------------------------
EXTENDS Integers, Sequences

CONSTANTS
    (*
        A set of clients.
        @type: Set(Str);
     *)
    CLIENTS,
    (*
        A set of all possible orders.
        @type: Set(Int);
     *)
    ORDERS

VARIABLES
    \* a list of outstanding orders on the server
    \* @typeAlias: ORDER = { type: Str, src: Str, dst: Str, order: Int };
    \* @type: Seq(ORDER);
    outstanding,
    \* the list of delivered orders, one per client
    \* @type: Str -> Seq(Int);
    delivered,
    \* all messages that are sent over the network
    \* @type: Set(ORDER);
    network

\* a constant for the server name
SERVER == "server"

ConstInit ==
    /\ CLIENTS = { "joe", "may" }
    /\ ORDERS = 1..5

(******************************** Client *************************************)    
SendNewOrder ==
    \E c \in CLIENTS, ord \in ORDERS:
        /\ network' = network \union {
             [ type |-> "orderReq", src |-> c, dst |-> SERVER, order |-> ord ]
           }
        /\ UNCHANGED <<outstanding, delivered>>

(******************************** Server *************************************)    
ReceiveOrder ==
    \E m \in network:
        /\ m.type = "orderReq"
        /\ outstanding' = Append(outstanding, m)
        /\ network' = network \union {
              [ type |-> "orderAck",
                src |-> SERVER,
                dst |-> m.src,
                order |-> m.order ]
            }
        /\ UNCHANGED delivered

DeliverOrder ==
    /\ Len(outstanding) /= 0
    /\ LET m == Head(outstanding) IN
        delivered' = [ delivered EXCEPT
                         ![m.src] = Append(delivered[m.src], m.order) ]
    /\ outstanding' = Tail(outstanding)                     
    /\ UNCHANGED network

(************************* Distributed system ********************************)
Init ==
    /\ outstanding = << >>
    /\ delivered = [ c \in CLIENTS |-> << >> ]
    /\ network = {}

Next ==
    \/ SendNewOrder
    \/ ReceiveOrder
    \/ DeliverOrder

(*********************** Expected properties *********************************)
NoDoubleDelivery ==
    \A c \in CLIENTS:
        LET deliveredToClient == delivered[c] IN
        \A i, j \in DOMAIN deliveredToClient:
            i /= j => deliveredToClient[i] /= deliveredToClient[j]

===============================================================================
