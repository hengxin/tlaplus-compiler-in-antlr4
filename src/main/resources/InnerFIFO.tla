---- MODULE InnerFIFO ----
(* Sequences定义了在有限序列上的操作 比如Seq(s)等 见P35 *)
EXTENDS Naturals, Sequences
CONSTANT Message
VARIABLES in, out, q
(* 传输使用的异步协议见P30 Module Channel *)
INChan == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out
----------------------------
Init == /\ InChan!Init
        /\ OutChan!Init
        /\ q = <<>>
TypeInvariant == /\ InChan!TypeInvariant
                 /\ OutChan!TypeInvariant
                 /\ q \in Seq(Message)
SSend(msg) == /\ InChan!Send(msg)             \* send message on channel in
              /\ UNCHANGED <<out, q>>
BufRcv == /\ InChan!Rcv
          /\ q' = Append(q, in.val)           \* Receive message from channel in and append it to tail of q
          /\ UNCHANGED out
BufSend == /\ q # <<>>                        \* Enabled only if q is nonempty.
           /\ OutChan!Send(Head(q))           \* Send Head(q) on channel out and remove it from q
RRcv == /\ OutChan!Rcv
        /\ UNCHANGED in                       \* Receive message from channel out
Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv
Spec == Init /\ [] [Next]_<<in, out, q>>
------------------------------
THEOREM Spec => [] TypeIInvariant
===========================================