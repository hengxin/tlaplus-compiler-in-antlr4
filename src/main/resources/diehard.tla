-------------------------- MODULE DieHard  --------------------------
EXTENDS Naturals
VARIABLES small,big

Init == /\ small = 0
       /\ big = 0

TypeOK == /\ small \in (0..3)
         /\ big \in (0..5)


FillSmall == /\ small' = 3
            /\ big' = big

FillBig == /\ small' = small
          /\ big' = 5


EmptySmall == /\ small' = 0
             /\ big' = big

EmptyBig == /\ big' = 0
           /\ small' = small

SmallToBig == IF small + big < 5
             THEN
                /\ big' = small + big
                /\ small' = 0
             ELSE
                /\ big' = 5
                /\ small' = small - (5 - big)

BigToSmall == IF small + big < 3
             THEN
                /\ small' = small + big
                /\ big' = 0
             ELSE
                /\ small' = 3
                /\ big' = big - (3 - small)

Next == \/ FillSmall
       \/ FillBig
       \/ SmallToBig
       \/ BigToSmall
       \/ EmptyBig
       \/ EmptySmall

================================================