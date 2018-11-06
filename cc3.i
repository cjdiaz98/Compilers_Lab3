// cc2.i -- block written for the lab 1 code check
//       -- uses in order of def
// Fall 2015, COMP 412, Rice University
//SIM INPUT: -i 0 1 2 3 4 5 6 7 8 9 10
//OUTPUT: 55
loadI  0 => r0
loadI  4 => r1
load   r0 => r10
add    r0, r1 => r0
load   r0 => r11
add    r0, r1 => r0
load   r0 => r12
add    r0, r1 => r0
load   r0 => r13
add    r0, r1 => r0
load   r0 => r14
add    r0, r1 => r0
load   r0 => r15
add    r0, r1 => r0
load   r0 => r16
add    r0, r1 => r0
load   r0 => r17
add    r0, r1 => r0
load   r0 => r18
add    r0, r1 => r0
load   r0 => r19
//
add    r18, r19 => r24
add    r16, r17 => r23
add    r14, r15 => r22
add    r12, r13 => r21
add    r10, r11 => r20
//
add    r20, r21 => r20
add    r22, r23 => r21
add    r20, r24 => r20
add    r20, r21 => r20
//
loadI  0   => r0
store  r20 => r0
output 0
add    r20, r21 => r30

