param int_n integer ;
param ext_n integer ;
param notches_n integer ;
set notches := {1..notches_n} ;

param pairs_n integer ;
param pairs{i in 1..pairs_n,1..2} integer ;

set int_head_notches{i in notches} default { } ;
set int_tail_notches{i in notches} default { } ;
set ext_head_notches{i in notches} default { } ;
set ext_tail_notches{i in notches} default { } ;

param ext_length{int_n..ext_n} integer ;

var int{i in 1..int_n} integer >= 0 ;
var int_leave{i in 1..int_n} integer >= 0 ;
var int_enter{i in 1..int_n} integer >= 0 ;
var int_both{i in 1..int_n} integer >= 0 ;
var ext{i in int_n..ext_n} integer >= 0 ;

minimize obj : sum{i in int_n..ext_n} ext_length[i] ;

s.t. complement{i in 1..pairs_n} :
    int[pairs[i,1]] + int_leave[pairs[i,1]] + int_enter[pairs[i,1]]
  - int[pairs[i,2]] - int_leave[pairs[i,2]] - int_enter[pairs[i,2]] = 0 ; 

s.t. int_notch{i in notches} : 
    sum{j in int_head_notches[i]} (int[j] + int_leave[j])
  - sum{j in int_tail_notches[i]} (int[j] + int_enter[j]) = 0 ;

s.t. ext_enter_notch{i in notches} : 
    sum{j in ext_head_notches[i]} ext[j]
  - sum{j in int_tail_notches[i]} int_leave[j] = 0 ;

s.t. ext_leave_notch{i in notches} : 
    sum{j in int_head_notches[i]} int_enter[j] 
  - sum{j in ext_tail_notches[i]} ext[j] = 0 ;

solve ;
      
printf '[' ;
printf{i in 1..int_n} '%.3f,', int[i];
printf{i in int_n..ext_n} '%.3f,', ext[i];
printf ']\n';

