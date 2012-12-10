param int_n integer ;
param ext_n integer ;
set notches ;

set int_head_notches{i in notches} default { } ;
set int_tail_notches{i in notches} default { } ;
set ext_head_notches{i in notches} default { } ;
set ext_tail_notches{i in notches} default { } ;

param pairs_n integer ;
param pairs{i in 1..pairs_n,1..2} integer ;

param length{1..ext_n} integer ;

param vertices_n integer ;
set vertex_heads{1..vertices_n} dimen 2 ;
set vertex_tails{1..vertices_n} dimen 2 ;


var ext{i in int_n+1..ext_n} integer >= 0 ;
var leave{i in 1..int_n} integer >= 0 ;
var enter{i in 1..int_n} integer >= 0 ;
var near_leave{i in 1..int_n} integer >= 0 ;
var near_enter{i in 1..int_n} integer >= 0 ;

var vertex{1..vertices_n} integer ;

# param letters_n integer ;
# param letter_face{1..letters_n} integer ;
# set letter_edges{1..letters_n} ;


minimize obj : sum{i in 1..int_n} (near_leave[i] + near_enter[i]) ;

s.t. boundary_length_six : sum{i in int_n+1..ext_n} length[i]*ext[i] = 6 ;

s.t. complement{i in 1..pairs_n} :
    leave[pairs[i,1]] + enter[pairs[i,1]] 
  + near_leave[pairs[i,1]] + near_enter[pairs[i,1]] 
  = leave[pairs[i,2]] + enter[pairs[i,2]] 
  + near_leave[pairs[i,2]] + near_enter[pairs[i,2]] ; 

# s.t. complement_both{i in 1..pairs_n} :
#     both[pairs[i,1]] + near_both[pairs[i,1]] 
#   = both[pairs[i,2]] + near_both[pairs[i,2]] ; 

s.t. near_notch{i in notches} : 
    sum{j in int_head_notches[i]} near_enter[j] 
  = sum{j in int_tail_notches[i]} near_leave[j] ;

s.t. ext_enter_notch{i in notches} : 
    sum{j in int_tail_notches[i]} leave[j] 
  = sum{j in ext_head_notches[i]} ext[j] ;

s.t. ext_leave_notch{i in notches} : 
    sum{j in int_head_notches[i]} enter[j] 
  = sum{j in ext_tail_notches[i]} ext[j] ;


param vertex_leaving{i in 1..int_n,j in 1..vertices_n} := 
    sum{(k,n) in vertex_tails[j]} if k=i then n else 0 ;
param vertex_entering{i in 1..int_n,j in 1..vertices_n} := 
    sum{(k,n) in vertex_heads[j]} if k=i then n else 0 ;
s.t. edge{i in 1..int_n} : 
    sum{j in 1..vertices_n} ( vertex_leaving[i,j]*vertex[j] )
  + leave[i] + near_leave[i] 
  = sum{j in 1..vertices_n} ( vertex_entering[i,j]*vertex[j] )
  + enter[i] + near_enter[i] ;

# s.t. letters{i in 1..letters_n} : 
#     sum{j in letter_edges[i]} (int[j] + int_leave[j] + int_enter[j] + ext[j])
#   - faces[letter_face[i]] = 0 ;

solve ;

printf 'ext := [' ;
printf{i in int_n+1..ext_n : ext[i]<>0} '[%d,%.3f],', i, ext[i] ;
printf ']\n';

printf 'leave := [' ;
printf{i in 1..int_n : leave[i]<>0} '[%d,%.3f],', i, leave[i] ;
printf ']\n';
printf 'enter := [' ;
printf{i in 1..int_n : enter[i]<>0} '[%d,%.3f],', i, enter[i] ;
printf ']\n';

printf 'near_leave := [' ;
printf{i in 1..int_n : near_leave[i]<>0} '[%d,%.3f],', i, near_leave[i] ;
printf ']\n';
printf 'near_enter := [' ;
printf{i in 1..int_n : near_enter[i]<>0} '[%d,%.3f],', i, near_enter[i] ;
printf ']\n';

printf 'vertex := [' ;
printf{i in 1..vertices_n : vertex[i]<>0} '[%d,%.3f],', i, vertex[i] ;
printf ']\n';

end ;

