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


var int{i in 1..int_n} integer >= 0 ;
var int_leave{i in 1..int_n} integer >= 0 ;
var int_enter{i in 1..int_n} integer >= 0 ;
var int_both{i in 1..int_n} integer >= 0 ;
var ext{i in int_n+1..ext_n} integer >= 0 ;


# param faces_n integer ;
# param letters_n integer ;
# param letter_face{1..letters_n} integer ;
# set letter_edges{1..letters_n} ;

# var faces{1..faces_n} integer ;


minimize obj : sum{i in 1..int_n} (int[i] + int_leave[i] + int_enter[i] + int_both[i]) ;

s.t. boundary_length_six : sum{i in int_n+1..ext_n} length[i]*ext[i] = 6 ;

s.t. complement{i in 1..pairs_n} :
    int[pairs[i,1]] + int_leave[pairs[i,1]] + int_enter[pairs[i,1]] 
  = int[pairs[i,2]] + int_leave[pairs[i,2]] + int_enter[pairs[i,2]] ; 

s.t. complement_both{i in 1..pairs_n} :
    int_both[pairs[i,1]] = int_both[pairs[i,2]] ; 

s.t. int_notch{i in notches} : 
    sum{j in int_head_notches[i]} (int[j] + int_leave[j])
  - sum{j in int_tail_notches[i]} (int[j] + int_enter[j]) = 0 ;

s.t. ext_enter_notch{i in notches} : 
    sum{j in ext_head_notches[i]} ext[j]
  - sum{j in int_tail_notches[i]} int_leave[j] 
  - sum{j in int_tail_notches[i]} int_both[j] = 0 ;

s.t. ext_leave_notch{i in notches} : 
    sum{j in int_head_notches[i]} int_enter[j] 
  + sum{j in int_head_notches[i]} int_both[j] 
  - sum{j in ext_tail_notches[i]} ext[j] = 0 ;

# s.t. letters{i in 1..letters_n} : 
#     sum{j in letter_edges[i]} (int[j] + int_leave[j] + int_enter[j] + int_both[j] + ext[j])
#   - faces[letter_face[i]] = 0 ;

# s.t. edge{i in 1..int_n} :
#     int[i] + int_leave[i] + int_enter[i] >= sum{j in 1..vertices_n} edges_by_vertex[i,j] * vertex[j] ;

solve ;
      
printf 'int_pure := [' ;
printf{i in 1..int_n : int[i]<>0} '[%d,%.3f],', i, int[i] ;
printf ']\n';
printf 'int_leave := [' ;
printf{i in 1..int_n : int_leave[i]<>0} '[%d,%.3f],', i, int_leave[i] ;
printf ']\n';
printf 'int_enter := [' ;
printf{i in 1..int_n : int_enter[i]<>0} '[%d,%.3f],', i, int_enter[i] ;
printf ']\n';
printf 'int_both := [' ;
printf{i in 1..int_n : int_both[i]<>0} '[%d,%.3f],', i, int_both[i] ; 
printf ']\n';
printf 'ext_pure := [' ;
printf{i in int_n+1..ext_n : ext[i]<>0} '[%d,%.3f],', i, ext[i] ;
printf ']\n';
# printf 'vertex := [' ;
# printf{i in 1..vertices_n : vertex[i]<>0} '[%d,%.3f],', i, vertex[i] ;
# printf ']\n';

end ;

