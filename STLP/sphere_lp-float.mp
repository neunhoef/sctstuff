param int_n integer ;
param ext_n integer ;

# set notches ;
# set int_head_notches{i in notches} default { } ;
# set int_tail_notches{i in notches} default { } ;
# set ext_head_notches{i in notches} default { } ;
# set ext_tail_notches{i in notches} default { } ;

param pairs_n integer ;
param pairs{i in 1..pairs_n,1..2} integer ;

param length{1..ext_n} integer ;

param vertices_n integer ;
set vertex_heads{1..vertices_n} dimen 2 ;
set vertex_tails{1..vertices_n} dimen 2 ;

param faces_n integer ;
param face_length_n integer ;
param face_power{1..faces_n} ;
set vertex_by_letter{1..faces_n,1..face_length_n} dimen 2 ;


var vertex{1..vertices_n} >= 0 ;
var faces{1..faces_n} >= 0 ;


minimize obj : sum{i in 1..vertices_n} vertex[i] ;

# s.t. nontrivial : sum{i in 1..vertices_n} vertex[i] >= 1 ;

param vertex_valencies{v in 1..vertices_n} :=
    sum {(k,n) in vertex_heads[v]} n ;
s.t. euler : 
    sum{f in 1..faces_n} faces[f] 
  + sum{v in 1..vertices_n} (1 - vertex_valencies[v]/2) * vertex[v]
  = 2 ;

s.t. edge{i in 1..int_n} : 
    sum{v in 1..vertices_n} 
    ( sum{(k,n) in vertex_tails[v]} if k=i then n*vertex[v] else 0 )
  = sum{v in 1..vertices_n} 
    ( sum{(k,n) in vertex_heads[v]} if k=i then n*vertex[v] else 0 ) ; 

s.t. letters{i in 1..faces_n,j in 1..face_length_n} :
    sum{(k,n) in vertex_by_letter[i,j]} n*vertex[k] = faces[i] ; 

solve ;

param f symbolic default "results.g";

printf 'vertex := [' >>f ;
printf{i in 1..vertices_n : vertex[i]<>0} '[%d,%.3f],', i, vertex[i] >>f ;
printf ']\n' >>f ;

end ;

