combine := function(l)
  # takes a list of permutation groups, must be perm reps of the same 
  # gens of the same group
  local gens,hgens,i,ind,j,m,n,pos;
  n := Length(l);
  m := Length(GeneratorsOfGroup(l[1]));
  gens := List([1..m],x->[]);
  pos := 0;
  for i in [1..n] do
    hgens := GeneratorsOfGroup(l[i]);
    if Length(hgens) <> m then Error("buh!"); fi;
    ind := LargestMovedPoint(l[i]);
    for j in [1..m] do
      Append(gens[j],ListPerm(hgens[j],ind)+pos);
    od;
    pos := pos + ind;
  od;
  return Group(List(gens,PermList));
end;

