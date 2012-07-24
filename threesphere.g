n := 14;
c := Cartesian(ListWithIdenticalEntries(n,[-1,1]));;
cc := List(c,x->Concatenation(x,x));;
inv := function(v)
  local w,i;
  w := Reversed(v);
  for i in [2..Length(w)-1] do
    w[i] := -w[i];
  od;
  return w;
end;
test := function(v)
  local k;
  k := PositionSublist(v,inv(v{[1..n/2+1]}));
  if k = fail then return false; fi;
  k := PositionSublist(v,inv(v{[k+n/2..k+n]}));
  if k = fail then return false; fi;
  k := PositionSublist(v,inv(v{[k+n/2..k+n]}));
  if k = fail then return false; fi;
  return k;
end;
ccc := List(cc,test);;
Collected(ccc);
Positions(ccc,8);

