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

NormalFinder := function(g)
  local found,h,inds,l,limit,ll,minpos,n,poss;
  h := g;
  repeat
      limit := 6;
      repeat
          limit := limit + 6;
          Print("Finding low index subgroups up to index ",limit,"...\n");
          l := LowIndexSubgroupsFpGroup(h,limit);
          l := Filtered(l,x->IsNormal(g,x) and Index(h,x) > 1);
      until Length(l) > 0;
      Print("Found ",Length(l)," normal subgroups in G.\n");
      ll := List(l,x->IsomorphismFpGroupByGenerators(x,GeneratorsOfGroup(x)));
      found := List(ll,x->HasSize(Image(x)) and Size(Image(x)) = infinity and
                          Set(AbelianInvariants(Image(x))) = [0] and
                          IsAbelian(Image(x)));
      poss := Positions(found,true);
      if Length(poss) > 0 then
          l := l{poss};
          ll := ll{poss};
          inds := List(l,x->Index(g,x));
          minpos := Position(inds,Minimum(inds));
          n := l[minpos];
          Print("Taking normal subgroup of index ",inds[minpos]," in G.\n");
          return rec( g := g, n := n, isoimg := Image(ll[minpos]),
                      iso := ll[minpos], epi := FactorCosetAction(g,n) );
      fi;
      inds := List(l,x->Index(g,x));
      minpos := Position(inds,Minimum(inds));
      h := l[minpos];
      Print("Going to normal subgroup of index ",inds[minpos],"...\n");
  until false;
end;

ComputeActionOnNormalSubgroup := function(r,gens)
  local dim,gensact,guck,i,mat,row,x,y;
  gensact := [];
  dim := Length(GeneratorsOfGroup(r.isoimg));
  for x in gens do
    mat := [];
    for y in GeneratorsOfGroup(r.n) do
      row := 0*[1..dim];
      guck := ExtRepOfObj(ImageElm(r.iso,x^-1*y*x));
      for i in [1,3..Length(guck)-1] do
        row[guck[i]] := row[guck[i]] + guck[i+1];
      od;
      Add(mat,row);
    od;
    Add(gensact,mat);
  od;
  return gensact;
end;

FindStructure := function(r)
  # Takes a result of NormalFinder
  local x;
  r.structurefinite := StructureDescription(Image(r.epi));
  r.gensact := ComputeActionOnNormalSubgroup(r,GeneratorsOfGroup(r.g));
  Print("Structure of finite quotient of order ", Size(Image(r.epi))," is ",
        r.structurefinite,"\n");
  Print("Action on free abelian normal subgroup:\n");
  for x in r.gensact do
    PrintArray(x);
  od;
end;
