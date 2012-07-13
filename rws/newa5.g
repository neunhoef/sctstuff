f := FreeGroup("R","S","T");
AssignGeneratorVariables(f);
rels := [R*S,S*S*S,T*T,(S*T)^5];
g := f/rels;
Size(g);
IdGroup(g);
IdGroup(AlternatingGroup(5));
p := Image(IsomorphismPermGroup(g));
infra := InfraStructure("RST","SRT",[["SS","R"],["RR","S"]],
                        CompareByWeights, rec( weights := [17,18,17] ));
r := DehnRewrites(infra,[Rep("ST",5),Rep("RTST",5)]);
rws := RewriteSystem("RST",Concatenation(r.rws));
Display(rws);
r := CheckCyclicEpsilonConfluence2(rws,infinity,rec());
gens := ShallowCopy(GeneratorsOfGroup(p));
gens2 := [["R",gens[1]],["S",gens[2]],["T",gens[3]]];
op := function(x,g)
  return [Concatenation(x[1],g[1]),x[2]*g[2]];
end;
MakeRandomWord := function(n)
  local i,x;
  x := ["",()];
  for i in [1..n] do
      x := op(x,Random(gens2{[1..2]}));
      x := op(x,gens2[3]);
  od;
  return x;
end;

MakeIdWord := function(n)
  local l,s,x,y;
  l := [];
  s := [];
  while true do
    x := MakeRandomWord(n);
    if x[2] in s then
        y := First(l,a->a[2]=x[2]);
        return Concatenation(x[1],Invert(infra,y[1]));
    fi;
    Add(l,x);
    AddSet(s,x[2]);
  od;
end;

