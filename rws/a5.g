f := FreeGroup("a","b");
AssignGeneratorVariables(f);
rels := [a^2,b^3,(a*b)^5];
g := f/rels;
Size(g);
IdGroup(g);
IdGroup(AlternatingGroup(5));
p := Image(IsomorphismPermGroup(g));
rws := DehnRewrites1("Bab","baB",["bbb","ababababab"]);
rws := RewriteSystem(rws.alph,rws.ialph,rws.rws);
Display(rws);
r := CheckCyclicEpsilonConfluence(rws,infinity);
gens := ShallowCopy(GeneratorsOfGroup(p));
Add(gens,gens[2]^-1);
gens2 := [["a",gens[1]],["b",gens[2]],["B",gens[3]]];
op := function(x,g)
  return [Concatenation(x[1],g[1]),x[2]*g[2]];
end;
MakeRandomWord := function(n)
  local i,x;
  x := ["",()];
  for i in [1..n] do
      x := op(x,gens2[1]);
      x := op(x,Random(gens2{[2..3]}));
  od;
  return x;
end;

inv := function(w) return Invert(Set("Bab"),"baB",w); end;

MakeIdWord := function(n)
  local l,s,x,y;
  l := [];
  s := [];
  while true do
    x := MakeRandomWord(n);
    if x[2] in s then
        y := First(l,a->a[2]=x[2]);
        return Concatenation(x[1],inv(y[1]));
    fi;
    Add(l,x);
    AddSet(s,x[2]);
  od;
end;

