LoadPackage("orb");
m12 := DehnRewriteSystem("Bab","baB",["bbb",Rep("ab",11),Rep("ababaB",6)]);
f := FreeGroup("a","b");
AssignGeneratorVariables(f);
rels := [a*a,b*b*b,(a*b)^11,Comm(a,b)^6,(a*b*a*b*a*b^-1)^6];
g := f/rels;
p := Image(IsomorphismPermGroup(g));
gens := ShallowCopy(GeneratorsOfGroup(p));
Add(gens,gens[2]^-1);
gens2 := [["a",gens[1]],["b",gens[2]],["B",gens[3]]];
op := function(x,g)
  return [Concatenation(x[1],g[1]),x[2]*g[2]];
end;
hf := HashFunctionForStrings;
hashlen := NextPrimeInt(100000000);
words := [];
looker := function(o,x)
  if not(IsOne(x[2])) then return false; fi;
  if Length(Reduce(m12,CyclicWord(x[1]))) = 0 then
    #Print(x," is OK\n");
    Add(words,x[1]);
    return false;
  fi;
  Print(x," is bad\n");
  return true;
end;

#o := Orb(gens2,["",()],op,rec( hashfunc := rec(func := hf, data := hashlen), 
#         hashlen := hashlen, report := 100000, eqfunc := \=,
#         lookingfor := looker));
#Enumerate(o);

o2 := Orb(gens,(),OnRight,rec(schreier := true));
Enumerate(o2);

x := ["",()];
for i in [1..30] do x := op(x,Random(gens2)); od;
word := TraceSchreierTreeForward(o2,Position(o2,x[2]));
y := ["",()];
for i in word do y := op(y,gens2[i]); od;

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


# CyclicWord("BaBaBababaBaBaBababaBabaBaBabaBababaBabaBabaBaBaBababaBabaBabaBabaBabaBabaBaBabaBabababaBababa") kills it

