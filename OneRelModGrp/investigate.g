i := LowIndexSubgroupsFpGroupIterator(g,12);
while not IsDoneIterator(i) do
h := NextIterator(i);
if Index(g,h) > 0 then
  success := true;
fi;
success := false;
Print(".\c");
od;
h;
Index(g,h);
i := LowIndexSubgroupsFpGroupIterator(g,12);
success := false;
while not IsDoneIterator(i) do
h := NextIterator(i);
if Index(g,h) > 1 then
  success := true;
  break;
fi;
Print(".\c");
od;
Index(g,h);
gg := g;
index := 1;
index := index * Index(g,h);
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
i := LowIndexSubgroupsFpGroupIterator(g,12);
success := false;
while not IsDoneIterator(i) do
h := NextIterator(i);
if Index(g,h) > 1 then
  success := true;
  break;
fi;
Print(".\c");
od;
Index(g,h);
index := index * Index(g,h);
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
RelatorsOfFpGroup(g);
i := LowIndexSubgroupsFpGroupIterator(g,12);
success := false;
while not IsDoneIterator(i) do
h := NextIterator(i);
if Index(g,h) > 1 then
  success := true;
  break;
fi;
Print(".\c");
od;
Index(g,h);
index := index * Index(g,h);
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
RelatorsOfFpGroup(g);
i := LowIndexSubgroupsFpGroupIterator(g,12);
success := false;
while not IsDoneIterator(i) do
h := NextIterator(i);
if Index(g,h) > 1 then
  success := true;
  break;
fi;
Print(".\c");
od;
Index(g,h);
index := index * Index(g,h);
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
RelatorsOfFpGroup(g);
i := LowIndexSubgroupsFpGroupIterator(g,12);
success := false;
while not IsDoneIterator(i) do
h := NextIterator(i);
if Index(g,h) > 1 then
  success := true;
  break;
fi;
Print(".\c");
od;
Index(g,h);
index := index * Index(g,h);
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
RelatorsOfFpGroup(g);
i := LowIndexSubgroupsFpGroupIterator(g,12);
success := false;
while not IsDoneIterator(i) do
h := NextIterator(i);

if Index(g,h) > 1 then
  success := true;
  break;
fi;
Print(".\c");
od;
Index(g,h);
index := index * Index(g,h);
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
RelatorsOfFpGroup(g);
i := LowIndexSubgroupsFpGroupIterator(g,12);
success := false;
while not IsDoneIterator(i) do
h := NextIterator(i);
if Index(g,h) > 1 then
  success := true;
  break;
fi;
Print(".\c");
od;
Index(g,h);
index := index * Index(g,h);
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
RelatorsOfFpGroup(g);
i := LowIndexSubgroupsFpGroupIterator(g,12);
success := false;
while not IsDoneIterator(i) do
h := NextIterator(i);
if Index(g,h) > 1 then
  success := true;
  break;
fi;
Print(".\c");
od;
Index(g,h);
index := index * Index(g,h);
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
RelatorsOfFpGroup(g);
i := LowIndexSubgroupsFpGroupIterator(g,12);
success := false;
while not IsDoneIterator(i) do
h := NextIterator(i);
if Index(g,h) > 1 then
  success := true;
  break;
fi;
Print(".\c");
od;
i;
g;
g := gg;
AbelianInvariants(g);
h := DerivedSubgroup(g);
GeneratorsOfGroup(h);
Index(g,h);
h
;
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
h := DerivedSubgroup(g);
GeneratorsOfGroup(h);
Index(g,h);
;
h;
index := 6;
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
h := DerivedSubgroup(g);
GeneratorsOfGroup(h);
index := index * Index(g,h);
h;
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
h := DerivedSubgroup(g);
GeneratorsOfGroup(h);
index := index * Index(g,h);
h;
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
h := DerivedSubgroup(g);
GeneratorsOfGroup(h);
index := index * Index(g,h);
h;
g := Image(IsomorphismFpGroup(h));
AbelianInvariants(g);
h := DerivedSubgroup(g);
GeneratorsOfGroup(h);
index := index * Index(g,h);
h;
Size(h);
h;
g := gg;
l := LowIndexSubgroupsFpGroup(g,20);
List(l,x->Index(g,x));
Positions(last,20);
HELP("Core");
Core(g,l[11]);
h := last;
Index(g,h);
IdGroup(g/h);
IdGroup(AlternatingGroup(5));
index := 60;
g := Image(IsomorphismFpGroup(h));
RelatorsOfFpGroup(g);
AbelianInvariants(g);
l := LowIndexSubgroupsFpGroup(g,20);
l := LowIndexSubgroupsFpGroup(g,10);
fails{[1..10]};
BinaryGroupNumber(17803);
GroupNumberBinary([0,0,0,1,0,1,1]);
Canonicalise(139);
Position(reps,139);
res[29];
