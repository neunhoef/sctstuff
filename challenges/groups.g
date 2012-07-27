f := FreeGroup("a","b","c","d");
AssignGeneratorVariables(f);
rels := [Comm(a,b)*Comm(c,d)];
G1 := f/rels;

f := FreeGroup("S","T");
AssignGeneratorVariables(f);
U := S*T;
V := S*S*T;

rels := [T*T,S*S*S,(S*T)^7,(S*T*S*S*T)^13];
G2 := f/rels;

rels := [T*T,S*S*S,((S*T)^4*S*S*T)^2];
G3 := f/rels;

rels := [T*T,S*S*S,U^13,(U*V)^4];
G4 := f/rels;

rels := [T*T,S*S*S,U^7*V^4*U*V^3*U*V^4];
G5 := f/rels;
