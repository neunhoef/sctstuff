# Find STLPs using a linear program with too positively curved vertices as variables.

DeclareInfoClass("InfoSTLP");
SetInfoLevel(InfoSTLP,1);
SetAssertionLevel(1);

# Some utilities:

DeclareOperation("EmptyList", [IsInt, IsList]);
DeclareOperation("LexLeastRotation", [IsList]);

InstallMethod(EmptyList, "for an integer and a string",
  [ IsInt, IsString and IsStringRep ],
  function(len, l) return EmptyString(len); end );

InstallMethod(EmptyList, "for an integer and a plist",
  [ IsInt, IsList and IsPlistRep ],
  function(len, l) return EmptyPlist(len); end );

InstallMethod( LexLeastRotation, "for a list",
  [ IsList ],
  function( l )
    local a,i,j,k,n,nn;
    if IsEmpty(l) then return [ShallowCopy(l),1]; fi;
    n := Length(l);
    a := EmptyList(2*n,l);
    Append(a,l);
    Append(a,l);
    k := 0;
    nn := 2*n;
    while k < nn do
        i := k+1;
        j := k+2;
        while true do
            if j-1-k = n and n mod (j-i) = 0 then
                return [a{[k+1..k+j-i]},n/(j-i)];
            fi;
            if j <= nn then
                if a[i] < a[j] then
                    i := k+1; j := j+1; continue;
                elif a[i] = a[j] then
                    i := i+1; j := j+1; continue;
                fi;
            fi;
            repeat
                k := k + (j-i);
            until k >= i;
            break;
        od;
    od;
    return fail;
  end );

BindGlobal("PongosFamily",NewFamily("PongosFamily"));
DeclareCategory("IsPongo", IsObject);
DeclareRepresentation("IsCayleyPongo", IsPongo and IsPositionalObjectRep,[]);
BindGlobal("CayleyPongoType",NewType(PongosFamily, IsCayleyPongo));

DeclareOperation("PongoMult",[IsPongo,IsObject,IsObject]);
DeclareOperation("IsZero",[IsPongo,IsObject]);
DeclareOperation("IsAccepting",[IsPongo,IsObject]);
DeclareOperation("PongoElements",[IsPongo]);
DeclareOperation("CayleyPongo",[IsList, IsPosInt]);
  # --> takes a list of lists containing the Cayley-Table without 0
  #     and the number of accepting elements, these are [1..nr]
DeclareAttribute("Size",IsPongo);
DeclareProperty("IsRegistrationPongo",IsPongo);
DeclareProperty("IsCancellative",IsPongo);
DeclareOperation("Complement",[IsPongo and IsCancellative,IsObject]);
DeclareOperation("SetElementNames",[IsPongo,IsStringRep]);
DeclareOperation("ElementNames",[IsPongo]);
DeclareOperation("ElementNameTable",[IsPongo]);


# Inverse tables:

BindGlobal("InvTabsFamily",NewFamily("InvTabsFamily"));
DeclareCategory("IsInvTab", IsObject);
DeclareRepresentation("IsPlainInvTabRep",IsInvTab and IsPositionalObjectRep,[]);
BindGlobal("InvTabType",NewType(InvTabsFamily, IsPlainInvTabRep));

DeclareOperation("PlainInvTab", [IsList]);
DeclareOperation("Complement",[IsInvTab, IsObject]);
DeclareOperation("SetElementNames",[IsInvTab,IsStringRep]);
DeclareOperation("ElementNames",[IsInvTab]);
DeclareOperation("ElementNameTable",[IsInvTab]);

DeclareOperation("Cancel",[IsPongo and IsCancellative, IsInvTab, IsList]);
  # Deals with a cyclic word of [PONGO,LETTER] pairs (third argument)
  # Second argument is invtab for letters, letters are [1..n]

#######################################################################
# The implementation starts
#######################################################################

InstallMethod( CayleyPongo, "for a square matrix and an integer",
  [ IsList, IsPosInt ],
  function( M, nr )
    return Objectify(CayleyPongoType, [M,nr]);
  end );

InstallMethod( ViewObj, "for a cayley pongo",
  [ IsCayleyPongo ],
  function( p )
    Print("<cayley pongo with ",Length(p![1])," elements and ",
          p![2]," acceptors");
    if IsBound(p![4]) then
        Print(" with element names \"",p![4],"\"");
    fi;
    Print(">");
  end );

InstallMethod( PongoMult, "for a cayley pongo and two integers",
  [ IsCayleyPongo, IsInt, IsInt ],
  function( p, a, b )
    if a = 0 or b = 0 then return 0; fi;
    return p![1][a][b];
  end );

InstallMethod( IsZero, "for a cayley pongo and an integer",
  [ IsCayleyPongo, IsInt ],
  function( p, a )
    return IsZero(a);
  end );

InstallMethod( IsAccepting, "for a cayley pongo and an integer",
  [ IsCayleyPongo, IsInt ],
  function( p, a )
    return not IsZero(a) and a <= p![2];
  end );

InstallMethod( PongoElements, "for a cayley pongo",
  [ IsCayleyPongo ],
  function( p ) return [1..Length(p![1])]; end );

InstallMethod( Size, "for a cayley pongo",
  [ IsCayleyPongo ],
  function( p ) return Length(p![1]); end );

PongoInverses := function(p,e)
  return Filtered(PongoElements(p), x->IsAccepting(p,PongoMult(p,x,e)) );
end;

InstallMethod( IsRegistrationPongo, "for a cayley pongo",
  [ IsCayleyPongo ],
  function( p )
    local a,acc,b,c,d,e,els,f;
    els := PongoElements(p);
    for a in els do
      for b in els do
        d := PongoMult(p,a,b);
        if not(IsZero(p,d)) then
          for c in els do
            e := PongoMult(p,b,c);
            if not(IsZero(p,e)) then
              f := PongoMult(p,d,c);
              if IsZero(p,f) then
                return false;
              fi;
            fi;
          od;
        fi;
      od;
    od;
    acc := Filtered(els,x->IsAccepting(p,x));
    for a in acc do
      for b in els do
        c := PongoMult(p,a,b);
        if not(IsZero(p,c)) then
          if c <> b then return false; fi;
        fi;
        c := PongoMult(p,b,a);
        if not(IsZero(p,c)) then
          if c <> b then return false; fi;
        fi;
      od;
    od;
    return true;
  end );

InstallMethod( IsCancellative, "for a cayley pongo",
  [ IsCayleyPongo ],
  function( p )
    local a,b,c,complements,els;
    if not(IsRegistrationPongo(p)) then return false; fi;
    els := PongoElements(p);
    complements := [];
    for a in els do
      for b in els do
        c := PongoMult(p,a,b);
        if IsAccepting(p,c) then
          Assert(1,(not(IsBound(complements[a])) or complements[a]=b) and
                   (not(IsBound(complements[b])) or complements[b]=a));
          complements[a] := b;
          complements[b] := a;
        fi;
      od;
      if not(IsBound(complements[a])) then
        return false;
      fi;
    od;
    p![3] := complements;  # for future lookup
    return true;
  end );

InstallMethod( Complement, "for a cancellative cayley pongo, and an integer",
  [ IsCayleyPongo and HasIsCancellative and IsCancellative, IsInt ],
  function(p,x)
    if x = 0 then return fail; fi;
    return p![3][x];
  end );

InstallMethod( Cancel, 
  "for a canc. cayley pongo, an invtab and a cyclic word of pongo/letter pairs",
  [ IsCayleyPongo and IsCancellative, IsPlainInvTabRep, IsList ],
  function( p, invtab, cw)
    local CancelOnce,i;
    CancelOnce := function(pos)
        local a,b,c,ca,pos2,pos3;
        if Length(cw) < 3 then return false; fi;
        pos2 := pos mod Length(cw) + 1;
        pos3 := pos2 mod Length(cw) + 1;
        # Now pos, pos2 and pos3 are three adjacent positions
        a := cw[pos];
        b := cw[pos2];
        c := cw[pos3];
        # First the letters:
        if a[2] <> Complement(invtab,b[2]) then return false; fi;
        # Now the middle pongo element:
        if not(IsAccepting(p,b[1])) then return false; fi;
        # Now the two outer pongo elements:
        ca := PongoMult(p,c[1],a[1]);
        if IsZero(p,ca) then return false; fi;
        cw[pos] := [ca,c[2]];
        Remove(cw,pos2);
        if pos3 > pos2 then
            Remove(cw,pos3-1);
        else
            Remove(cw,pos3);
        fi;
        return true;
    end;
    i := 1;
    while i <= Length(cw) do
        if CancelOnce(i) then
            i := i - 2;
            if i < 1 then i := 1; fi;
        else
            i := i + 1;
        fi;
    od;
    return cw;
  end );

InstallMethod(SetElementNames, "for a cayley pongo and a string",
  [ IsCayleyPongo, IsStringRep ],
  function(p,st)
    local i;
    p![4] := st;
    p![5] := [];
    for i in [1..Length(st)] do
        p![5][IntChar(st[i])] := i;
    od;
  end );

InstallMethod(ElementNames, "for a cayley pongo",
  [ IsCayleyPongo ],
  function( p )
    if IsBound(p![4]) then return p![4];
    else return fail; fi;
  end );

InstallMethod(ElementNameTable, "for a cayley pongo",
  [ IsCayleyPongo ],
  function( p )
    if IsBound(p![5]) then return p![5];
    else return fail; fi;
  end );

InstallMethod(PlainInvTab, "for a plain list of integers",
  [ IsList ],
  function( t )
    local res;
    if not(ForAll(t,IsPosInt)) then
        Error("InvTabs must only contain positive integers");
        return fail;
    fi;
    res := [t];
    return Objectify(InvTabType, res);
  end );

InstallMethod(ViewObj, "for a plain invtab",
  [ IsPlainInvTabRep ],
  function( t )
    Print("<invtab ",t![1]);
    if IsBound(t![2]) then
        Print(" with letter names \"",t![2],"\"");
    fi;
    Print(">");
  end );

InstallMethod(Complement, "for a plain invtab, and a positive int",
  [ IsPlainInvTabRep, IsPosInt ],
  function( t, i )
    return t![1][i];
  end );

InstallMethod(SetElementNames, "for a plain invtab and a string",
  [ IsPlainInvTabRep, IsStringRep ],
  function(t,st)
    local i;
    t![2] := st;
    t![3] := [];
    for i in [1..Length(st)] do
        t![3][IntChar(st[i])] := i;
    od;
  end );

InstallMethod(ElementNames, "for a plain invtab",
  [ IsPlainInvTabRep ],
  function( t )
    if IsBound(t![2]) then return t![2];
    else return fail; fi;
  end );

InstallMethod(ElementNameTable, "for a plain invtab",
  [ IsPlainInvTabRep ],
  function( t )
    if IsBound(t![3]) then return t![3];
    else return fail; fi;
  end );

InstallMethod(\+,[IsInt,IsNegInfinity],function(a,b) return -infinity; end);
InstallMethod(\+,[IsNegInfinity,IsInt],function(a,b) return -infinity; end);
InstallMethod(\+,[IsNegInfinity,IsNegInfinity],
              function(a,b) return -infinity; end);
InstallMethod(\/,[IsNegInfinity,IsInt],function(a,b) return -infinity; end);

BindGlobal("SCTProblemsFamily",NewFamily("SCTProblemsFamily"));
DeclareCategory("IsSCTProblem", IsComponentObjectRep and IsAttributeStoringRep);
DeclareRepresentation("IsSTLPProblem",IsSCTProblem,
  ["pongo","invtab","relators","rewrites","halfedges"]);
BindGlobal("STLPProblemType",NewType(SCTProblemsFamily, IsSTLPProblem));


MakeProblem := function(pongo, invtab, relators, rewrites)
  # Essentially just puts together a record, which it returns
  if not(IsCancellative(pongo)) then
      Error("Analysis only works for cancellative pongos.");
      return fail;
  fi;
  return Objectify(STLPProblemType,
           rec( pongo := pongo, invtab := invtab, relators := relators,
                rewrites := rewrites ));
end;

InstallMethod( ViewObj, "for a tom problem",
  [IsSTLPProblem],
  function(s)
    Print("<tom problem ",Length(s!.relators)," rels");
    if IsBound(s!.halfedges) then
        Print(", ",Length(s!.halfedges)," halfedges");
    fi;
    Print(">");
  end );

InverseRelator := function(s,r)
  local pw,x,y;
  if not(IsCancellative(s!.pongo)) then Error(); fi;
  pw := [];
  y := r.primword[1];
  for x in Reversed(r.primword) do
    Add(pw, [ Complement(s!.pongo,y[1]), Complement(s!.invtab,x[2]) ] );
    y := x;
  od;
  return rec( power := r.power, area := r.area, primword := pw );
end;

RelatorLength := function(r)
  return Length(r.primword) * r.power;
end;

IndexPrimWord := function(r,i)
  return ((i-1) mod Length(r.primword))+1;
end;

ReduceModBase1 := function(x,m)
  return (x-1) mod m + 1;
end;

IsOneCompletable := function(s,e1,e2)
  # Decides whether or not the corner given by two halfedges e1 and e2
  # can be completed to a valency 3 vertex. This involves looking at
  # three pongo elements and two letters to see whether there could be
  # one more edge.
  local L1,L2,he1c,he2,he2c,p,pos,rel;
  he2 := s!.halfedges[e2];
  rel := s!.relators[he2.relator];
  p := rel.primword[he2.start][1];
  he1c := s!.halfedges[s!.halfedges[e1].complement];
  rel := s!.relators[he1c.relator];
  p := PongoMult(s!.pongo,p,rel.primword[he1c.start][1]);
  if IsZero(s!.pongo,p) then return false; fi;
  L1 := rel.primword[IndexPrimWord(rel,he1c.start-1)][2];
  he2c := s!.halfedges[s!.halfedges[e2].complement];
  rel := s!.relators[he2c.relator];
  pos := IndexPrimWord(rel,he2c.start+he2c.length);
  p := PongoMult(s!.pongo,p,rel.primword[pos][1]);
  if not IsAccepting(s!.pongo,p) then return false; fi;
  L2 := rel.primword[pos][2];
  if L2 <> Complement(s!.invtab,L1) then return false; fi;
  return true;
end;



DeclareAttribute("RelatorsPongoElements", IsSTLPProblem);

InstallMethod( RelatorsPongoElements, "for a tom problem",
  [ IsSTLPProblem ],
  function( s )
    local i1,p1,r1,rpe;
    rpe := [];
    for i1 in [1..Length(s!.relators)] do
      r1 := s!.relators[i1];
      for p1 in [1..Length(r1.primword)] do
        AddSet(rpe,r1.primword[p1][1]);
      od;
    od;
    return rpe;
  end );

DeclareAttribute("RelatorsLPLTriples", IsSTLPProblem);

InstallMethod( RelatorsLPLTriples, "for a tom problem",
  [ IsSTLPProblem ],
  function( s )
    local i1,lplt,p1,r1;
    lplt := [];
    for i1 in [1..Length(s!.relators)] do
      r1 := s!.relators[i1];
      for p1 in [1..Length(r1.primword)] do
        AddSet(lplt,[r1.primword[IndexPrimWord(r1,p1-1)][2],
                     r1.primword[p1][1],
                     r1.primword[p1][2]]);
      od;
    od;
    return lplt;
  end );

DeclareOperation("IsTwoCompletable",[IsSTLPProblem,IsObject]);
# The pongo element variant. This checks whether or not a vertex
# can be completed with two more edges. The second argument is
# the pongo element coming from the edges known so far. Note that
# the minimal case is that there is only one edge given and this
# checks whether or not there is a valency 3 vertex with this edge.
# In general, v-2 edges are given, one pongo element comes from the v-1
# pongo elements adjacent to these v-2 edges and the question is whether
# these can be completed to a vertex with two more edges. The necessary
# condition this checks is whether or not some relator contains a pongo
# element which is complementary to the second argument.
#             /
#         p2 /
#  ---------* ?       the horizontal edge is given, thus p1 and p2 known
#         p1 \        this checks whether there is a relator with a ?
#             \       completing this vertex.
# Similarly for more than one given edge.


DeclareOperation("IsTwoCompletable",[IsSTLPProblem,IsObject,IsObject,IsObject]);
# The letter, pongo element, letter variant. This checks whether or not
# a vertex can be completed with two more edges. The second to fourth
# arguments are a letter, a pongo element and another letter. The pongo
# element is the one coming from the edges known so far. Note that
# the minimal case is that there is only one edge given and this checks
# whether or not there is a valency 3 vertex with this edge. In general,
# v-2 edges are given, one pongo element comes from the v-1 pongo
# elements adjacent to these v-2 edges and the question is whether
# these can be completed to a vertex with two more edges. The two
# letters are from the two "outermost" relators on the known edges.
# The necessary and sufficient condition this checks is whether or
# not some relator contains a sequence letter, pongo, letter which is
# complementary to the three arguments given.
#           L2 /
#             / ?
#         p2 /
#  ---------* ?       the horizontal edge is given, thus L1, p1*p2 and L2 are
#         p1 \        known this checks whether there is a relator with ???
#             \ ?     completing this vertex.
#           L1 \
# Similarly for more than one given edge.


InstallMethod( IsTwoCompletable, "for a tom problem and a pongo element",
  [ IsSTLPProblem, IsObject ],
function(s,x)
  local p,rpe;
  rpe := RelatorsPongoElements(s);
  if IsCancellative(s!.pongo) then
     return Complement(s!.pongo,x) in rpe;
  fi;
  for p in PongoInverses(s!.pongo,x) do
    if p in rpe then return true; fi;
  od;
  return false;
end);

InstallMethod( IsTwoCompletable, 
  "for a tom problem, a letter, a pongo element and a letter",
  [ IsSTLPProblem, IsObject, IsObject, IsObject ],
function(s,L1,p,L2)
  if not IsCancellative(s!.pongo) then TryNextMethod(); fi;
  return [Complement(s!.invtab,L1),
          Complement(s!.pongo,p),
          Complement(s!.invtab,L2)] in RelatorsLPLTriples(s);
end);

### Compute Edges ###

ComputeInternalEdges := function(s)
  # Takes a STLP-Problem and computes all internal (half-)edges 
  # avoiding inverse registration.
  # Stores a component "!.halfedges" with the result
  local c,he1,he2,hel,i,i1,i2,j1,j2,l,m,p1,p2,r,r1,r1l,r2,r2l,v;
  Info(InfoSTLP,1,"Computing edges...");

  s!.halfedges := [];
  for i1 in [1..Length(s!.relators)] do
    r1 := s!.relators[i1];
    for i2 in [i1..Length(s!.relators)] do
      r2 := s!.relators[i2];
      for p1 in [1..Length(r1.primword)] do
        for p2 in [1..Length(r2.primword)] do
          # We avoid double counting for i1=i2 later on!
          hel := [];
          r1l := RelatorLength(r1);
          r2l := RelatorLength(r2);
          m := Minimum(r1l,r2l);
          for l in [1..m] do 
            j1 := IndexPrimWord(r1,p1+(l-1));
            j2 := IndexPrimWord(r2,p2-(l-1));
            if r1.primword[j1][2] <> 
               Complement(s!.invtab,r2.primword[IndexPrimWord(r2,j2-1)][2]) then 
              break; 
            fi; 
            c := -1 + l/r1l + l/r2l;
            he1 := rec( relator := i1, start := p1,
                        length := l, contrib := c/2,
                        pongoel := r1.primword[p1][1] );
            he2 := rec( relator := i2, start := IndexPrimWord(r2,p2-l), 
                        length := l, contrib := c/2 );
            he2!.pongoel := r2.primword[he2.start][1];
            if i1 <> i2 or he1.start <= he2.start then
                Add(hel, he1); 
                i := Length(s!.halfedges) + Length(hel);
                if i1=i2 and he1.start = he2.start then
                   he1.complement := i; 
                else 
                   he1.complement := i+1;
                   he2.complement := i;
                   Add(hel, he2);
                fi;
            fi; 
            if not(IsAccepting(s!.pongo,
                     PongoMult(s!.pongo,r1.primword[IndexPrimWord(r1,j1+1)][1],
                               r2.primword[IndexPrimWord(r2,j2-1)][1]))) then
                break;
            fi;
            if (l=m) then hel := []; fi;
          od;
          Append(s!.halfedges, hel);
        od;
      od;
    od;
  od;
  Info(InfoSTLP,1,"Number of internal halfedges: ",Length(s!.halfedges),".");
end;

DoulbeSelfComplementEdges := function(s)
  local i,o,he;

  o := Length(s!.halfedges);
  for i in [1..Length(s!.halfedges)] do
    he := s!.halfedges[i];
    if he.complement=i then
      Add(s!.halfedges, ShallowCopy(he));
      he.complement := Length(s!.halfedges);
    fi;
  od;
  Info(InfoSTLP,1,"Added ",Length(s!.halfedges)-o," complements for self-complement halfedges.");
end;

ComputeBoundaryEdges := function(s)
  # Takes a STLP-Problem and computes all boundary (half-)edges 
  # avoiding those that consume over half a relator.
  # Adds these into the "!.halfedges" component with .complement=0
  local i,j,k,l,r,he;
  Info(InfoSTLP,1,"Computing boundary edges...");

  s!.internal_halfedges_n := Length(s!.halfedges);
  for i in [1..Length(s!.relators)] do
    r := s!.relators[i];
    l := RelatorLength(r);
    for j in [1..Length(r.primword)] do
      for k in [1..Int(l/2)] do
        he := rec( relator := i, start := j, length := k,
                   complement := 0, contrib := -1 + k/l );
        Add(s!.halfedges, he);
      od;
    od;
  od;
  Info(InfoSTLP,1,"Number of boundary halfedges: ",Length(s!.halfedges)-s!.internal_halfedges_n,".");
end;

### Index Edges ###

IndexEdges := function(s)
  # Index the edges by relator, notch type, sorted by length:
  local he,i,start_idx,end_idx,j,n,rel,comp,sorter;
  Info(InfoSTLP,1,"Indexing edges...");
  n := Length(s!.relators);
  start_idx := EmptyPlist(n);
  end_idx := EmptyPlist(n);
  for i in [1..n] do
      start_idx[i] := List([1..Length(s!.relators[i].primword)],j->[]);
      end_idx[i] := List([1..Length(s!.relators[i].primword)],j->[]);
  od;
  for i in [1..Length(s!.halfedges)] do
      he := s!.halfedges[i];
      rel := s!.relators[he.relator];
      Add(start_idx[he.relator][he.start],i);
      j := IndexPrimWord(rel, he.start+he.length);
      Add(end_idx[he.relator][j],i);
  od;
  # Sort indices in length decreasing order:
  comp := function(a,b) 
    return s!.halfedges[a].length > s!.halfedges[b].length;
  end;
  sorter := function(idx)
    for j in [1..Length(idx[i])] do
      Sort(idx[i][j],comp);
    od;
  end;
  for i in [1..n] do
    sorter(start_idx);
    sorter(end_idx);
  od;
  s!.heindex_start := start_idx;
  s!.heindex_end := end_idx;
end;

### Find Curved Vertices ###

Last := function(l)  return l[Length(l)];  end;

HalfEdgePongo := function(s,i)
  local he;
  he := s!.halfedges[i];
  return s!.relators[he.relator].primword[he.start][1];
end;

StartVertexO := function(s,o)
  return rec( outgoing := [o], incoming := [],
     p := HalfEdgePongo(s,o), 
     curvature := 1 + s!.halfedges[o].contrib,
     boundary := s!.halfedges[o].complement=0,
     valency := 1
  );
end;

AddToVertexIOLeft := function(s,v,i,o)
  # Add incoming and outgoing half-edge pair to vertex counter clockwise, 
  # meaning pongo multiplication occurs on the left.
  Assert(2, s!.halfedges[i].complement = o, 
     "AddToVertexIOLeft passed non-complementary edges");
  return rec( 
     incoming := Concatenation([i],v.incoming),
     outgoing := Concatenation([o],v.outgoing),
     p := PongoMult(s!.pongo, HalfEdgePongo(s,o), v.p),
     curvature := v.curvature + s!.halfedges[o].contrib,
     valency := v.valency + 1
  ); 
end;

CompleteExtVertexILeft := function(v,i)
  # A final boundary edge going counter clockwise must be incoming.
  return rec( incoming := Concatenation([i],v.incoming), 
              outgoing := v.outgoing,
              name := v.outgoing, 
              p := v.p, 
              curvature := v.curvature,
              boundary := true, 
              valency := v.valency + 1
      ); 
end;

CompleteIntVertexLeft := function(v,i)
  # Please observe that LexLeastRotation corrupts the correspondence between 
  # in and out.  Ideally, we should obtain the rotation from LexLeastRotation
  # but really we nolonger need this correspondence.
  return rec( incoming := Concatenation([i],v.incoming),
              outgoing := v.outgoing,
              name := LexLeastRotation(v.outgoing), 
              p := v.p, 
              curvature := v.curvature,
              boundary := false, 
              valency := v.valency
      ); 
end;

BuildVertices0 := function(s,curvature,vertex)
  local i,j,he,he_head,he_tail,p1,r,vertices;
  he_head := s!.halfedges[ Last(vertex.outgoing) ];
  he_tail := s!.halfedges[ vertex.outgoing[1] ];
  vertices := [ ];
  for i in s!.heindex_end[he_tail.relator][he_tail.start] do
    he := s!.halfedges[i]; 
    if he.complement=0 then
      if he_head.complement=0 and Length(vertex.outgoing) > 1 then
        Add(vertices, CompleteExtVertexILeft(vertex,i) );
      fi; 
      continue;
    fi; 
    j := he.complement;
    if j > Last(vertex.outgoing) then continue; fi;
    if ( j = Last(vertex.outgoing) and Length(vertex.outgoing) > 2 and
         IsAccepting(s!.pongo,vertex.p) ) then
      Add(vertices, CompleteIntVertexLeft(vertex,i) );
    fi; 
    he := s!.halfedges[j]; 
    if vertex.curvature + he.contrib > curvature then
      r := s!.relators[ he.relator ];
      Append(vertices, BuildVertices0(s,curvature,
           AddToVertexIOLeft(s,vertex,i,j)
      ) );
    fi;
  od;
  return vertices;
end;

Uniqueish := function(old,f)
  local a,b,new;
  if IsEmpty(old) then return []; fi;
  new := [ old[1] ];
  b := old[1];
  for a in old do
    if f(a) <> f(b) then
      Add(new,a);
      b := a;
    fi;
  od;
  return new;
end;

BuildVertices := function(s,curvature)
  local v,vertices;
  Info(InfoSTLP,1,"Finding curved vertices...");
  vertices := [ ];
  for v in [1..Length(s!.halfedges)] do
    if 1 + s!.halfedges[v].contrib > curvature then
      Append(vertices, 
         BuildVertices0(s,curvature,StartVertexO(s,v)) 
      );
    fi; 
  od;
  Sort(vertices, function(a,b) return a.name < b.name; end );
  Uniqueish(vertices, x->x.name );
  Info(InfoSTLP,1,"Number of curved vertices: ",Length(vertices),".");
  return vertices;
end;

### STLP Linear Program ###

ChopBoth := function(s)
  Remove(s,Length(s));
  Remove(s,1);
end;

RawRatList := function(s)
  ChopBoth(s);
  return List(SplitString(s,","),Rat);
end;

RawDeTuple := function(s)
  ChopBoth(s);
  return SplitString(s,",");
end; 

SummationString := function(l,v)
  local j,s;
  s := "";
  for j in [1..Length(l)] do
    if l[j] <> 0 then
      Append(s,Concatenation(PrintString(l[j]), "*",
               v,"[",PrintString(j),"]+"));
    fi;
  od;
  if s="" then return "0"; fi;
  Remove(s,Length(s));
  return s;
end;

Simplex := function(mode,obj,A,op,b)
  local i,j,m,o,r;

  m := Filename(DirectoryTemporary(),"foo.tmp");
  o := OutputTextFile(m,false);
  SetPrintFormattingStatus(o,false);
  PrintTo(o,Concatenation(
     "var v{i in 1..",PrintString(Length(obj)),"} integer >= 0 ;\n"
  ));
  AppendTo(o,mode," obj : ",SummationString(obj,"v")," ;\n");
  for i in [1..Length(A)] do
    AppendTo(o,Concatenation(
        "s.t. c",PrintString(i)," : ",
        SummationString(A[i],"v"),
        op[i],PrintString(b[i])," ;\n" ));
  od;
  AppendTo(o,
      "solve ;\n",
      "printf '[';",
      "printf{i in 1..",PrintString(Length(obj)),"} '%.3f,', v[i];",
      "printf ']\\n';"
  );
  CloseStream(o);

  Info(InfoSTLP,1,"Running Simplex : glpsol -m ",m,"\n");
  r := "";
  o := OutputTextString(r,true);
  Process(DirectoryCurrent(),"/opt/local/bin/glpsol",
          InputTextNone(),o,["-m",m]);
  # Use DirectoriesPackageLibrary(..) in future.
  CloseStream(o);
  Info(InfoSTLP,1,"Simplex returned : ",r,"\n");

  o := rec( feasible := false );
  r := SplitString(r,"\n");
  for i in [1..Length(r)] do
    if r[i] = "OPTIMAL SOLUTION FOUND" then
      o.feasible := true;
      # v.value := ;
    fi;
  od;
  if o.feasible=true then 
    j := r[Length(r)-1];
    RemoveCharacters(j,"[]\n");
    o.param := List(SplitString(j,","),Rat);
  fi;
  return o;
end;


PrintTuple := function(a,b)
  return Concatenation("x",PrintString(a),"y",PrintString(b));
end;

LinearSTLP := function(s)
  local d,i,j,k,o,r,DataV,DataS,Edges,BoundaryLength;

  d := Filename(DirectoryTemporary(),"foo.tmp");
  o := OutputTextFile(d,false);
  SetPrintFormattingStatus(o,false);
  PrintTo(o,"# \n");
  DataV := function(s,v)
    AppendTo(o,s," := ",PrintString(v)," ;\n");
  end;
  DataS := function(s,l)
    AppendTo(o,s," := ",JoinStringsWithSeparator(l," ")," ;\n");
  end;
  DataV("param int_n", s!.internal_halfedges_n );
  DataV("param ext_n", Length(s!.halfedges) );
  DataS("set notches",Concatenation(
    List([1..Length(s!.relators)], 
      r->List([1..RelatorLength(s!.relators[r])],
        j->PrintTuple(r,j)) )
  ));

  Edges := function(n,idx,f)
    local i,r;
    for r in [1..Length(s!.relators)] do
      for i in [1..RelatorLength(s!.relators[r])] do
        DataS(Concatenation(n,"[",PrintTuple(r,i),"]"),Filtered(idx[r][i],f));
      od;
    od;
  end;
  Edges("set int_head_notches",s!.heindex_start,j->j<=s!.internal_halfedges_n);
  Edges("set int_tail_notches",s!.heindex_end,j->j<=s!.internal_halfedges_n);
  Edges("set ext_head_notches",s!.heindex_start,j->j>s!.internal_halfedges_n);
  Edges("set ext_tail_notches",s!.heindex_end,j->j>s!.internal_halfedges_n);

  DataV("param pairs_n",s!.internal_halfedges_n/2);
  k := 1;
  AppendTo(o,"param pairs : 1 2 := ");
  for i in [1..Length(s!.halfedges)] do
    j := s!.halfedges[i].complement;
    if j>i then
  AppendTo(o,"\n            ",PrintString(k)," ",PrintString(i)," ",PrintString(j));
      k := k + 1;
    fi;
  od;
  AppendTo(o," ;\n");

  BoundaryLength := function(he)
    if he.complement=0 then 
      return he.length; # / RelatorLength(s!.relators[he.relator]);
    else return 0; fi;
  end;

  AppendTo(o,"param length := ");
  for i in [1..Length(s!.halfedges)] do
    AppendTo(o, Concatenation(
        "[",PrintString(i),"] ",
        PrintString(s!.halfedges[i].length)," "
    ) );
  od;
  AppendTo(o,";\n");
  AppendTo(o,"\nend ;\n");
  CloseStream(o);

  Info(InfoSTLP,1,"Running Simplex : glpsol -m edge_lp.mp -d ",d,"\n");
  r := "";
  o := OutputTextString(r,true);
  Process(DirectoryCurrent(),"/opt/local/bin/glpsol",
          InputTextNone(),o,["-m","edge_lp.mp","-d",d]);
  # Use DirectoriesPackageLibrary(..) in future.
  CloseStream(o);
  Info(InfoSTLP,1,"Simplex returned : ",r,"\n");
end;

### Testing Utilities ###

DoAll := function(s)
    ComputeInternalEdges(s);
    DoulbeSelfComplementEdges(s);
    ComputeBoundaryEdges(s);
    # RemoveForbiddenEdges(s);
    IndexEdges(s);
    LinearSTLP(s);
end;

# y := []; for i in [1..Length(x)] do if x[i] <> 0. then Add(y,[i,x[i]]); fi; od; y;
# List(y,z->[z[2],s!.halfedges[z[1]]]);



# Sample input:

Rep := function(w,pow)
  local i,res;
  res := [];
  for i in [1..pow] do
      Append(res,w);
  od;
  return res;
end;

ParsePongoLetter := function(pongo,invtab,st)
    # st a string, must be even length and pongo,letter,pongo,letter
    # letter names for pongo and letter are allowed
    # (...)^int is allowed for repetition
    local area,i,inamtab,nextpongo,pair,pnamtab,pow,ran,res,stack,stack2;
    pnamtab := ElementNameTable(pongo);
    inamtab := ElementNameTable(invtab);
    if pnamtab = fail or inamtab = fail then
        Error("need element name tables in pongo and invtab");
        return fail;
    fi;
    if not(IsStringRep(st)) and IsList(st) and Length(st) >= 1 and
       IsStringRep(st[1]) then
        return List(st,x->ParsePongoLetter(pongo,invtab,x));
    fi;
    res := [];
    i := 1;
    stack := [];
    stack2 := [];
    nextpongo := true;
    area := 10;
    while i <= Length(st) do
        if st[i] = '(' then
            if not nextpongo then
                Error("opening bracket only between letter and pongo possible");
                return fail;
            fi;
            Add(stack,Length(res)+1);
        elif st[i] = ')' then
            if Length(stack) = 0 then
                Error("too many closing brackets");
                return fail;
            fi;
            Add(stack2,[Remove(stack)..Length(res)]);
        elif st[i] = '^' then
            if Length(stack2) = 0 then
                Error("no bracket expression before ^");
                return fail;
            fi;
            ran := Remove(stack2);
            # Now read an int:
            i := i + 1;
            pow := 0;
            while i <= Length(st) and st[i] >= '0' and st[i] <= '9' do
                pow := pow * 10 + IntChar(st[i]) - IntChar('0');
                i := i + 1;
            od;
            if pow = 0 then
                Error("power 0 not allowed");
                return fail;
            fi;
            while true do
                pow := pow - 1;
                if pow <= 0 then break; fi;
                Append(res,res{ran});
            od;
            i := i - 1;
        elif st[i] = ':' then
            # Now read an int:
            i := i + 1;
            area := 0;
            while i <= Length(st) and st[i] >= '0' and st[i] <= '9' do
                area := area * 10 + IntChar(st[i]) - IntChar('0');
                i := i + 1;
            od;
            i := i - 1;
        elif nextpongo then
            if not(IsBound(pnamtab[IntChar(st[i])])) then
                Error("not a pongo element: ",st[i]);
            fi;
            pair := [pnamtab[IntChar(st[i])],0];
            nextpongo := false;
        else 
            if not(IsBound(inamtab[IntChar(st[i])])) then
                Error("not an invtab element: ",st[i]);
            fi;
            pair[2] := inamtab[IntChar(st[i])];
            Add(res,pair);
            nextpongo := true;
        fi;
        i := i + 1;
    od;
    res := LexLeastRotation(res);
    return rec( primword := res[1], power := res[2], area := area );
end;

Pretty := function(pongo,invtab,word)
  local i,inams,pnams,res;
  pnams := ElementNames(pongo);
  inams := ElementNames(invtab);
  if pnams = fail or inams = fail then
      Error("need element name tables in pongo and invtab");
      return fail;
  fi;
  res := "";
  for i in [1..Length(word)] do
      Add(res,pnams[word[i][1]]);
      Add(res,inams[word[i][2]]);
  od;
  return res;
end;

pongo := CayleyPongo([[1,2,3],[2,3,1],[3,1,2]],1);
SetElementNames(pongo,"1SR");
invtab := PlainInvTab([1]);
SetElementNames(invtab,"T");

relators := ParsePongoLetter(pongo,invtab,
         ["STSTSTSTRTRTRTSTSTSTRTRTRTRTSTRTSTRT"]);

relators0 := ParsePongoLetter(pongo,invtab,
    ["(ST)^7:10", "(RT)^7:10", "(STRT)^13:10"]);

rewrites := [];

s := MakeProblem(pongo, invtab, relators, rewrites);

free := MakeProblem(pongo, invtab, [], rewrites);


