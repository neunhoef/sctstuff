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

ComputeBoundaryEdges := function(s)
  # Takes a STLP-Problem and computes all boundary (half-)edges 
  # avoiding those that consume over half a relator.
  # Adds these into the "!.halfedges" component with .complement=0
  local i,j,k,l,r,he;
  Info(InfoSTLP,1,"Computing boundary edges...");

  for i in [1..Length(s!.relators)] do
    r := s!.relators[i];
    l := RelatorLength(r);
    for j in [1..Length(r.primword)] do
      for k in [1..Floor(l/2)] do
        he := rec( relator := i, start := j, length := k,
                   complement := 0, contrib := -1 + k/l );
        Add(s!.halfedges, he);
      od;
    od;
  od;
  Info(InfoSTLP,1,"Number of boundary halfedges: ",Length(s!.halfedges),".");
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
  return s!.realtors[he.relator].primword[he.start][1];
end;

StartVertexO := function(s,o)
  return rec( outgoing := [o], incoming := [],
     p := HalfEdgePongo(s,o), 
     curvature := 1 + s!.halfedges[o].contrib
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
     curvature := v.curvature + s!.halfedges[o].contrib 
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
      Add(vertices, CompleteIntVertexLeft(vertex,i,j) );
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
  return vertices;
end;

### STLP Linear Program ###

ChopBoth := function(s)
  Remove(s,Length(s));
  Remove(s,1);
end;

RawRatList := function(s)
  ChopBoth(s);
  return List(SplitString(s),Rat);
end;

RawDeTuple := function(s)
  ChopBoth(s);
  return SplitString(s,",");
end;

Simplex := function(mode,obj,A,op,b)
  local i,o,p,r;
  p := Concatenation(mode," (", PrintString(), ") ([ ");
  for i in [1..Length(A)] do
    Append(p, PrintString(A[i]) );
    Append(p, " :" );
    Append(p, op[i] );
    Append(p, ": " );
    Append(p, PrintString(b[i]) );
  od;
  Append(p, " ]) []");
  r := "";
  o := OutputTextString(r,true);
  Process(DirectoryCurrent(),"simplex",InputTextNone(),o,p);
  CloseStream(o);
  # Use DirectoriesPackageLibrary(..) in future.
  r := SplitString(r," ");
  o := RawDeTuple(r[2]);
  return rec( status := r[1], value := Rat(o[1]), param := RawRatList(o[2]) );
end;

LinearSTLP := function(s,curvature)
  local r,c,he,obj,A,Afaces,Aeuler,op,b,index,i,j,k,vertices,v;
  vertices := BuildVertices(s,curvature);
  c := Length(vertices) + Length(s!.relators); 
  r := Length(s!.halfedges) + 1; 
  index := []; 
  for i in [1..Length(s!.relators)] do
    index[i] := r; 
    r := r + Length(s!.relators[i].primword);
  od; 
  A := NullMat(r,c);   # equations x variables
  Aeuler := ListWithIdenticalEntries(c,0);
  Afaces := ListWithIdenticalEntries(c,0);
  obj := ListWithIdenticalEntries(c,0);
  for i in [1..Length(vertices)] do
    if vertices[i].valency then
      Aeuler[i] := -1 + 1/vertices[i].valency;
    fi; 
    for v in vertices[i].outgoing do
      A[v][i] := A[v][i] - 1; 
      he := s!.halfedges[v]; 
      for j in [1..he.length] do
        k := index[he.relator] + 
               IndexPrimWord(s!.relators[he.relator], he.start+j);
        A[k][i] := A[k][i] + 1; 
      od; 
    od; 
    for v in vertices[i].incoming do
      A[v][i] := A[v][i] + 1;
      # We'll skip counting outgoing half edges in the relator counts
    od;
    if vertices[i].boundary=true then
      j := vertices[i].outgoing[1];
      he := s!.halfedges[j];
      obj[j] := obj[j] + he.length;
    fi;
  od;
  for i in [1..Length(s!.relators)] do
    Afaces[Length(vertices)+i] := 1;
    Aeuler[Length(vertices)+i] := 1;
    k := s!.relators[i];
    for j in [1..Length(k.primword)] do
      A[index[i]+j][Length(vertices)+i] := -k.power;
    od;
  od;
  b := ListWithIdenticalEntries(r,0);
  op := ListWithIdenticalEntries(r,"=");
  Append(A, [Aeuler, Afaces]);
  Append(b, [1, 1]);
  Append(op, ["=", "<="]);
  return Simplex("Minimize",obj,A,op,b);
end;

### Testing Utilities ###

DoAll := function(s)
    ComputeEdges(s);
    RemoveForbiddenEdges(s);
    IndexEdges(s);
    InitCornerData(s);
    Sunflower(s,flowerlimit,timeout);
    RemoveForbiddenSunflowers(s);
    Poppy(s);
    RemoveForbiddenPoppies(s);
    FindNewRewrites(s);
end;




pongo := CayleyPongo([[1,2,3],[2,3,1],[3,1,2]],1);
SetElementNames(pongo,"1SR");
invtab := PlainInvTab([1]);
SetElementNames(invtab,"T");

rels := ParsePongoLetter(pongo,invtab,
         ["(ST)^7:10",
          "(RT)^7:10",
          "(STRT)^13:10"]);
rewrites := [];

MakeProblem := function(pongo, invtab, relators, rewrites);


