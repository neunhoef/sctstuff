
# For the released GAP:

InstallMethod(ViewString, "for integer", [IsInt], function(n)
  local mb, l, start, trail;
  mb := UserPreference("MaxBitsIntView");
  if not IsSmallIntRep(n) and mb <> fail and
      mb > 64 and Log2Int(n) > mb then
    if n < 0 then
      l := LogInt(-n, 10);
      trail := String(-n mod 1000);
    else
      l := LogInt(n, 10);
      trail := String(n mod 1000);
    fi;
    start := String(QuoInt(n, 10^(l-2)));
    while Length(trail) < 3 do
      trail := Concatenation("0", trail);
    od;
    return Concatenation("<integer ",start,"...",trail," (",
                         String(l+1)," digits)>");
  else
    return String(n);
  fi;
end);

DebugRunning := false;

DeclareGlobalFunction("Debug");

InstallGlobalFunction( Debug,
  function(arg)
    local c,kb;
    if DebugRunning then return; fi;
    for c in arg do ViewObj(c); od;
    Print("\nDebug:\c");
    kb := InputTextUser();
    c := CharInt(ReadByte(kb));
    Print(c,"\n");
    if c = 'q' then Error(); fi;
    if c = 'r' then DebugRunning := true; fi;
  end);


LoadPackage("io");
LoadPackage("orb");

# This implements what is laid out on a sheet of paper in my notebook.
# It verifies an officer called "Tom" which is based on corner values.

DeclareInfoClass("InfoTom");
SetInfoLevel(InfoTom,1);
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
DeclareRepresentation("IsTomProblem",IsSCTProblem,
  ["pongo","invtab","relators","rewrites","halfedges"]);
BindGlobal("TomProblemType",NewType(SCTProblemsFamily, IsTomProblem));


MakeTomProblem := function(pongo, invtab, relators, rewrites)
  # Essentially just puts together a record, which it returns
  if not(IsCancellative(pongo)) then
      Error("Officer Tom analysis only works for cancellative pongos.");
      return fail;
  fi;
  return Objectify(TomProblemType,
           rec( pongo := pongo, invtab := invtab, relators := relators,
                rewrites := rewrites ));
end;

InstallMethod( ViewObj, "for a tom problem",
  [IsTomProblem],
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



DeclareAttribute("RelatorsPongoElements", IsTomProblem);

InstallMethod( RelatorsPongoElements, "for a tom problem",
  [ IsTomProblem ],
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

DeclareAttribute("RelatorsLPLTriples", IsTomProblem);

InstallMethod( RelatorsLPLTriples, "for a tom problem",
  [ IsTomProblem ],
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

DeclareOperation("IsTwoCompletable",[IsTomProblem,IsObject]);
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


DeclareOperation("IsTwoCompletable",[IsTomProblem,IsObject,IsObject,IsObject]);
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
  [ IsTomProblem, IsObject ],
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
  [ IsTomProblem, IsObject, IsObject, IsObject ],
function(s,L1,p,L2)
  if not IsCancellative(s!.pongo) then TryNextMethod(); fi;
  return [Complement(s!.invtab,L1),
          Complement(s!.pongo,p),
          Complement(s!.invtab,L2)] in RelatorsLPLTriples(s);
end);

ComputeEdges := function(s)
  # Takes a Tom-Problem and computes all (half-)edges avoiding inverse
  # registration.
  # Stores a component "!.halfedges" with the result
  local c,cppa,he1,he2,hel,i,i1,i2,j1,j2,l,m,nppa,p1,p2,r,r1,r1l,r2,r2l,v;
  Info(InfoTom,1,"Computing edges...");

  s!.halfedges := [];
  for i1 in [1..Length(s!.relators)] do
    r1 := s!.relators[i1];
    for i2 in [i1..Length(s!.relators)] do
      r2 := s!.relators[i2];
      for p1 in [1..Length(r1.primword)] do
        for p2 in [1..Length(r2.primword)] do
          # We avoid away double counting for i1=i2 later on!
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
            he1 := rec( relator := i1, start := p1, length := l,
                        pongoel := r1.primword[p1][1] );
            he2 := rec( relator := i2, start := IndexPrimWord(r2,p2-l), 
                        length := l );
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
  Info(InfoTom,1,"Number of halfedges: ",Length(s!.halfedges),".");
end;

CanYouDoThisWithSmallerArea := function(s,cw,areabound)
  # Use rewrites to check whether or not there is a diagram with this
  # cw as beach boundary word and area less than areabound. Uses the
  # rewrites and recursion to either answer fail if it cannot do it
  # better or an area value < areabound if it could do it better.

  # This is a rather crude first hack at it, we simply try all rewrites
  # in all possible places, provided curvature - 1/2 relative area - 1/2 
  # relative length >= 0 (using goes up and stays up on the Greendlinger
  # subsets.

  local area,count,i,len,match,n,newcw,newcw2,p,poscw,posrel,r,rel,rewr;

  if areabound <= 0 then return fail; fi;
  Cancel(s!.pongo,s!.invtab,cw);
  if Length(cw) = 0 then return 0; fi;
  # Now see if it is equal to one of the relators with less area:
  for r in [1..Length(s!.relators)] do
      rel := s!.relators[r];
      len := Length(rel.primword)*rel.power;
      if rel.area < areabound and len = Length(cw) then
          for n in [1..Length(rel.primword)] do
              posrel := n;
              poscw := 1;
              count := 0;
              while count < len do
                  if not IsAccepting(s!.pongo,PongoMult(s!.pongo,cw[poscw][1],
                                     rel.primword[posrel][1])) then
                      break;
                  fi;
                  poscw := ReduceModBase1(poscw-1,len);
                  if cw[poscw][2] <> 
                     Complement(s!.invtab,rel.primword[posrel][2]) then
                      break;
                  fi;
                  count := count + 1;
                  posrel := IndexPrimWord(rel,posrel+1);
              od;
              if count >= len then
                  return rel.area;
              fi;
          od;
      fi;
  od;

  for r in [1..Length(s!.rewrites)] do
      # Try all rewrites
      rewr := s!.rewrites[r];
      rel := s!.relators[rewr.relator];
      if rel.area < areabound and
         rewr.length <= Length(cw) and
         2*rewr.curv >= rel.area/areabound + rewr.length/Length(cw) then
          for p in [1..Length(cw)] do
              # Try all positions to apply rewrite
              poscw := ReduceModBase1(p-1,Length(cw));
              posrel := rewr.notchtype;
              match := 0;
              while true do   # will be left by break
                  if cw[poscw][2] <> 
                     Complement(s!.invtab,rel.primword[posrel][2]) then
                      match := false; break;
                  fi;
                  match := match+1;   # number of matched letters
                  posrel := IndexPrimWord(rel,posrel+1);
                  if match >= rewr.length then
                      match := true; break;
                  fi;
                  if not(IsAccepting(s!.pongo,
                             PongoMult(s!.pongo,cw[poscw][1],
                                               rel.primword[posrel][1]))) then
                      match := false;
                      break;
                  fi;
                  poscw := ReduceModBase1(poscw-1,Length(cw));
              od;
              if match then
                  # Now rewrite and recurse:
                  # First the unchanged part:
                  if p > poscw then
                    newcw := cw{Concatenation([p+1..Length(cw)],[1..poscw-1])};
                  else    # p <= poscw, equality possible!
                    newcw := cw{[p+1..poscw-1]};
                  fi;
                  # Now the replacement:
                  newcw2 := EmptyPlist(RelatorLength(rel)-rewr.length+1);
                  Add(newcw2,[PongoMult(s!.pongo,rel.primword[posrel][1],
                                                cw[poscw][1]),
                              Complement(s!.invtab,rel.primword[posrel][2])]);
                  for i in [1..RelatorLength(rel)-rewr.length-1] do
                      posrel := IndexPrimWord(rel,posrel+1);
                      Add(newcw2,ShallowCopy(rel.primword[posrel]));
                  od;
                  posrel := IndexPrimWord(rel,posrel+1);
                  Assert(1,posrel = rewr.notchtype);
                  Add(newcw2,[PongoMult(s!.pongo,cw[p][1],
                                                rel.primword[posrel][1]),
                              cw[p][2]]);
                  Append(newcw,newcw2);
                  area := CanYouDoThisWithSmallerArea(s,newcw,
                                      areabound-rel.area);
                  if area <> fail then
                      return area+rel.area;
                  fi;
              fi;
          od;
      fi;
  od;
  return fail;
end;

HamburgerSurf := function(s,halfedge)
  # Makes the surf of the hamburger of the edge consisting of halfedge
  # and its complement.
  local he1,he2,i,pair,pos1,pos2,rel1,rel2,surf;
  he1 := s!.halfedges[halfedge];
  rel1 := s!.relators[he1.relator];
  he2 := s!.halfedges[he1.complement];
  rel2 := s!.relators[he2.relator];

  pos1 := he1.start;
  pos2 := IndexPrimWord(rel2,he2.start + he2.length);
  surf := [];
  pair := [Complement(s!.pongo,
                      PongoMult(s!.pongo,rel2.primword[pos2][1],
                                        rel1.primword[pos1][1])),0];
  pos1 := IndexPrimWord(rel1,pos1-1);
  pair[2] := Complement(s!.invtab,rel1.primword[pos1][2]);
  Add(surf,pair);
  for i in [1..Length(rel1.primword)*rel1.power-he1.length-1] do
      pair := [Complement(s!.pongo,rel1.primword[pos1][1]),0];
      pos1 := IndexPrimWord(rel1,pos1-1);
      pair[2] := Complement(s!.invtab,rel1.primword[pos1][2]);
      Add(surf,pair);
  od;
  pos2 := he2.start;
  pair := [Complement(s!.pongo,
                      PongoMult(s!.pongo,rel1.primword[pos1][1],
                                        rel2.primword[pos2][1])),0];
  pos2 := IndexPrimWord(rel2,pos2-1);
  pair[2] := Complement(s!.invtab,rel2.primword[pos2][2]);
  Add(surf,pair);
  for i in [1..Length(rel2.primword)*rel2.power-he2.length-1] do
      pair := [Complement(s!.pongo,rel2.primword[pos2][1]),0];
      pos2 := IndexPrimWord(rel2,pos2-1);
      pair[2] := Complement(s!.invtab,rel2.primword[pos2][2]);
      Add(surf,pair);
  od;
  return surf;
end;

RemoveForbiddenEdges := function(s)
  # Removes (half-)edges which are forbidden by the rewrites given.
  local area,e,he1,he2,i,newnumbers,pair,pos1,pos2,rel1,rel2,surf,tokeep,toremove;
  Info(InfoTom,1,"Removing forbidden (half-)edges...");
  toremove := [];
  for e in [1..Length(s!.halfedges)] do
      he1 := s!.halfedges[e];
      rel1 := s!.relators[he1.relator];
      he2 := s!.halfedges[he1.complement];
      rel2 := s!.relators[he2.relator];
      surf := HamburgerSurf(s,e);
      area := CanYouDoThisWithSmallerArea(s,surf,rel1.area+rel2.area);
      if area <> fail then
          AddSet(toremove,e);
          AddSet(toremove,he1.complement);
      fi;
  od;
  tokeep := Difference([1..Length(s!.halfedges)],toremove);
  newnumbers := 0*[1..Length(s!.halfedges)];
  for i in [1..Length(tokeep)] do
      newnumbers[tokeep[i]] := i;
  od;
  for i in [1..Length(toremove)] do
      newnumbers[toremove[i]] := i;
  od;
  s!.halfedgesremoved := s!.halfedges{toremove};
  s!.halfedges := s!.halfedges{tokeep};
  for i in [1..Length(s!.halfedges)] do
      s!.halfedges[i].complement := newnumbers[s!.halfedges[i].complement];
  od;
  for i in [1..Length(s!.halfedgesremoved)] do
      s!.halfedgesremoved[i].complement := 
         newnumbers[s!.halfedgesremoved[i].complement];
  od;
  Info(InfoTom,1,"Have removed ",Length(toremove)," halfedges.");
end;

IndexEdges := function(s)
  # Index the edges by relator, notch type, sorted by length:
  local he,i,index,j,n,rel;
  Info(InfoTom,1,"Indexing edges...");
  n := Length(s!.relators);
  index := EmptyPlist(n);
  for i in [1..n] do
      index[i] := List([1..Length(s!.relators[i].primword)],j->[]);
  od;
  for i in [1..Length(s!.halfedges)] do
      he := s!.halfedges[i];
      rel := s!.relators[he.relator];
      Add(index[he.relator][he.start],i);
  od;
  # Sort indices in length decreasing order:
  for i in [1..Length(index)] do
    for j in [1..Length(index[i])] do
      Sort(index[i][j],function(a,b) 
                         return s!.halfedges[a].length > s!.halfedges[b].length;
                       end);
    od;
  od;
  s!.heindex := index;
end;

AddCornerException := function(s,p,c)
  # Just a stub to be replaced further down
  # p=[e1,e2] can either already be an exception or not.
  # if p is an integer, it is a corner number
end;

#$$$ This function initialises the exceptions data structures for the
# corner values. Corner values are integers between 0 and circle/2 
# and corner value $(c$) actually means $(c/circle$). This function
# makes sure that all corners for which the average of the two relative
# lengths of the two edges is greater than the default corner value.
# This is needed for the sunflower algorithm. If the argument 
# mode is equal to the string <C>$"sunflowershappy$"</C> then the actual 
# corner value for these corners is chosen such that there are no
# sunflowers, this is good to find some poppies. If the argument mode
# is equal to the string <C>$"default$"</C> then all values are set to
# default values, this is good to find some sunflowers.
InitCornerData := function(s,circle,mode)
  # Initialise the data structures for corner exception lists
  local e1,endpos,he1,i,ind,len1,modebool,r,rel;
  Info(InfoTom,1,"Initialising corner data structures mode=",mode,"...");

  # A corner is a certain pair of halfedges [e1,e2].
  # Curvature is stored in units of 1/circle, if we mention 0 <= c <= 1
  # in comments we mean c/circle.
  # Every corner value is 1/6 or 1/4, unless it is an exception.
  # It is 1/6 if there is a vertex of valency 3 containing this corner
  # and otherwise 1/4.
  # We maintain a list of exceptional corners "!.cornleft" and
  # "!.cornright" and a hash table "!.cornhash" to find the number of a
  # corner [e1,e2]. The exceptional values are then stored in "!.cornval"
  # which is a list of the same length as "!.cornleft".
  # To find the exceptional corners with left hand side e1 we keep
  # in "!.cornindex[e1]" a list of all corner numbers of the [e1,e2].
  s!.cornleft := EmptyPlist(1000);
  s!.cornright := EmptyPlist(1000);
  s!.cornval := EmptyPlist(1000);
  s!.cornindex := List([1..Length(s!.halfedges)],i->[]);
  s!.cornhash := HTCreate(fail,rec(hashlen := NextPrimeInt(10000),
                                   forflatplainlists := true));
  s!.circle := circle;
  if mode = "default" then
      modebool := true;
  elif mode = "sunflowershappy" then
      modebool := false;
  else
      Error("mode must be \"default\" or \"sunflowershappy\"");
  fi;

  # This also needs to find all corners with average relative length greater
  # than the default corner value to put them on the exception list.
  for e1 in [1..Length(s!.halfedges)] do
      he1 := s!.halfedges[e1];
      rel := s!.relators[he1.relator];
      len1 := he1.length*circle/(RelatorLength(rel)*2);
      i := 1;
      endpos := IndexPrimWord(rel,he1.start+he1.length);
      ind := s!.heindex[he1.relator][endpos];
      for i in [1..Length(ind)] do
          r := len1 + s!.halfedges[ind[i]].length*circle/(RelatorLength(rel)*2);
          if 6 * r <= circle then break; fi;
          if IsOneCompletable(s,e1,ind[i]) then
              # Default value would be 1/6
              if modebool then
                  AddCornerException(s,[e1,ind[i]],QuoInt(circle,6));
              else
                  AddCornerException(s,[e1,ind[i]],Int(r));
              fi;
          elif 4 * r > circle then
              # Default value would be 1/4
              if modebool then
                  AddCornerException(s,[e1,ind[i]],QuoInt(circle,4));
              else
                  AddCornerException(s,[e1,ind[i]],Int(r));
              fi;
          fi;
      od;
  od;
end;

AddCornerException := function(s,p,c)
  # p=[e1,e2] can either already be an exception or not.
  # if p is an integer, it is a corner number
  local pos;
  if IsInt(p) then
    s!.cornval[p] := c;
  else
    pos := HTValue(s!.cornhash,p);
    if pos = fail then
      Add(s!.cornleft,p[1]);
      Add(s!.cornright,p[2]);
      pos := Length(s!.cornleft);
      Add(s!.cornindex[p[1]],pos);
      HTAdd(s!.cornhash,ShallowCopy(p),pos);
    fi;
    s!.cornval[pos] := c;
  fi;
end;

LookupCornerValue := function(s,p)
  local he1,he2,p1,p2,pos,rel1,rel2;
  if IsInt(p) then
    return s!.cornval[p];
  fi;
  pos := HTValue(s!.cornhash,p);
  if pos <> fail then
    return s!.cornval[pos];
  fi;
  # Now the default values:
  he1 := s!.halfedges[s!.halfedges[p[1]].complement];
  rel1 := s!.relators[he1!.relator];
  p1 := he1.start;
  he2 := s!.halfedges[s!.halfedges[p[2]].complement];
  rel2 := s!.relators[he2!.relator];
  p2 := IndexPrimWord(rel2,he2.start+he2.length-1);
  if IsOneCompletable(s,p[1],p[2]) then
      return s!.circle/6;
  else 
      return s!.circle/4;
  fi;
end;

IsExceptionalCorner := function(s,p)
  local pos;
  pos := HTValue(s!.cornhash,p);
  return pos <> fail;
end;

ExportExceptions := function(s)
  return rec( cornleft := ShallowCopy(s!.cornleft),
              cornright := ShallowCopy(s!.cornright),
              cornval := ShallowCopy(s!.cornval),
              cornindex := ShallowCopy(s!.cornindex),
              cornhash := StructuralCopy(s!.cornhash) );
end;

ImportExceptions := function(s,r)
  s!.cornleft := ShallowCopy(r.cornleft);
  s!.cornright := ShallowCopy(r.cornright);
  s!.cornval := ShallowCopy(r.cornval);
  s!.cornindex := ShallowCopy(r.cornindex);
  s!.cornhash := StructuralCopy(r.cornhash);
  Unbind(s!.sunflowers);
  Unbind(s!.poppies);
end;

Sunflower := function(r)
  # Find all positively curved sunflowers.
  local DoStep,Y,c,ce1e2,circle,co,cornindex,cornright,cornval,d,e,e1,e2,
        ee,halfedges,he,he1,he2,hee,heindex,j,k,kk,len,n,pos,re1e2,rel,
        relators,rellene,sometodo,start,starttime,t,timeout,flowerlimit;

  timeout := ValueOption("SunflowerTimeout");
  if timeout = fail then timeout := infinity; fi;
  flowerlimit := ValueOption("SunflowerLimit");
  if flowerlimit = fail then flowerlimit := infinity; fi;

  Info(InfoTom,3,"Running sunflower with timeout ",timeout,"...");
  starttime := Runtime();
  r!.sunflowers := [];
  # This investigates whether there is a goes up and stays up sunflower
  # starting with this directed edge.
  # The value we do goes up and stays up with is r(e1,e2) - c(e1,e2)
  # where r(e1,e2) is the average relative length of the two halfedges
  # (i.e. (l(e1)+l(e2))/(2*len) where len is the full relator length)
  # and c(e1,e2) is the corner value.
  # Every corner value c(e1,e2) not on the exception list is either 1/6
  # or 1/4.
  # We know: if r(e1,e2) > 1/6 (or 1/4 in the other case), then 
  # c(e1,e2) is on the exception list.
  # Thus: We only have to start with corners on the exception list.
  DoStep := function(ee,d)
    # This uses variables n, he, len, e1, r, Y from the outer function!
    local f,flow,nn,s;
    nn := n + he.length;
    if nn >= len then
        if nn > len then return; fi;
        if ee <> e1 then return; fi;
        # Hurray! We found a sunflower!
        flow := rec( curv := d, hes := EmptyPlist(6));
        s := t;
        while s <> fail do
            Add(flow.hes,s[1]);
            s := s[3];
        od;
        flow.hes := Reversed(flow.hes);
        Add(r!.sunflowers,flow);
        Info(InfoTom,3,"Found sunflower, curvature ",d);
    else
        # Now need to add [ee,d] in Y[nn]:
        if not(IsBound(Y[nn])) then Y[nn] := []; fi;
        f := First([1..Length(Y[nn])],l->Y[nn][l][1]=ee);
        if f = fail then
            Add(Y[nn],[ee,d,t]);
        else
            if d > Y[nn][f][2] then
                Y[nn][f][2] := d;
                Y[nn][f][3] := t;
            fi;
        fi;
    fi;
  end;

  # to speed up access (and save some ! signs):
  cornindex := r!.cornindex;
  cornright := r!.cornright;
  cornval := r!.cornval;
  halfedges := r!.halfedges;
  relators := r!.relators;
  circle := r!.circle;
  heindex := r!.heindex;

  # First run through all possible first halfedges:
  for e1 in [1..Length(halfedges)] do
      # Y[n] contains segments of length n, each element is a triple
      # [e2,curvsum,previous]
      start := [e1,0,fail];
      Y := [];
      sometodo := false;
      for co in cornindex[e1] do
          e2 := cornright[co];
          ce1e2 := cornval[co];
          he1 := halfedges[e1];
          rel := relators[he1.relator];
          he2 := halfedges[e2];
          len := RelatorLength(rel);
          re1e2 := (he1.length+he2.length)*circle/(2*len);
          c := re1e2 - ce1e2;
          if c > 0 then
              if not(IsBound(Y[he1.length])) then Y[he1.length] := []; fi;
              Add(Y[he1.length],[e2,c,start]);
              sometodo := true;
          fi;
      od;
      if sometodo then
          for n in [1..len-1] do
              if IsBound(Y[n]) then
                  for j in [1..Length(Y[n])] do
                      t := Y[n][j];
                      # Now try to follow this with one more edge:
                      e := t[1];
                      c := t[2];
                      he := halfedges[e];
                      rel := relators[he.relator];
                      len := RelatorLength(rel);
                      # We need another corner [e,ee] for which 
                      # c + r(e,ee)-c(e,ee) > 0
                      # There are two cases: Either it is on the exception
                      # list or c(e,ee) >= 1/6 and thus 
                      # 0 < c+r(e,ee)-c(e,ee) <= c+r(e,ee)-1/6 and thus
                      # r(e,ee) > 1/6 - c
                      rellene := he.length*circle/(2*len);
                      c := c+rellene;
                      for co in cornindex[e] do
                          ee := cornright[co];
                          hee := halfedges[ee];
                          d := c + hee.length*circle/(2*len) - cornval[co];
                          if d > 0 then
                              DoStep(ee,d);
                          fi;
                      od;
                      # Now handle the generic case:
                      pos := IndexPrimWord(rel,he.start+he.length);
                      kk := Length(heindex[he.relator][pos]);
                      for k in [1..kk] do   # this gives descending values
                                            # of rellenee
                          ee := heindex[he.relator][pos][k];
                          if not IsExceptionalCorner(r,[e,ee]) then
                              hee := halfedges[ee];
                              d := c + hee.length*circle/(2*len);
                              if d-circle/6 <= 0 then
                                  # This is OK because we descend with
                                  # rellenee!
                                  break; 
                              fi;
                              if IsOneCompletable(r,e,ee) then
                                  d := d - circle/6;
                              else
                                  d := d - circle/4;
                              fi;
                              if d > 0 then
                                  DoStep(ee,d);
                              fi;
                          fi;
                      od;
                  od;
                  if Runtime()-starttime > timeout or 
                     Length(r!.sunflowers) > flowerlimit then
                      Info(InfoTom,1,"Sunflower: Giving up, have ",
                           Length(r!.sunflowers)," sunflowers.");
                      return;
                  fi;
              fi;
          od;
      fi;
  od;
  if Length(r!.sunflowers) = 0 then
      Info(InfoTom,2,"Completed sunflower successfully, none found.");
  else
      Info(InfoTom,2,"Completed sunflower, found ",Length(r!.sunflowers),
           " sunflowers.");
  fi;

end;

RemoveForbiddenSunflowers := function(s)
  # Does what it says.
  Info(InfoTom,3,"Removing forbidden sunflowers...");

  if IsBound(s!.sunflowers) then
      Info(InfoTom,3,"Sunflowers left: ",Length(s!.sunflowers),".");
  fi;
end;

Poppy := function(s)
  # Find all positively curved poppies.
  # Plan: first try valency v=3, if no failures, try 4 etc.
  #   Going counterclockwise round a vertex, do
  #   goes up and stays up on c(e1,e2)-(v-2)/2v
  #   Note (v-2)/2v is 1/6 for v=3 and grows monotonically with v
  # 0) Set v:=3 and a := (v-2)/2v := 1/6
  # 1) Write down all corners with c(e1,e2)-a > 0
  # 2) Check which of them are v-poppies (need coincidence)
  # 3) if some, report
  # 4) v := v + 1
  # 5) a := (v-2)/2v, 
  # 6) weed out non-going up and staying up ones
  # 7) if empty, bail out
  # 8) for each left, add one more step in all possible ways
  # 9) go to 2
  # Data: have a list of cases, have v and a
  # A case is a list [curv,e1,e2,e3,...,e_{v-1}] of halfedges
  local a,anew,c,ca,cases,circle,co,cornindex,cornright,cornval,d,e,e1,e2,
        ee,eee,f,found,halfedges,he,he1,he1c,he2,he2c,hee,heee,heindex,i,
        invtab,j,newca,newcases,newstart,p,pongo,poppy,pos,rel,relators,
        todelete,v,timeout,flowerlimit,starttime;

  timeout := ValueOption("PoppyTimeout");
  if timeout = fail then timeout := infinity; fi;
  flowerlimit := ValueOption("PoppyLimit");
  if flowerlimit = fail then flowerlimit := infinity; fi;

  Info(InfoTom,3,"Running poppy with timeout ",timeout,"...");
  starttime := Runtime();

  # Some assignments to local variables to speed up access:
  pongo := s!.pongo;
  invtab := s!.invtab;
  halfedges := s!.halfedges;
  relators := s!.relators;
  heindex := s!.heindex;
  circle := s!.circle;
  cornindex := s!.cornindex;
  cornright := s!.cornright;
  cornval := s!.cornval;

  s!.poppies := [];
  v := 3;
  a := (v-2)*circle/(2*v);

  # Initialise cases, note that since a=1/6 they are all on the exceptions
  # lists:
  cases := [];
  for e1 in [1..Length(halfedges)] do
      he1 := halfedges[e1];
      he1c := halfedges[he1.complement];
      for co in cornindex[e1] do
          c := cornval[co];
          if c > a then   # Note a=1/6 at this stage
              e2 := cornright[co];
              he2 := halfedges[e2];
              he2c := halfedges[he2.complement];
              rel := relators[he2c.relator];
              pos := IndexPrimWord(rel,he2c.start+he2c.length);
              p := rel.primword[pos][1];
              rel := relators[he2.relator];
              p := PongoMult(pongo,p,rel.primword[he2.start][1]);
              rel := relators[he1c.relator];
              p := PongoMult(pongo,p,rel.primword[he1c.start][1]);
              if not(IsZero(pongo,p)) then
                  Add(cases,rec(curv := c-a, hes := [e1,he2.complement],
                                pongoelm := p));
              fi;
          fi;
      od;
  od;
  #Debug("have cases");
  while true do
      if Runtime() - starttime > timeout then
          Info(InfoTom,1,"Poppy: timeout, giving up, have ",
               Length(s!.poppies)," poppies.");
          return;
      fi;
      if Length(s!.poppies) > flowerlimit then
          Info(InfoTom,1,"Poppy: hit flower limit, giving up, have ",
               Length(s!.poppies)," poppies.");
          return;
      fi;

      # Check whether or not our cases are v-poppies:
      Info(InfoTom,3,"v=",v,", have ",Length(cases)," cases.");
      found := false;
      for i in [1..Length(cases)] do
          ca := cases[i];
          if IsAccepting(s!.pongo,ca.pongoelm) then
              # Otherwise this cannot be a v-poppy!
              f := halfedges[ca.hes[1]].complement;
              e := ca.hes[Length(ca.hes)];
              he := halfedges[e];
              newstart := IndexPrimWord(relators[he.relator],
                                        he.start+he.length);
              for ee in heindex[he.relator][newstart] do
                  c := ca.curv + LookupCornerValue(s,[e,ee]) - a;
                  if c > 0 then
                      hee := halfedges[ee];
                      eee := hee.complement;
                      heee := halfedges[eee];
                      rel := relators[heee.relator];
                      pos := IndexPrimWord(rel,heee.start+heee.length);
                      if f in heindex[heee.relator][pos] then
                          c := c + LookupCornerValue(s,[eee,f]) - a;
                          if c > 0 then
                              poppy := rec(curv := c, hes:=ShallowCopy(ca.hes),
                                           pongoelm := ca.pongoelm);
                              Add(poppy.hes,eee);
                              Add(s!.poppies,poppy);
                              found := true;
                              if Length(s!.poppies) > flowerlimit then
                                  Info(InfoTom,1,"Poppy: hit flower limit, ",
                                       "giving up, have ",
                                       Length(s!.poppies)," poppies.");
                                  return;
                              fi;
                          fi;
                      fi;
                  fi;
              od;
          fi;
      od;
      #Debug("have extended");
      if found then break; fi;
      # Now try one valency higher:
      v := v + 1;
      anew := (v-2)*circle/(2*v);
      todelete := [];
      for i in [1..Length(cases)] do
          ca := cases[i];
          ca.curv := ca.curv + (Length(ca.hes)-1)*(a-anew);
          if ca.curv < 0 then 
              Add(todelete,i);
          else
              d := 0;
              for j in [1..Length(ca.hes)-1] do
                  d := d + LookupCornerValue(s,[ca.hes[j],ca.hes[j+1]]) - anew;
                  if d <= 0 then
                      Add(todelete,i);
                      break;
                  fi;
              od;
          fi;
      od;
      cases := cases{Difference([1..Length(cases)],todelete)};
      a := anew;
      Info(InfoTom,3,"v=",v,", have weeded out ",Length(todelete)," cases.");
      if Length(cases) = 0 then break; fi;

      # Now extend by 1:
      newcases := EmptyPlist(Length(cases));
      for i in [1..Length(cases)] do
          ca := cases[i];
          e := ca.hes[Length(ca.hes)];
          he := halfedges[e];
          for ee in heindex[he.relator][he.start] do
              c := ca.curv + LookupCornerValue(s,[e,ee]) - a;
              if c > 0 then
                  hee := halfedges[ee];
                  eee := hee.complement;
                  heee := halfedges[eee];
                  rel := relators[heee.relator];
                  pos := IndexPrimWord(rel,heee.start+heee.length);
                  p := PongoMult(pongo,rel.primword[pos][1],ca.pongoelm);
                  if not(IsZero(pongo,p)) then
                      newca := rec(curv := c, 
                                   hes := EmptyPlist(Length(ca.hes)+1),
                                   pongoelm := p);
                      Append(newca.hes,ca.hes);
                      Add(newca.hes,eee);
                      Add(newcases,newca);
                  fi;
              fi;
          od;
      od;
      #Debug("newcases");
      cases := newcases;
      if Length(cases) = 0 then break; fi;
  od;
  if Length(s!.poppies) = 0 then
      Info(InfoTom,2,"Completed poppy successfully, none found.");
  else
      Info(InfoTom,2,"Completed poppy, found ",Length(s!.poppies),
           " poppies.");
  fi;

end;

RemoveForbiddenPoppies := function(s)
  # Does what it says.
  Info(InfoTom,3,"Removing forbidden poppies...");

  if IsBound(s!.poppies) then
      Info(InfoTom,3,"Poppies left: ",Length(s!.poppies),".");
  fi;
end;

PickPoppy := function(s,poppy)
  # Decreases some corner values to make poppy happy (i.e. go away)
  local c,cc,p,pairs,v;
  v := Length(poppy.hes);
  c := poppy.curv;
  pairs := List([1..v-1],i->[poppy.hes[i],
                             s!.halfedges[poppy.hes[i+1]].complement]);
  Add(pairs,[poppy.hes[v],s!.halfedges[poppy.hes[1]].complement]);
  for p in pairs do
      cc := LookupCornerValue(s,p);
      AddCornerException(s,p,Int(cc-c/v));
  od;
end;

PickSunflower := function(s,sunflower)
  # Increases some corner values to make sunflower happy (i.e. go away)
  local c,cc,p,pairs,v;
  v := Length(sunflower.hes);
  c := sunflower.curv;
  pairs := List([1..v-1],i->[sunflower.hes[i],sunflower.hes[i+1]]);
  Add(pairs,[sunflower.hes[v],sunflower.hes[1]]);
  for p in pairs do
      cc := LookupCornerValue(s,p);
      AddCornerException(s,p,Int(cc+c/v));
  od;
end;

Ymaxsq := function(x)
  if x <= 0 then return 0;
  else return x^2; fi;
end;

dYmaxsq := function(x)
  if x <= 0 then return 0;
  else return 2*x; fi;
end;

dYmaxsqeps := function(x)
  if x <= -1/1000 then return 0;
  else return 2*(x-1/1000); fi;
end;

Yideps := function(x)
  if x <= -360 then return 0;
  else return x+360; fi;
end;

dYideps := function(x)
  if x <= -360 then return 0;
  else return 1; fi;
end;

#$$$ This computes the gradient of the badness function. It will only
# work if all corners in the flowers are already in the exception list
# and are stored in the flower record.
# This is for example achieved by using CollectFlowers to add them to
# the allpoppies and allsunflowers components.
#
# Y is a function in one variable used in the badness function
# dY must be its derivative
FindGradient := function(s,poppies,sunflowers,dY)
  local c,gradient,hash,i,l,p,pos,v;
  gradient := 0*[1..Length(s!.cornval)];
  hash := s!.cornhash;
  for p in poppies do
      l := p.corns;
      v := Length(l);
      c := p.curv;
      for i in [1..v] do
          pos := l[i];
          gradient[pos] := gradient[pos] + dY(c);
      od;
  od;
  for p in sunflowers do
      l := p.corns;
      v := Length(l);
      c := p.curv;
      for i in [1..v] do
          pos := l[i];
          gradient[pos] := gradient[pos] - dY(c);
      od;
  od;
  return gradient;
end;

ApplyGradient := function(s,grad,factor)
  local c,i;
  for i in [1..Length(grad)] do
      c := s!.cornval[i];
      AddCornerException(s,i,Int(c+grad[i]*factor));
  od;
end;
  

ApplyCorrections := function(s,corr,factor)
  local c,i;
  for i in [1..Length(corr.corners)] do
      c := LookupCornerValue(s,corr.corners[i]);
      AddCornerException(s,corr.corners[i],Int(c+corr.corrections[i]*factor));
  od;
end;

FindNewRewrites := function(s)
  # Classify for each segment of a relator the largest curvature this
  # face could have if this segment is exposed on the boundary.
  # Only report positive such bounds.
  Info(InfoTom,1,"Finding rewrites...");

  Info(InfoTom,1,"Found ",Length(s!.rewrites)," rewrites.");
end;

RationalApproximation := function(x,prec)
  # x needs to be a number (rational, float, or real irrational)
  # prec needs to be a positive integer
  local a,i,l,lasta,minus,stop,xi;
  l := [];
  lasta := 0;
  a := 0;
  stop := false;
  while DenominatorRat(a) <= prec do
      xi := Int(x);
      x := x-xi;
      if not(IsZero(x)) then
          x := x^-1;
      else
          stop := true;
      fi;
      Add(l,xi);
      lasta := a;
      a := xi;
      for i in [Length(l)-1,Length(l)-2..1] do
          a := l[i] + 1/a;
      od;
      if stop then return a; fi;
  od;
  return lasta;
end;

Badness := function(poppies,sunflowers,Y)
  # Y is a function in one variable used in the badness function
  # dY must be its derivative
  local i,p,sum;
  sum := 0;
  for p in poppies do
      if p.curv > 0 then
          sum := sum + Y(p.curv);
      fi;
  od;
  for p in sunflowers do
      if p.curv > 0 then
          sum := sum + Y(p.curv);
      fi;
  od;
  return sum;
end;

#$$$ This function adds all corners of the poppy f to the exception
# list and stores a list of the corner numbers in f.corns.
ComputePoppyCorners := function(s,f)
  local co,corns,h,hes,i,j,p;
  h := s!.halfedges;
  hes := f.hes;
  corns := EmptyPlist(Length(hes));
  for i in [1..Length(hes)] do
      j := i + 1; if j > Length(hes) then j := 1; fi;
      p := [hes[i],h[hes[j]].complement];
      co := HTValue(s!.cornhash,p);
      if co = fail then
          AddCornerException(s,p,LookupCornerValue(s,p));
          co := HTValue(s!.cornhash,p);
      fi;
      Add(corns,co);
  od;
  f.corns := corns;
end;

#$$$ This function adds all corners of the sunflower f to the exception
# list and stores a list of the corner numbers in f.corns.
ComputeSunflowerCorners := function(s,f)
  local co,corns,hes,i,j,p;
  hes := f!.hes;
  corns := EmptyPlist(Length(hes));
  for i in [1..Length(hes)] do
      j := i + 1; if j > Length(hes) then j := 1; fi;
      p := [hes[i],hes[j]];
      co := HTValue(s!.cornhash,p);
      if co = fail then
          AddCornerException(s,p,LookupCornerValue(s,p));
          co := HTValue(s!.cornhash,p);
      fi;
      Add(corns,co);
  od;
  f.corns := corns;
end;

#$$$ This function adds the currently bad sunflowers and poppies to the
# collection of all sunflowers and poppies. In addition, all corners
# occurring are put into the exception database, so they get a number.
# This allows to put corner numbers in the flower descriptions.
CollectFlowers := function(s,poppies,sunflowers)
  local co,corns,f,h,hes,i,j,p,w;
  h := s!.halfedges;
  for f in poppies do
      ComputePoppyCorners(s,f);
  od;
  for f in sunflowers do
      ComputeSunflowerCorners(s,f);
  od;

  if not IsBound(s!.allpoppies) then s!.allpoppies := EmptyPlist(1000); fi;
  Append(s!.allpoppies,poppies);
  if Length(s!.allpoppies) > 0 then
      Sort(s!.allpoppies);
      w := 2;
      for j in [2..Length(s!.allpoppies)] do
          if s!.allpoppies[j-1] <> s!.allpoppies[j] then
              s!.allpoppies[w] := s!.allpoppies[j];
              w := w + 1;
          fi;
      od;
      for j in [w..Length(s!.allpoppies)] do
          Unbind(s!.allpoppies[j]);
      od;
  fi;

  if not IsBound(s!.allsunflowers) then s!.allsunflowers:=EmptyPlist(1000);fi;
  Append(s!.allsunflowers,sunflowers);
  if Length(s!.allsunflowers) > 0 then
      Sort(s!.allsunflowers);
      w := 2;
      for j in [2..Length(s!.allsunflowers)] do
          if s!.allsunflowers[j-1] <> s!.allsunflowers[j] then
              s!.allsunflowers[w] := s!.allsunflowers[j];
              w := w + 1;
          fi;
      od;
      for j in [w..Length(s!.allsunflowers)] do
          Unbind(s!.allsunflowers[j]);
      od;
  fi;
  Info(InfoTom,1,"Flower collection now has ",Length(s!.allpoppies),
       " poppies and ",Length(s!.allsunflowers)," sunflowers.");
end;

#$$$ This function recomputes the corner numbers and curvature values
# for the given lists of flowers. Note that this can add exceptional
# corners in s.
RecomputeFlowerCurvature := function(s,poppies,sunflowers)
  # Changes lists poppies and sunflowers
  local c,corns,cornval,f,h,i,j;
  h := s!.halfedges;
  cornval := s!.cornval;
  for i in [1..Length(poppies)] do
      f := poppies[i];
      ComputePoppyCorners(s,f);
      corns := f.corns;
      c := s!.circle-s!.circle*Length(corns)/2;
      for j in [1..Length(corns)] do
          c := c + cornval[corns[j]];
      od;
      # for testing: if f.curv <> c then Error(1); fi;
      f.curv := c;
  od;
  for i in [1..Length(sunflowers)] do
      f := sunflowers[i];
      ComputeSunflowerCorners(s,f);
      corns := f.corns;
      c := s!.circle;
      for j in [1..Length(corns)] do
          c := c - cornval[corns[j]];
      od;
      # for testing: if f.curv <> c then Error(2); fi;
      f.curv := c;
  od;
end;

#$$$ Idea: Take the poppies and sunflowers, compute a gradient and then
# apply that one with different factors, take the best and repeat.
# Y is a function in one variable used in the badness function
# dY must be its derivative
# We assume that poppy and sunflower have just run with the current
# exceptions and that those have already been collected.

GradientApproximateGoodOfficer := function(s,steps,timeout,Y,dY)
  local backup,badness,best,factors,grad,i,j,newbadness,norm,starttime;
  starttime := Runtime();
  if Length(s!.poppies) + Length(s!.sunflowers) = 0 then
      Info(InfoTom,1,"Nothing to do, no poppies or sunflowers!");
      return;
  fi;
  for i in [1..steps] do
      badness := Badness(s!.allpoppies,s!.allsunflowers,Y);
      #Error();
      if i < 5 then 
          factors := [1/5];
      elif badness < 1000000 then
          factors := [1/30,1/5,3/5,1,3/2,2];
      else
          factors := [1/30,1/5,3/5];
      fi;
      Info(InfoTom,1,"Badness: ",badness,
                     " before step ",i," of ",steps,"...");
      Info(InfoTom,1,"Have ",Length(s!.poppies),"/",Length(s!.allpoppies),
           " poppies and ",Length(s!.sunflowers),"/",Length(s!.allsunflowers),
           " sunflowers.");
      if Runtime()-starttime > timeout then 
          Info(InfoTom,1,"Timeout reached, giving up...");
          return;
      fi;
      backup := ExportExceptions(s);
      grad := FindGradient(s,s!.allpoppies,s!.allsunflowers,dY);
      norm := -badness/Sum(grad,x->x^2);
      best := 0;
      badness := 10^100;
      for j in [1..Length(factors)] do
          ImportExceptions(s,backup);
          ApplyGradient(s,grad,factors[j]*norm);
          Sunflower(s);
          RemoveForbiddenSunflowers(s);
          Poppy(s);
          RemoveForbiddenPoppies(s);
          if Length(s!.poppies) = 0 and Length(s!.sunflowers) = 0 then
              Info(InfoTom,1,"Success with factor ",factors[j],"! All done.");
              return;
          fi;
          newbadness := Badness(s!.poppies,s!.sunflowers,Y);
          if newbadness < badness then
              Info(InfoTom,2,"Factor ",factors[j]," improves badness to ",
                   newbadness,".");
              badness := newbadness;
              best := j;
              #Error(2);
          else
              Info(InfoTom,2,"Factor ",factors[j]," worsens badness to ",
                   newbadness,".");
              #Error(3);
          fi;
      od;
      if best = 0 then
          Info(InfoTom,1,"No correction made it better, giving up.");
          ImportExceptions(s,backup);
          RecomputeFlowerCurvature(s,s!.allpoppies,s!.allsunflowers);
          return;
      fi;
      Info(InfoTom,1,"Used factor ",factors[best]);
      ImportExceptions(s,backup);
      ApplyGradient(s,grad,factors[best]*norm);
      Sunflower(s);
      RemoveForbiddenSunflowers(s);
      Poppy(s);
      RemoveForbiddenPoppies(s);
      RecomputeFlowerCurvature(s,s!.allpoppies,s!.allsunflowers);
      CollectFlowers(s,s!.poppies,s!.sunflowers);
  od;
  Info(InfoTom,1,"No success, giving up after ",steps," steps.");
end;

#$$$ This function takes the current flower collection and uses one gradient
# to improve things.
# We assume that poppy and sunflower have just run with the current
# exceptions and that those have already been collected.
GradStep := function(s,Y,dY)
  local a,b,badnessa,badnessb,badnessc,c,grad,norm,dist;
  if Length(s!.poppies) + Length(s!.sunflowers) = 0 then
      Info(InfoTom,1,"Nothing to do, no poppies or sunflowers!");
      return;
  fi;
  grad := FindGradient(s,s!.allpoppies,s!.allsunflowers,dY);
  badnessa := Badness(s!.allpoppies,s!.allsunflowers,Y);
  a := ExportExceptions(s);
  norm := -badnessa/Sum(grad,x->x^2);

  ApplyGradient(s,grad,norm);
  RecomputeFlowerCurvature(s,s!.allpoppies,s!.allsunflowers);
  badnessb := Badness(s!.allpoppies,s!.allsunflowers,Y);
  b := ExportExceptions(s);

  ApplyGradient(s,grad,norm);
  RecomputeFlowerCurvature(s,s!.allpoppies,s!.allsunflowers);
  badnessc := Badness(s!.allpoppies,s!.allsunflowers,Y);
  c := ExportExceptions(s);

  while true do
      dist := AbsInt(badnessa-badnessb) +AbsInt(badnessc-badnessb);
      Info(InfoTom,1,"a=",badnessa," b=",badnessb," c=",badnessc," dist=",
           dist);
      if dist < 1000 or 20*dist < badnessb then break; fi;
      if badnessb <= badnessa and badnessc <= badnessb then
          # drop a, step over c
          a := b; badnessa := badnessb;
          b := c; badnessb := badnessc;
          c := StructuralCopy(c);
          c.cornval := 2*b.cornval - a.cornval;
          ImportExceptions(s,c);
          RecomputeFlowerCurvature(s,s!.allpoppies,s!.allsunflowers);
          badnessc := Badness(s!.allpoppies,s!.allsunflowers,Y);
      elif badnessc >= badnessb and badnessb >= badnessa then
          # drop c, step over a
          c := b; badnessc := badnessb;
          b := a; badnessb := badnessa;
          a := StructuralCopy(a);
          a.cornval := 2*b.cornval - c.cornval;
          ImportExceptions(s,a);
          RecomputeFlowerCurvature(s,s!.allpoppies,s!.allsunflowers);
          badnessa := Badness(s!.allpoppies,s!.allsunflowers,Y);
      # now: badnessc >= badnessb and badnessb <= badnessa
      elif badnessc >= badnessa then
          # drop c, go between a and b
          c := b; badnessc := badnessb;
          b := StructuralCopy(b);
          b.cornval := List([1..Length(b.cornval)],
                            i->QuoInt(a.cornval[i]+c.cornval[i],2));
          ImportExceptions(s,b);
          RecomputeFlowerCurvature(s,s!.allpoppies,s!.allsunflowers);
          badnessb := Badness(s!.allpoppies,s!.allsunflowers,Y);
      else   # badnessc <= badnessa
          # drop a, go between b and c
          a := b; badnessa := badnessb;
          b := StructuralCopy(b);
          b.cornval := List([1..Length(b.cornval)],
                            i->QuoInt(a.cornval[i]+c.cornval[i],2));
          ImportExceptions(s,b);
          RecomputeFlowerCurvature(s,s!.allpoppies,s!.allsunflowers);
          badnessb := Badness(s!.allpoppies,s!.allsunflowers,Y);
      fi;
  od;
  ImportExceptions(s,b);
  RecomputeFlowerCurvature(s,s!.allpoppies,s!.allsunflowers);
  Poppy(s);
  Sunflower(s);
  if Length(s!.poppies) + Length(s!.sunflowers) = 0 then
      Info(InfoTom,1,"Success! No more poppies and sunflowers!");
      return true;
  fi;
  CollectFlowers(s,s!.poppies,s!.sunflowers);
  return false;
end;

IterativeGradient := function(s,steps,Y,dY)
  local i;
  for i in [1..steps] do
      Info(InfoTom,1,"IterativeGradient: step=",i);
      if GradStep(s,Y,dY) then return true; fi;
  od;
  return false;
end;

#$$$ This function takes the collection of poppies and sunflowers and
# tries to run an LP solver to find new corner values to make all of 
# them happy. It returns a boolen, true if successful and false otherwise.
# In the former case the corner exceptions are adjusted according to the
# solution. This function relies on the externally installed glpsol
# program.
DoLP := function(s,withopt)
  local c,count,dir,f,i,j,li,lines,lp,p,popoccur,prob,res,sunoccur;
  dir := DirectoryTemporary();
  prob := Filename(dir,"problem.mod");
  p := IO_File(prob,"w");
  IO_Write(p,"# This is a poppy/sunflower problem for tom2.g\n");
  IO_Write(p,"var x{i in 1..",Length(s!.cornval),"} >=0, <=",s!.circle/2,";\n");
  if withopt then
      popoccur := BlistList([1..Length(s!.cornval)],[]);
      sunoccur := BlistList([1..Length(s!.cornval)],[]);
      for f in s!.allpoppies do
          for c in f.corns do
              popoccur[c] := true;
          od;
      od;
      for f in s!.allsunflowers do
          for c in f.corns do
              sunoccur[c] := true;
          od;
      od;
  fi;
  IO_Write(p,"minimize cost : 0");
  if withopt then
      for c in [1..Length(s!.cornval)] do
          if popoccur[c] and not(sunoccur[c]) then
              IO_Write(p,"-x[",c,"]");
          elif sunoccur[c] and not(popoccur[c]) then
              IO_Write(p,"+x[",c,"]");
          fi;
      od;
  fi;
  IO_Write(p,";\n");
  count := 1;
  for f in s!.allpoppies do
      IO_Write(p,"s.t. poppy",count,":");
      IO_Write(p,s!.circle-Length(f.corns)*s!.circle/2);
      for c in f.corns do
          IO_Write(p,"+x[",c,"]");
      od;
      IO_Write(p,"<=0;\n");
      count := count + 1;
  od;
  count := 1;
  for f in s!.allsunflowers do
      IO_Write(p,"s.t. sunflower",count,":");
      IO_Write(p,s!.circle);
      for c in f.corns do
          IO_Write(p,"-x[",c,"]");
      od;
      IO_Write(p,"<=0;\n");
      count := count + 1;
  od;
  IO_Write(p,"solve;\n");
  IO_Write(p,"printf 'Solution:\\n';\n");
  IO_Write(p,"printf {i in 1..",Length(s!.cornval),"}:'%.0f\\n',x[i];\n");
  IO_Write(p,"printf 'Done.\\n';\n");
  IO_Write(p,"en","d;\n");
  IO_Close(p);
  lp := IO_Popen("glpsol",["--model",prob],"r");
  res := IO_ReadUntilEOF(lp);
  IO_Close(lp);
  lines := SplitString(res,"\n","");
  # Parse output:
  for i in [1..Length(lines)] do
      li := lines[i];
      if li = "PROBLEM HAS NO PRIMAL FEASIBLE SOLUTION" then
          IO_unlink(prob);
          return false;
      elif li = "OPTIMAL SOLUTION FOUND" then
          Info(InfoTom,1,"Found solution for LP problem!");
      elif li = "Solution:" then
          for j in [i+1..i+Length(s!.cornval)] do
              AddCornerException(s,j-i,Int(lines[j]));
          od;
          RecomputeFlowerCurvature(s,s!.allpoppies,s!.allsunflowers);
          IO_unlink(prob);
          return true;
      fi;
  od;
  Error("could not have happened!");
end;

#$$$ This function repeatedly calls DoLP until there are no more flowers.
# We assume that there is already a collection of flowers.
IterateLP := function(s,steps,withopt)
  local i,suc;
  for i in [1..steps] do
      Info(InfoTom,1,"IterateLP: step ",i);
      suc := DoLP(s,withopt);
      if not suc then 
          Info(InfoTom,1,"IterateLP: no solution! Giving up.");
          return fail; 
      fi;
      Poppy(s);
      Sunflower(s);
      if Length(s!.poppies) = 0 and Length(s!.sunflowers) = 0 then
          Info(InfoTom,1,"IterateLP: SUCCESS!");
          return true;
      fi;
      Info(InfoTom,1,"IterateLP: Found ",Length(s!.poppies)," new poppies and ",
           Length(s!.sunflowers)," new sunflowers.");
      CollectFlowers(s,s!.poppies,s!.sunflowers);
  od;
  Info(InfoTom,1,"IterateLP: Giving up.");
  return false;
end;


StartupTom := function(s)
    local store,store2;
    ComputeEdges(s);
    RemoveForbiddenEdges(s);
    IndexEdges(s);
    InitCornerData(s,360360,"sunflowershappy");
    Poppy(s);
    RemoveForbiddenPoppies(s);
    CollectFlowers(s,s!.poppies,[]);
    InitCornerData(s,360360,"default");
    RecomputeFlowerCurvature(s,s!.allpoppies,s!.allsunflowers);
    Poppy(s);
    RemoveForbiddenPoppies(s);
    Sunflower(s);
    RemoveForbiddenSunflowers(s);
    CollectFlowers(s,s!.poppies,s!.sunflowers);
end;

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
    # :A specifies the area of the relator
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

rels := ParsePongoLetter(pongo,invtab,
         ["(ST)^7:10",
          "(RT)^7:10",
          "(STRT)^13:10"]);
rewrites := [];

s := MakeTomProblem(pongo,invtab,rels,rewrites);


rels2 := ParsePongoLetter(pongo,invtab,
         ["(ST)^7:10",
          "(RT)^7:10",
          "(STRT)^13:10",
          "(STRT)^11RT(ST)^4(RT)^2:29",
          "(STRT)^11(ST)^2(RT)^4ST:29"
         ]);

s2 := MakeTomProblem(pongo,invtab,rels2,rewrites);

OneRelatorQuotientOfModularGroupForTom := function(n)
  local invtab,l,ll,pongo,rels;
  pongo := CayleyPongo([[1,2,3],[2,3,1],[3,1,2]],1);
  SetElementNames(pongo,"1SR");
  invtab := PlainInvTab([1]);
  SetElementNames(invtab,"T");
  rels := [];
  if n > 1 then
      l := [];
      ll := [];
      while n > 1 do
          if IsOddInt(n) then
              Add(l,[3,1]);
              Add(ll,[2,1]);
              n := (n-1)/2;
          else
              Add(l,[2,1]);
              Add(ll,[3,1]);
              n := n/2;
          fi;
      od;
      l := Reversed(l);
      l := LexLeastRotation(l);
      ll := LexLeastRotation(ll);
      Add(rels,rec( area := 10, power := l[2], primword := l[1] ));
      if l <> ll then
          Add(rels,rec( area := 10, power := ll[2], primword := ll[1] ));
      fi;
  fi;
  return MakeTomProblem(pongo,invtab,rels,[]);
end;

Do := function(n)
  local s;
  s := OneRelatorQuotientOfModularGroupForTom(n);
  StartupTom(s);
  GradientApproximateGoodOfficer(s,10000,1000000,Ymaxsq,dYmaxsq,1000000);
end;

