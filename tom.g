
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

AddCornerException := function(s,e1,e2,c)
  local he2,rellen2;
  AddSet(s!.except[e1],[c,e2]);
end;

ChangeCornerException := function(s,e1,e2,c)
  # This is slow, but could be replaced by something faster
  local i,l;
  l := s!.except[e1];
  for i in [1..Length(l)] do
      if l[i][2] = e2 then l[i][1] := c; Sort(l); return; fi;
  od;
  AddCornerException(s,e1,e2,c);
end;

LookupCornerValue := function(s,e1,e2)
  # This is slow, but could be replaced by something faster
  local he1,he2,i,l,p1,p2,rel1,rel2;
  l := s!.except[e1];
  for i in [1..Length(l)] do
      if l[i][2] = e2 then return l[i][1]; fi;
  od;
  # Now the default values:
  he1 := s!.halfedges[s!.halfedges[e1].complement];
  rel1 := s!.relators[he1!.relator];
  p1 := he1.start;
  he2 := s!.halfedges[s!.halfedges[e2].complement];
  rel2 := s!.relators[he2!.relator];
  p2 := IndexPrimWord(rel2,he2.start+he2.length-1);
  if IsOneCompletable(s,e1,e2) then
      return 1/6;
  else 
      return 1/4;
  fi;
end;

IsExceptionalCorner := function(s,e1,e2)
  # This is slow, but could be replaced by something faster
  local i,l;
  l := s!.except[e1];
  for i in [1..Length(l)] do
      if l[i][2] = e2 then return true; fi;
  od;
  return false;
end;

InitCornerData := function(s)
  # Initialise the data structures for corner exception lists
  local e1,endpos,he1,i,ind,len1,r,rel;
  Info(InfoTom,1,"Initialising corner data structures...");

  # A corner is a certain pair of halfedges [e1,e2].
  # Every corner value is 1/6 or 1/4, unless it is an exception.
  # It is 1/6 if there is a vertex of valency 3 containing this corner
  # and otherwise 1/4.
  # Every exceptional corner value v of a corner [e1,e2] is stored
  # under s!.except[e1][i] = [v,e2] and all s!.except[e1] are lists sorted
  # in lexicographically increasing order.
  s!.except := List([1..Length(s!.halfedges)],i->[]);

  # This also needs to find all corners with average relative length greater
  # than the default corner value to put them on the exception list.
  for e1 in [1..Length(s!.halfedges)] do
      he1 := s!.halfedges[e1];
      rel := s!.relators[he1.relator];
      len1 := he1.length/(RelatorLength(rel)*2);
      i := 1;
      endpos := IndexPrimWord(rel,he1.start+he1.length);
      ind := s!.heindex[he1.relator][endpos];
      for i in [1..Length(ind)] do
          r := len1 + s!.halfedges[ind[i]].length/(RelatorLength(rel)*2);
          if r <= 1/6 then break; fi;
          if r > 1/4 or (IsOneCompletable(s,e1,ind[i]) and r > 1/6) then
              AddCornerException(s,e1,ind[i],r);
          fi;
      od;
  od;
end;

Sunflower := function(r,flowerlimit,timeout)
  # Find all positively curved sunflowers.
  local DoStep,Y,c,ce1e2,d,e,e1,e2,ee,he,he1,he2,hee,j,k,kk,len,n,pos,
        re1e2,rel,rellene,sometodo,start,starttime,t;
  Info(InfoTom,3,"Running sunflower with timeout ",timeout,"...");
  starttime := Runtime();
  r!.sunflowers := [];
  # This investigates whether there is a goes up and stays up sunflower
  # starting with this directed edge.
  # The value we do goes up and stays up with is r(e1,e2) - c(e1,e2)
  # where r(e1,e2) is the average relative length of the two halfedges
  # (i.e. (l(e1)+l(e2))/(2*len) where len is the full relator length)
  # and c(e1,e2) is the corner value.
  # Every corner value c(e1,e2) not on the exception list is 1/6.
  # We know: if r(e1,e2) > 1/6 then c(e1,e2) is on the exception list.
  # Thus: We only have to start with corners on the exception list.
  DoStep := function(ee,d)
    # This uses variables n, he, len, e1, r, Y from the outer function!
    local f,flow,nn,s;
    nn := n + he.length;
    if nn >= len then
        if nn > len then continue; fi;
        if ee <> e1 then continue; fi;
        # Hurray! We found a sunflower!
        flow := rec( curv := d, hes := []);
        s := t;
        while s <> fail do
            Add(flow.hes,s[1],1);
            s := s[3];
        od;
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

  # First run through all possible first halfedges:
  for e1 in [1..Length(r!.halfedges)] do
      # Y[n] contains segments of length n, each element is a triple
      # [e2,curvsum,previous]
      start := [e1,0,fail];
      Y := [];
      sometodo := false;
      for j in [1..Length(r!.except[e1])] do
          e2 := r!.except[e1][j][2];
          ce1e2 := r!.except[e1][j][1];
          he1 := r!.halfedges[e1];
          rel := r!.relators[he1.relator];
          he2 := r!.halfedges[e2];
          len := RelatorLength(rel);
          re1e2 := (he1.length+he2.length)/(2*len);
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
                      he := r!.halfedges[e];
                      rel := r!.relators[he.relator];
                      len := RelatorLength(rel);
                      # We need another corner for which r(e,ee)-c(e,ee) >= c.
                      # There are two cases: Either it is on the exception
                      # list or c(e,ee)=1/6 and thus r(e,ee) >= c+1/6
                      rellene := he.length/(2*len);
                      kk := Length(r!.except[e]);
                      for k in [1..kk] do
                          ee := r!.except[e][k][2];
                          hee := r!.halfedges[ee];
                          d := c + rellene + hee.length/(2*len)
                                 - r!.except[e][k][1];
                          if d > 0 then
                              DoStep(ee,d);
                          fi;
                      od;
                      # Now handle the generic case:
                      pos := IndexPrimWord(rel,he.start+he.length);
                      kk := Length(r!.heindex[he.relator][pos]);
                      for k in [1..kk] do   # this gives descending values
                                            # of rellen2
                          ee := r!.heindex[he.relator][pos][k];
                          if not IsExceptionalCorner(r,e,ee) then
                              hee := r!.halfedges[ee];
                              d := c + rellene + hee.length/(2*len);
                              if d-1/6 < 0 then
                                  # This is OK because we descend with
                                  # rellen2!
                                  break; 
                              fi;
                              if IsOneCompletable(r,e,ee) then
                                  d := d - 1/6;
                              else
                                  d := d - 1/4;
                              fi;
                              if d > 0 then
                                  DoStep(ee,d);
                              fi;
                          fi;
                      od;
                  od;
                  if Runtime()-starttime > timeout or 
                     Length(r!.sunflowers) > flowerlimit then
                      Info(InfoTom,1,"Giving up, have ",
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
  local a,anew,c,ca,cases,d,e,e1,e2,ee,eee,f,found,he,he1,he1c,he2,he2c,
        hee,heee,i,j,newca,newcases,newstart,p,poppy,pos,rel,todelete,v;
  Info(InfoTom,3,"Running poppy...");

  s!.poppies := [];
  v := 3;
  a := (v-2)/(2*v);
  # Initialise cases, note that since a=1/6 they are all on the exceptions
  # lists:
  cases := [];
  for e1 in [1..Length(s!.halfedges)] do
      he1 := s!.halfedges[e1];
      he1c := s!.halfedges[he1.complement];
      for i in [1..Length(s!.except[e1])] do
          c := s!.except[e1][i][1];
          if c > a then   # Note a=1/6 at this stage
              e2 := s!.except[e1][i][2];
              he2 := s!.halfedges[e2];
              he2c := s!.halfedges[he2.complement];
              rel := s!.relators[he2c.relator];
              pos := IndexPrimWord(rel,he2c.start+he2c.length);
              p := rel.primword[pos][1];
              rel := s!.relators[he2.relator];
              p := PongoMult(s!.pongo,p,rel.primword[he2.start][1]);
              rel := s!.relators[he1c.relator];
              p := PongoMult(s!.pongo,p,rel.primword[he1c.start][1]);
              if not(IsZero(s!.pongo,p)) then
                  Add(cases,rec(curv := c-a, hes := [e1,he2.complement],
                                pongoelm := p));
              fi;
          fi;
      od;
  od;
  while true do
      # Check whether or not our cases are v-poppies:
      Info(InfoTom,3,"v=",v,", have ",Length(cases)," cases.");
      found := false;
      for i in [1..Length(cases)] do
          ca := cases[i];
          if IsAccepting(s!.pongo,ca.pongoelm) then
              # Otherwise this cannot be a v-poppy!
              f := s!.halfedges[ca.hes[1]].complement;
              e := ca.hes[Length(ca.hes)];
              he := s!.halfedges[e];
              newstart := IndexPrimWord(s!.relators[he.relator],
                                        he.start+he.length);
              for ee in s!.heindex[he.relator][newstart] do
                  c := ca.curv + LookupCornerValue(s,e,ee) - a;
                  if c >= 0 then
                      hee := s!.halfedges[ee];
                      eee := hee.complement;
                      heee := s!.halfedges[eee];
                      rel := s!.relators[heee.relator];
                      pos := IndexPrimWord(rel,heee.start+heee.length);
                      if f in s!.heindex[heee.relator][pos] then
                          c := c + LookupCornerValue(s,eee,f) - a;
                          if c > 0 then
                              poppy := rec(curv := c, hes:=ShallowCopy(ca.hes),
                                           pongoelm := ca.pongoelm);
                              Add(poppy.hes,eee);
                              Add(s!.poppies,poppy);
                              found := true;
                          fi;
                      fi;
                  fi;
              od;
          fi;
      od;
      if found then break; fi;
      # Now try one valency higher:
      v := v + 1;
      anew := (v-2)/(2*v);
      todelete := [];
      for i in [1..Length(cases)] do
          ca := cases[i];
          ca.curv := ca.curv + (Length(ca.hes)-1)*(a-anew);
          if ca.curv < 0 then 
              Add(todelete,i);
          else
              d := 0;
              for j in [1..Length(ca.hes)-1] do
                  d := d + LookupCornerValue(s,ca.hes[j],ca.hes[j+1]) - anew;
                  if d < 0 then
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
      newcases := [];
      for i in [1..Length(cases)] do
          ca := cases[i];
          e := ca.hes[Length(ca.hes)];
          he := s!.halfedges[e];
          for ee in s!.heindex[he.relator][he.start] do
              c := ca.curv + LookupCornerValue(s,e,ee) - a;
              if c >= 0 then
                  hee := s!.halfedges[ee];
                  eee := hee.complement;
                  heee := s!.halfedges[eee];
                  rel := s!.relators[heee.relator];
                  pos := IndexPrimWord(rel,heee.start+heee.length);
                  p := PongoMult(s!.pongo,rel.primword[pos][1],ca.pongoelm);
                  if not(IsZero(s!.pongo,p)) then
                      newca := rec(curv := c, hes := ShallowCopy(ca.hes),
                                   pongoelm := p);
                      Add(newca.hes,eee);
                      Add(newcases,newca);
                  fi;
              fi;
          od;
      od;
      cases := newcases;
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
      cc := LookupCornerValue(s,p[1],p[2]);
      ChangeCornerException(s,p[1],p[2],cc-c/v);
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
      cc := LookupCornerValue(s,p[1],p[2]);
      ChangeCornerException(s,p[1],p[2],cc+c/v);
  od;
end;

FindCorrection := function(s,poppies,sunflowers)
  local corner,corners,corrections,force,forces,i,l,p,pos,v;
  corners := [];
  forces := [];
  for p in poppies do
    if p.curv > 0 then    # happy poppies do not exert force!
      l := ShallowCopy(p.hes);
      v := Length(l);
      Add(l,p.hes[1]);
      for i in [1..v] do
          corner := [l[i],s!.halfedges[l[i+1]].complement];
          force := -p.curv/v;
          pos := PositionSorted(corners,corner);
          if pos > Length(corners) or corners[pos] <> corner then
              Add(corners,corner,pos);
              Add(forces,[0,0],pos);
          fi;
          forces[pos][1] := Minimum(forces[pos][1],force);
      od;
    fi;
  od;
  for p in sunflowers do
    if p.curv > 0 then   # happy sunflowers do not exert force!
      l := ShallowCopy(p.hes);
      v := Length(l);
      Add(l,p.hes[1]);
      for i in [1..v] do
          corner := [l[i],l[i+1]];
          force := p.curv/v;
          pos := PositionSorted(corners,corner);
          if pos > Length(corners) or corners[pos] <> corner then
              Add(corners,corner,pos);
              Add(forces,[0,0],pos);
          fi;
          forces[pos][1] := Maximum(forces[pos][2],force);
      od;
    fi;
  od;
  corrections := List([1..Length(forces)],i->(forces[i][1]+forces[i][2])*2);
  return rec(corners := corners, forces := forces, corrections := corrections);
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

FindGradient := function(s,poppies,sunflowers,dY)
  # This computes the gradient of the badness function.
  # Y is a function in one variable used in the badness function
  # dY must be its derivative
  local corner,corners,gradient,i,l,p,pos,v;
  corners := [];
  gradient := [];
  for p in poppies do
    if p.curv > 0 then    # happy poppies do not exert force!
      l := ShallowCopy(p.hes);
      v := Length(l);
      Add(l,p.hes[1]);
      for i in [1..v] do
          corner := [l[i],s!.halfedges[l[i+1]].complement];
          pos := PositionSorted(corners,corner);
          if pos > Length(corners) or corners[pos] <> corner then
              Add(corners,corner,pos);
              Add(gradient,0,pos);
          fi;
          gradient[pos] := gradient[pos] + dY(p.curv);
      od;
    fi;
  od;
  for p in sunflowers do
    if p.curv > 0 then   # happy sunflowers do not exert force!
      l := ShallowCopy(p.hes);
      v := Length(l);
      Add(l,p.hes[1]);
      for i in [1..v] do
          corner := [l[i],l[i+1]];
          pos := PositionSorted(corners,corner);
          if pos > Length(corners) or corners[pos] <> corner then
              Add(corners,corner,pos);
              Add(gradient,0,pos);
          fi;
          gradient[pos] := gradient[pos] - dY(p.curv);
      od;
    fi;
  od;
  return rec(corners := corners, gradient := gradient);
end;

ApplyGradient := function(s,grad,factor)
  local c,i;
  for i in [1..Length(grad.corners)] do
      c := LookupCornerValue(s,grad.corners[i][1],grad.corners[i][2]);
      ChangeCornerException(s,grad.corners[i][1],grad.corners[i][2],
                            c+grad.gradient[i]*factor);
  od;
end;
  

ApplyCorrections := function(s,corr,factor)
  local c,i;
  for i in [1..Length(corr.corners)] do
      c := LookupCornerValue(s,corr.corners[i][1],corr.corners[i][2]);
      ChangeCornerException(s,corr.corners[i][1],corr.corners[i][2],
                            c+corr.corrections[i]*factor);
  od;
end;

FindNewRewrites := function(s)
  # Classify for each segment of a relator the largest curvature this
  # face could have if this segment is exposed on the boundary.
  # Only report positive such bounds.
  Info(InfoTom,1,"Finding rewrites...");

  Info(InfoTom,1,"Found ",Length(s!.rewrites)," rewrites.");
end;

DoAll := function(s,flowerlimit,timeout)
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

RecomputeFlowerCurvature := function(s,poppies,sunflowers)
  # Changes lists poppies and sunflowers
  local c,f,h,hes,i,j;
  h := s!.halfedges;
  for i in [1..Length(poppies)] do
      f := poppies[i];
      hes := ShallowCopy(f!.hes);
      c := 1-Length(hes)/2;
      Add(hes,hes[1]);
      for j in [1..Length(hes)-1] do
          c := c + LookupCornerValue(s,hes[j],h[hes[j+1]].complement);
      od;
      # for testing: if f.curv <> c then Error(1); fi;
      f.curv := c;
  od;
  for i in [1..Length(sunflowers)] do
      f := sunflowers[i];
      hes := ShallowCopy(f!.hes);
      Add(hes,hes[1]);
      c := 1;
      for j in [1..Length(hes)-1] do
          c := c - LookupCornerValue(s,hes[j],hes[j+1]);
      od;
      # for testing: if f.curv <> c then Error(2); fi;
      f.curv := c;
  od;
end;

ApproximateExceptions := function(s,prec)
  local i,j,p;
  for i in [1..Length(s!.except)] do
      if IsBound(s!.except[i]) then
          for j in [1..Length(s!.except[i])] do
              p := s!.except[i][j];
              p[1] := RationalApproximation(p[1],prec);
          od;
          Sort(s!.except[i]);
      fi;
  od;
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

ApproximateGoodOfficer := function(s,steps,timeout)
  # Idea: Take the poppies and sunflowers, compute a correction and then
  # apply that one with different factors, take the best and repeat.
  # Also try a rational approximation with small denominators as an 
  # alternative.
  # We assume that poppy and sunflower have just run with the current
  # exceptions.
  local backup,badness,best,corr,factors,i,j,newbadness,poppies,starttime,
        sunflowers,w;
  factors := [1/100,1/10,1,6/5,"ratapprox"];
             # note "ratapprox" must always be last!
  starttime := Runtime();
  poppies := Set(s!.poppies);
  sunflowers := Set(s!.sunflowers);
  for i in [1..steps] do
      badness := Badness(poppies,sunflowers);
      Info(InfoTom,1,"Badness: ",Float(badness)," before step ",i," of ",
           steps,"...");
      Info(InfoTom,1,"Have ",Length(s!.poppies),"/",Length(poppies),
           " poppies and ",Length(s!.sunflowers),"/",Length(sunflowers),
           " sunflowers.");
      if Runtime()-starttime > timeout then 
          Info(InfoTom,1,"Timeout reached, giving up...");
          return;
      fi;
      backup := StructuralCopy(s!.except);
      corr := FindCorrection(s,poppies,sunflowers);
      best := 0;
      for j in [1..Length(factors)] do
          if j > 1 then
              s!.except := StructuralCopy(backup);
          fi;
          if factors[j] = "ratapprox" then
              ApproximateExceptions(s,3600);
          else
              ApplyCorrections(s,corr,factors[j]);
          fi;
          RecomputeFlowerCurvature(s,poppies,sunflowers);
          newbadness := Badness(poppies,sunflowers);
          if newbadness < badness then
              Info(InfoTom,3,"Factor ",factors[j]," improves badness to ",
                   Float(newbadness),".");
              badness := newbadness;
              best := j;
          fi;
      od;
      if best = 0 then
          Info(InfoTom,1,"No correction made it better, giving up.");
          s!.except := backup;
          RecomputeFlowerCurvature(s,poppies,sunflowers);
          return;
      fi;
      if factors[best] <> "ratapprox" then
          s!.except := backup;
          ApplyCorrections(s,corr,factors[best]);
      fi;
      Sunflower(s,5000,timeout-(Runtime()-starttime));
      RemoveForbiddenSunflowers(s);
      Poppy(s);
      RemoveForbiddenPoppies(s);

      if Length(s!.poppies) = 0 and Length(s!.sunflowers) = 0 then
          Info(InfoTom,1,"Success! All done.");
          return;
      fi;

      Append(sunflowers,s!.sunflowers);
      if Length(sunflowers) > 0 then
          Sort(sunflowers);
          w := 2;
          for j in [2..Length(sunflowers)] do
              if sunflowers[j-1] <> sunflowers[j] then
                  sunflowers[w] := sunflowers[j];
                  w := w + 1;
              fi;
          od;
          sunflowers := sunflowers{[1..w-1]};
      fi;

      Append(poppies,s!.poppies);
      if Length(poppies) > 0 then
          Sort(poppies);
          w := 2;
          for j in [2..Length(poppies)] do
              if poppies[j-1] <> poppies[j] then
                  poppies[w] := poppies[j];
                  w := w + 1;
              fi;
          od;
          poppies := poppies{[1..w-1]};
      fi;
  od;
  Error();
  Info(InfoTom,1,"No success, giving up after ",steps," steps.");
end;

GradientApproximateGoodOfficer := function(s,steps,timeout,Y,dY,prec)
  # Idea: Take the poppies and sunflowers, compute a gradient and then
  # apply that one with different factors, take the best and repeat.
  # Also try a rational approximation with small denominators as an 
  # alternative.
  # Y is a function in one variable used in the badness function
  # dY must be its derivative
  # prec is an integer for the precision of the rational approximation
  # We assume that poppy and sunflower have just run with the current
  # exceptions.
  local backup,badness,best,factors,grad,i,j,newbadness,norm,poppies,
        starttime,sunflowers,w;
  starttime := Runtime();
  poppies := Set(s!.poppies);
  sunflowers := Set(s!.sunflowers);
  if Length(poppies) + Length(sunflowers) = 0 then
      Info(InfoTom,1,"Nothing to do, no poppies or sunflowers!");
      return;
  fi;
  factors := [1/30,1/10,1/5,3/5,1,2,3];
  for i in [1..steps] do
      badness := Badness(poppies,sunflowers,Y);
      #Error();
      if i < 5 then 
          factors := [1/5];
      elif badness * 30 < 1 then
          factors := [1/30,1/5,3/5,1,3/2,2];
      else
          factors := [1/30,1/5,3/5];
          #factors := [1/30,1/10,1/5,3/5,1,2,3];
      fi;
      Info(InfoTom,1,"Badness: ",Float(RationalApproximation(badness,10^20)),
                     " before step ",i," of ",steps,"...");
      Info(InfoTom,1,"Have ",Length(s!.poppies),"/",Length(poppies),
           " poppies and ",Length(s!.sunflowers),"/",Length(sunflowers),
           " sunflowers.");
      if Runtime()-starttime > timeout then 
          Info(InfoTom,1,"Timeout reached, giving up...");
          return;
      fi;
      backup := s!.except;
      grad := FindGradient(s,poppies,sunflowers,dY);
      norm := -badness/Sum(grad.gradient,x->x^2);
      best := 0;
      badness := 10^20;
      for j in [1..Length(factors)] do
          s!.except := StructuralCopy(backup);
          ApplyGradient(s,grad,factors[j]*norm);
          ApproximateExceptions(s,prec);
          Sunflower(s,5000,timeout-(Runtime()-starttime));
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
                   Float(RationalApproximation(newbadness,10^20)),".");
              badness := newbadness;
              best := j;
              #Error(2);
          else
              Info(InfoTom,2,"Factor ",factors[j]," worsens badness to ",
                   Float(RationalApproximation(newbadness,10^20)),".");
              #Error(3);
          fi;
      od;
      if best = 0 then
          Info(InfoTom,1,"No correction made it better, giving up.");
          s!.except := backup;
          RecomputeFlowerCurvature(s,poppies,sunflowers);
          return;
      fi;
      Info(InfoTom,1,"Used factor ",factors[best]);
      s!.except := backup;
      ApplyGradient(s,grad,factors[best]*norm);
      ApproximateExceptions(s,prec);
      Sunflower(s,5000,timeout-(Runtime()-starttime));
      RemoveForbiddenSunflowers(s);
      Poppy(s);
      RemoveForbiddenPoppies(s);

      #poppies := s!.poppies;
      #sunflowers := s!.sunflowers;

      RecomputeFlowerCurvature(s,poppies,sunflowers);

      Append(sunflowers,s!.sunflowers);
      if Length(sunflowers) > 0 then
          Sort(sunflowers);
          w := 2;
          for j in [2..Length(sunflowers)] do
              if sunflowers[j-1] <> sunflowers[j] then
                  sunflowers[w] := sunflowers[j];
                  w := w + 1;
              fi;
          od;
          sunflowers := sunflowers{[1..w-1]};
      fi;

      Append(poppies,s!.poppies);
      if Length(poppies) > 0 then
          Sort(poppies);
          w := 2;
          for j in [2..Length(poppies)] do
              if poppies[j-1] <> poppies[j] then
                  poppies[w] := poppies[j];
                  w := w + 1;
              fi;
          od;
          poppies := poppies{[1..w-1]};
      fi;
  od;
  Info(InfoTom,1,"No success, giving up after ",steps," steps.");
  Error();
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
  DoAll(s,1000,60000);
  GradientApproximateGoodOfficer(s,10000,1000000,Ymaxsq,dYmaxsq,1000000);
end;

clean := function(l)
  local i;
  if IsList(l) then
     return List(l,clean);
  elif IsInt(l) then return l; 
  else return Float(l); fi;
end;
