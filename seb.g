# This implements what is laid out in roughplan.txt

DeclareInfoClass("InfoSeb");
SetInfoLevel(InfoSeb,1);
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

# Possibly rip code to find primitive word and power from somewhere

MakeSebProblem := function(pongo, invtab, relators, rewrites)
  # Essentially just puts together a record, which it returns
  return rec( pongo := pongo, invtab := invtab, relators := relators,
              rewrites := rewrites, issebproblem := true );
end;

InstallMethod( ViewObj, "for a seb problem",
  [IsRecord],
  function(s)
    if not IsBound(s.issebproblem) then
        TryNextMethod();
    fi;
    Print("<seb problem ",Length(s.relators)," rels");
    if IsBound(s.halfedges) then
        Print(", ",Length(s.halfedges)," halfedges");
    fi;
    Print(">");
  end );

InverseRelator := function(pongo,invtab,r)
  local pw,x,y;
  if not(IsCancellative(pongo)) then Error(); fi;
  pw := [];
  y := r.primword[1];
  for x in Reversed(r.primword) do
    Add(pw, [ Complement(pongo,y[1]), Complement(invtab,x[2]) ] );
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

IsCompletable := function(s,x)
  # Do not call IsCompletable until after calling ComputeEdges
  local p;
  if IsCancellative(s.pongo) then
     return Complement(s.pongo,x) in s.relatorspongoelements; 
  fi;
  for p in PongoInverses(s.pongo,x) do
    if p in s.relatorspongoelements then return true; fi;
  od;
  return false;
end;

ComputeEdges := function(s)
  # Takes a Seb-Problem and computes all (half-)edges avoiding inverse
  # registration.
  # Stores a component ".halfedges" with the result
  local c,cppa,he1,he2,hel,i,i1,i2,j1,j2,l,m,nppa,p1,p2,r,r1,r1l,r2,r2l,v;
  Info(InfoSeb,1,"Computing edges...");

  s.relatorspongoelements := [];
  for i1 in [1..Length(s.relators)] do
    r1 := s.relators[i1];
    for p1 in [1..Length(r1.primword)] do
      AddSet(s.relatorspongoelements,r1.primword[p1][1]);
    od;
  od;

  s.halfedges := [];
  for i1 in [1..Length(s.relators)] do
    r1 := s.relators[i1];
    for i2 in [i1..Length(s.relators)] do
      r2 := s.relators[i2];
      for p1 in [1..Length(r1.primword)] do
        if i1=i2 then r := [p1..Length(r2.primword)];
                 else r := [1..Length(r2.primword)]; fi;
        for p2 in r do
          cppa := IsCompletable(s, PongoMult(s.pongo,
                                r2.primword[p2][1], r1.primword[p1][1]) );
          hel := [];
          r1l := RelatorLength(r1);
          r2l := RelatorLength(r2);
          m := Minimum(r1l,r2l);
          for l in [1..m] do 
            j1 := IndexPrimWord(r1,p1+(l-1));
            j2 := IndexPrimWord(r2,p2-(l-1));
            if r1.primword[j1][2] <> 
               Complement(s.invtab,r2.primword[IndexPrimWord(r2,j2-1)][2]) then 
              break; 
            fi;
            nppa := IsCompletable(s, 
                       PongoMult(s.pongo,
                                 r1.primword[IndexPrimWord(r1,j1+1)][1],
                                 r2.primword[IndexPrimWord(r2,j2-1)][1]) );
            for v in [[3,3],[3,4],[4,3],[4,4]] do
              if (not(nppa) and v[2]=3) then continue; fi;
              if (not(cppa) and v[1]=3) then continue; fi;
              if v = [4,3] and i1=i2 and p1=p2 then continue; fi;
              c := -1 + 1/v[1] + 1/v[2];
              he1 := rec( relator := i1, start := p1, 
                          length := l, valency := v[1], 
                          contrib := c * r2l / (r1l+r2l) ); 
              he2 := rec( relator := i2, start := IndexPrimWord(r2,p2-l), 
                          length := l, valency := v[2],
                          contrib := c * r1l / (r1l+r2l) ); 
              Add(hel, he1); 
              i := Length(s.halfedges) + Length(hel);
              if (i1=i2 and p1=p2 and v[1]=v[2]) then
                 he1.complement := i; 
              else 
                 he1.complement := i+1;
                 he2.complement := i;
                 Add(hel, he2);
              fi;
            od;
            if not(IsAccepting(s.pongo,
                     PongoMult(s.pongo,r1.primword[IndexPrimWord(r1,j1+1)][1],
                               r2.primword[IndexPrimWord(r2,j2-1)][1]))) then
                break;
            fi;
            if (l=m) then hel := []; fi;
          od;
          Append(s.halfedges, hel);
        od;
      od;
    od;
  od;
  Info(InfoSeb,1,"Number of halfedges: ",Length(s.halfedges),".");
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
  Cancel(s.pongo,s.invtab,cw);
  if Length(cw) = 0 then return 0; fi;
  # Now see if it is equal to one of the relators with less area:
  for r in [1..Length(s.relators)] do
      rel := s.relators[r];
      len := Length(rel.primword)*rel.power;
      if rel.area < areabound and len = Length(cw) then
          for n in [1..Length(rel.primword)] do
              posrel := n;
              poscw := 1;
              count := 0;
              while count < len do
                  if not IsAccepting(s.pongo,PongoMult(s.pongo,cw[poscw][1],
                                     rel.primword[posrel][1])) then
                      break;
                  fi;
                  poscw := ReduceModBase1(poscw-1,len);
                  if cw[poscw][2] <> 
                     Complement(s.invtab,rel.primword[posrel][2]) then
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

  for r in [1..Length(s.rewrites)] do
      # Try all rewrites
      rewr := s.rewrites[r];
      rel := s.relators[rewr.relator];
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
                     Complement(s.invtab,rel.primword[posrel][2]) then
                      match := false; break;
                  fi;
                  match := match+1;   # number of matched letters
                  posrel := IndexPrimWord(rel,posrel+1);
                  if match >= rewr.length then
                      match := true; break;
                  fi;
                  if not(IsAccepting(s.pongo,
                             PongoMult(s.pongo,cw[poscw][1],
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
                  newcw2 := EmptyPlist(rel.length-rewr.length+1);
                  Add(newcw2,[PongoMult(s.pongo,rel.primword[posrel][1],
                                                cw[poscw][1]),
                              Complement(s.invtab,rel.primword[posrel][2])]);
                  for i in [1..rel.length-rewr.length-1] do
                      posrel := IndexPrimWord(rel,posrel+1);
                      Add(newcw2,ShallowCopy(rel.primword[posrel]));
                  od;
                  posrel := IndexPrimWord(rel,posrel+1);
                  Assert(1,posrel = rewr.notchtype);
                  Add(newcw2,[PongoMult(s.pongo,cw[p][1],
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
  he1 := s.halfedges[halfedge];
  rel1 := s.relators[he1.relator];
  he2 := s.halfedges[he1.complement];
  rel2 := s.relators[he2.relator];

  pos1 := he1.start;
  pos2 := IndexPrimWord(rel2,he2.start + he2.length);
  surf := [];
  pair := [Complement(s.pongo,
                      PongoMult(s.pongo,rel2.primword[pos2][1],
                                        rel1.primword[pos1][1])),0];
  pos1 := IndexPrimWord(rel1,pos1-1);
  pair[2] := Complement(s.invtab,rel1.primword[pos1][2]);
  Add(surf,pair);
  for i in [1..Length(rel1.primword)*rel1.power-he1.length-1] do
      pair := [Complement(s.pongo,rel1.primword[pos1][1]),0];
      pos1 := IndexPrimWord(rel1,pos1-1);
      pair[2] := Complement(s.invtab,rel1.primword[pos1][2]);
      Add(surf,pair);
  od;
  pos2 := he2.start;
  pair := [Complement(s.pongo,
                      PongoMult(s.pongo,rel1.primword[pos1][1],
                                        rel2.primword[pos2][1])),0];
  pos2 := IndexPrimWord(rel2,pos2-1);
  pair[2] := Complement(s.invtab,rel2.primword[pos2][2]);
  Add(surf,pair);
  for i in [1..Length(rel2.primword)*rel2.power-he2.length-1] do
      pair := [Complement(s.pongo,rel2.primword[pos2][1]),0];
      pos2 := IndexPrimWord(rel2,pos2-1);
      pair[2] := Complement(s.invtab,rel2.primword[pos2][2]);
      Add(surf,pair);
  od;
  return surf;
end;

RemoveForbiddenEdges := function(s)
  # Removes (half-)edges which are forbidden by the rewrites given.
  local area,e,he1,he2,i,newnumbers,pair,pos1,pos2,rel1,rel2,surf,tokeep,toremove;
  Info(InfoSeb,1,"Removing forbidden (half-)edges...");
  toremove := [];
  for e in [1..Length(s.halfedges)] do
      he1 := s.halfedges[e];
      rel1 := s.relators[he1.relator];
      he2 := s.halfedges[he1.complement];
      rel2 := s.relators[he2.relator];
      surf := HamburgerSurf(s,e);
      area := CanYouDoThisWithSmallerArea(s,surf,rel1.area+rel2.area);
      if area <> fail then
          AddSet(toremove,e);
          AddSet(toremove,he1.complement);
      fi;
  od;
  tokeep := Difference([1..Length(s.halfedges)],toremove);
  newnumbers := 0*[1..Length(s.halfedges)];
  for i in [1..Length(tokeep)] do
      newnumbers[tokeep[i]] := i;
  od;
  for i in [1..Length(toremove)] do
      newnumbers[toremove[i]] := i;
  od;
  s.halfedgesremoved := s.halfedges{toremove};
  s.halfedges := s.halfedges{tokeep};
  for i in [1..Length(s.halfedges)] do
      s.halfedges[i].complement := newnumbers[s.halfedges[i].complement];
  od;
  for i in [1..Length(s.halfedgesremoved)] do
      s.halfedgesremoved[i].complement := 
         newnumbers[s.halfedgesremoved[i].complement];
  od;
  Info(InfoSeb,1,"Have removed ",Length(toremove)," halfedges.");
end;

# This is now old:
FindInternalSegments := function(s)
  # Runs through halfedges and produces the segments which are the
  # input to sunflower.
  local e,he,he2,seg,segs;
  Info(InfoSeb,1,"Finding internal segments...");
  # Segment database is indexed by relator and then notchtype.
  # Each entry is a list of segment records, at first indexed by the
  # length of the segment, in the end, we compactify this list and
  # sort it by the maximal contribution in non-ascending order.
  s.segs := List([1..Length(s.relators)],
                 r->List([1..Length(s.relators[r].primword)],j->[]));
  segs := s.segs;
  for e in [1..Length(s.halfedges)] do
      he := s.halfedges[e];
      he2 := s.halfedges[he.complement];
      if not(IsBound(segs[he.relator][he.start][he.length])) then
          seg := rec( relator := he.relator, start := he.start, 
                      length := he.length, valbegin := he.valency,
                      valend := he2.valency, maxcontrib := he.contrib,
                      halfedges := [e] );
          segs[he.relator][he.start][he.length] := seg;
      else
          seg := segs[he.relator][he.start][he.length];
          if he.contrib > seg.maxcontrib then
              seg.valbegin := he.valency;
              seg.valend := he2.valency;
              seg.maxcontrib := he.contrib;
          fi;
          Add(seg.halfedges,e);
      fi;
      # Now the edge as it is has taken part in the maximisation.
      # However, this edge could be Steve-distance one from the boundary.
      if IsBound(he.altcontrib) and
         he.altcontrib > seg.maxcontrib then
          seg.valbegin := he.valency;
          seg.valend := he2.valency;
          seg.maxcontrib := he.altcontrib;
      fi;
  od;
end;

# This is now old:
IndexInternalSegments := function(s)
  # Does some sensible indexing and sorting for sunflower.
  local l,p,r;
  Info(InfoSeb,1,"Indexing internal segments...");
  for r in [1..Length(s.relators)] do
      for p in [1..Length(s.relators[r].primword)] do
          l := Compacted(s.segs[r][p]);
          Sort(l,function(a,b) return a.maxcontrib > b.maxcontrib; end);
          s.segs[r][p] := l;
      od;
  od;
end;

# This is now old:
Sunflower := function(s)
  # Find all curved sunflowers based on internal segments.
  Info(InfoSeb,1,"Running sunflower...");
  s.sunflowers := [];
  #...
  Info(InfoSeb,1,"Sunflower done, found ",Length(s.sunflowers), 
       " sunflowers.");
end;

InitialiseSegmentMatrices := function(s)
  local i,j,r;
  s.segmats := [];
  for i in [1..Length(s.relators)] do
    r := s.relators[i];
    s.segmats[i] := [];
    for j in [1..Length(r.primword)] do
       s.segmats[i][j] := ListWithIdenticalEntries(RelatorLength(r), 
                                                   [-infinity,fail]);
    od;
  od;
end;

# GammaContribution := functions(s,hen)
#   local x,y;
#   x := s.halfedges[hen]
#   y := s.halfedges[x.complement];
#   c := -1 + 1/x + 1/y;
#   return ;
# end;

PutEdgesIntoSegmentMatrices := function(s)
  local c,e,he,hes,l,n,r,segmats;
  Info(InfoSeb,1,"Putting edges into segment matrices...");
  segmats := s.segmats;
  hes := s.halfedges;
  for e in [1..Length(hes)] do
      he := hes[e];
      r := he.relator;
      n := he.start;
      l := he.length;
      c := Maximum(he.contrib,-1/3);
      if c > segmats[r][n][l][1] then
          segmats[r][n][l] := [c,-e];
      fi;
  od;
  Info(InfoSeb,1,"Done.");
end;

FinaliseSegmentMatrices := function(s)
  local L,c,l,ll,m,max,maxll,n,nts,r,rel,segmats;
  Info(InfoSeb,1,"Finalising segment matrices...");
  s.sunflowers := 0;
  segmats := s.segmats;
  for r in [1..Length(s.relators)] do
      Info(InfoSeb,2,"Doing relator ",r);
      rel := s.relators[r];
      L := Length(rel.primword)*rel.power;
      nts := Length(rel.primword);
      for l in [2..L] do
          Info(InfoSeb,3,"Doing length ",l);
          for n in [1..nts] do
              max := segmats[r][n][l][1];
              maxll := 0;
              for ll in [1..l-1] do
                  # ll is the length of the first step
                  m := IndexPrimWord(rel,n+ll);
                  c := segmats[r][n][ll][1] + segmats[r][m][l-ll][1]; 
                  if c > max then 
                      max := c; 
                      maxll := ll;
                  fi;
              od;
              if maxll > 0 then
                  segmats[r][n][l] := [max,maxll];
              fi;
          od;
      od;
      for n in [1..nts] do
        if (segmats[r][n][L][1] > -1) then s.sunflowers := s.sunflowers + 1; fi;
      od;
  od;
  s.segmats := segmats;
  Info(InfoSeb,1,"Done.  ",s.sunflowers," sunflowers.");
  return segmats;
end;

RemoveForbiddenSunflowers := function(s)
  # Does what it says.
  Info(InfoSeb,1,"Removing forbidden sunflowers...");

  Info(InfoSeb,1,"Sunflowers left: ",Length(s.sunflowers),".");
end;

FindNewRewrites := function(s)
  # Classify for each segment of a relator the largest curvature this
  # face could have if this segment is exposed on the boundary.
  # Only report positive such bounds.
  Info(InfoSeb,1,"Finding rewrites...");

  Info(InfoSeb,1,"Found ",Length(s.rewrites)," rewrites.");
end;

DoAll := function(s)
    ComputeEdges(s);
    RemoveForbiddenEdges(s);
    InitialiseSegmentMatrices(s);
    PutEdgesIntoSegmentMatrices(s);
    FinaliseSegmentMatrices(s);
    #RemoveForbiddenSunflowers(s);
    #FindNewRewrites(s);
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

MakeRandomPresentation := function(len, nrrels)
  # This function makes a truly random presentation of nrrels relators
  # of length len (syllables). This will be a modular group quotient:
  # <S,R,T|T^2=1=S^3=SR>
  # and relators will be STRTSTRT... where each S or R can be either S or R.
  # The inverse relators are given explicitly.
  local b,bb,f,i,r,rels,st,bytes,conv;
  #Print("Using /dev/random, if this is stuck, type something!\n");
  conv := function(x)
    if IntChar(x) >= 128 then return 2; else return 3; fi;
  end;
  f := IO_open("/dev/urandom",IO.O_RDONLY,0);
  rels := [];
  for i in [1..nrrels] do
      st := "";
      bytes := 0;
      while bytes < len do
          bytes := bytes + IO_read(f,st,bytes,len-bytes);
      od;
      b := List(st,x->[conv(x),1]);
      AddSet(rels, rec( primword := b, power := 1, area := 1 ) );
  od;
  IO_close(f);
  return rels;
end;

pongo := CayleyPongo([[1,2,3],[2,3,1],[3,1,2]],1);
SetElementNames(pongo,"1SR");
invtab := PlainInvTab([1]);
SetElementNames(invtab,"T");

TrySeveral := function(lens,n)
  local l,i,j,k,rels,rewrites,s,sunflowers,b,m,biggies;
  sunflowers := [];  biggies := [];
  for l in lens do
    sunflowers[l] := [];   biggies[l] := [];
    for i in [1..n] do
      rels := MakeRandomPresentation(l,1);
      Append(rels, List(rels, x->InverseRelator(pongo,invtab,x) ) );
      rewrites := [];
      s := MakeSebProblem(pongo,invtab,rels,rewrites);
      DoAll(s);
      Add(sunflowers[l], s.sunflowers);
      b := Maximum(List(s.halfedges, x->x.length));
      m := Filtered(s.halfedges, x->x.length=b);
      if (b > l/4) then 
        Add(biggies[l], [b,m,s.sunflowers,s]);
      fi; 
    od; 
  od; 
  for l in lens do
    i := sunflowers[l];
    k := Filtered(i, x->not(IsZero(x)) );
    b := biggies[l];
    Print("Length ",l," has ",Length(k),"/",Length(i)," sunflowers : ",sunflowers[l],"\n");
    Print("  ",List(b,x->Length(x[2]))," halfedges of length ",List(b,x->x[1]),"/",l);
    # m := Minimum(List(b, x->Length(x[2])));
    # biggies[l] := Filtered(b, x->Length(x[2])=m);
  od;
  return biggies;
end;

AntiEdgeWord := function(p,e)
  local r,s,l;
  r := p.relators[e.relator];
  s := e.start+e.length+1;
  l := RelatorLength(r) - e.length;
  return List([s..s+l], x->r.primword[IndexPrimWord(r,x)]);
end;

Hamburger := function(p,e)
  return rec( power := 1, area := 1,
      primword := Concatenation( AntiEdgeWord(p,e),
          AntiEdgeWord(p,p.halfedges[e.complement]) )
  );
end;

TrySeveralTwice := function(lens,n)
  local l,i,j,k,rels,rewrites,s1,s2,sunflowers,b,m;
  sunflowers := [];
  for l in lens do
    sunflowers[l] := [];
    for i in [1..n] do
      rels := MakeRandomPresentation(l,1);
      Append(rels, List(rels, x->InverseRelator(pongo,invtab,x) ) );
      rewrites := [];
      s1 := MakeSebProblem(pongo,invtab,StructuralCopy(rels),rewrites);
      DoAll(s1); 
      b := Maximum(List(s1.halfedges, x->x.length));
      m := Filtered(s1.halfedges, x->x.length=b);
      for k in List(m, x->Hamburger(s1,x)) do
        AddSet(rels, k);
        AddSet(rels, InverseRelator(pongo,invtab,k) );
      od; 
      s2 := MakeSebProblem(pongo,invtab,StructuralCopy(rels),rewrites);
      DoAll(s2); 
      Add(sunflowers[l], [s1.sunflowers, b, Length(m), s2.sunflowers]);
    od; 
  od; 
  for l in lens do
    i := sunflowers[l]; 
    k := Filtered(i, x->not(IsZero(x[1])) );
    b := Filtered(i, x->not(IsZero(x[4])) );
    Print("Length ",l," has ",Length(b)," : ",Length(k)," / ",Length(i)," sunflowers : ",sunflowers[l],"\n");
  od;
end;


# rels := MakeRandomPresentation(l,1);
# Append(rels, List(rels, x->InverseRelator(pongo,invtab,x) ) );
# s := MakeSebProblem(pongo,invtab,rels,[]);
# DoAll(s);
# rp := Filtered(s.halfedges, x -> x.valency=3 and s.halfedges[x.complement].valency=3);
# List([1..15],y->Length(Filtered(rp, x->x.length=y)));





# rels := ParsePongoLetter(pongo,invtab,
#          ["(ST)^7:10",
#           "(RT)^7:10",
#           "(STRT)^13:10"]);
# rewrites := [];
#
# s := MakeSebProblem(pongo,invtab,rels,rewrites);

# rels2 := ParsePongoLetter(pongo,invtab,
#          ["(ST)^7:10",
#           "(RT)^7:10",
#           "(STRT)^13:10",
#           "(STRT)^11RT(ST)^4(RT)^2:29",
#           "(STRT)^11(ST)^2(RT)^4ST:29"
#          ]);
# s2 := MakeSebProblem(pongo,invtab,rels2,rewrites);


