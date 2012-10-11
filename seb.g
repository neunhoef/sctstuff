# This implements what is laid out in roughplan.txt

DeclareInfoClass("InfoSeb");
SetInfoLevel(InfoSeb,1);
SetAssertionLevel(1);

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
DeclareProperty("IsCancellative",IsPongo);
DeclareOperation("Complement",[IsPongo and IsCancellative,IsObject]);
DeclareOperation("Cancel",[IsPongo and IsCancellative, IsList, IsList]);
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
          p![2]," acceptors>");
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

# TODO: Test for cancellativity (makes complement table), computation
# of complements, and cancellation routine for cyclic words.

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
    Print("<seb problem>");
  end );

RelatorLength := function(r)
  return Length(r.primword) * r.power;
end;

IndexPrimWord := function(r,i)
  return RemInd(i,Length(r.primword));
end;

ComputeEdges := function(s)
  # Takes a Seb-Problem and computes all (half-)edges avoiding inverse
  # registration.
  # Stores a component ".halfedges" with the result
  local i1,i2,r1,r2,p1,p2,,j1,j2,he1,he2,l,m,i,hel;
  s.halfedges := [];
  for i1 in [1..Length(s.relators) do
    r1 := s.relators[i1];
    for i2 in [1..Length(s.relators) do
      r2 := s.relators[i2];
      for p1 in [1..Length(r1.primword)] do
        for p2 in [1..Length(r2.primword)] do
          hel := [];
          m := Min(RelatorLengthr(r1),RelatorLength(r2));
          for l in [1..m] do
            j1 := IndexPrimWord(r1,p1+l);
            j2 := IndexPrimWord(r1,p2+l)
            if (r1.primword[j1][2] = r2.primword[j2][2] and ) then break; fi;
            i := Length(s.halfedges) + Length(hel);
            he1 := rec( relator := r1, start := p1, length := l, ); 
            he2 := rec( relator := r2, start := p2, length := l, ); 
            Add(hel, he1);
            if () then
               he1.complement := i+1;
               he2.complement := i;
               Add(hel, he2);
            else 
               he1.complement := i; 
            fi;
            if (p1=p2 and l=m) then hel := []; fi
          od;
          Append(s.halfedges, hel);
        od;
      od;
    od;
  od;
end;

WeedoutValency3 := function(s)
  # Removes halfedges with a valency 3 end which cannot be.
  # This is only using the pongo.

end;

CanYouDoThisWithThisArea := function(s,cycword,areabound)
  # Use rewrites to check whether or not there is a diagram with this
  # cycword as beach boundary word and area less than areabound. Uses the
  # rewrites and recursion to either answer fail if it cannot do it
  # better or an area value < areabound if it could do it better.

end;

RemoveForbiddenEdges := function(s)
  # Removes (half-)edges which are forbidden by the rewrites given.
  toremove := [];
  for e in [1..Length(s.halfedges)] do
      he1 := s.halfedges[e];
      rel1 := s.relators[he1.relator];
      he2 := s.halfedges[he1.complement];
      rel2 := s.relators[he2.relator];

      # First make the surf word of the hamburger:
      surf := [];
      p :=

      area := CanYouDoThisWithThisArea(s,surf,rel1.area+rel2.area);
      if area <> fail then
          AddSet(toremove,e);
          AddSet(toremove,he1.complement);
      fi;
  od;
end;

FindInternalSegments := function(s)
  # Runs through halfedges and produces the segments which are the
  # input to sunflower.

end;

IndexInternalSegments := function(s)
  # Does some sensible indexing and sorting for sunflower.

end;

Sunflower := function(s)
  # Find all curved sunflowers based on internal segments.

end;

RemoveForbiddenSunflowers := function(s)
  # Does what it says.

end;

FindNewRewrites := function(s)
  # Classify for each segment of a relator the largest curvature this
  # face could have if this segment is exposed on the boundary.
  # Only report positive such bounds.

end;


