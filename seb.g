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

ComputeEdges := function(s)
  # Takes a Seb-Problem and computes all (half-)edges avoiding inverse
  # registration.
  # Stores a component ".halfedges" with the result

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

ReduceMod := function(rel,pos)
  # reduce to [1..Length(rel.primword)] mod Length(rel.primword)
  local primlen;
  primlen := Length(rel.primword);
  return ((pos-1) mod primlen)+1;
end;

RemoveForbiddenEdges := function(s)
  # Removes (half-)edges which are forbidden by the rewrites given.
  local area,e,he1,he2,i,pair,pos1,pos2,rel1,rel2,surf,toremove;
  Info(InfoSeb,1,"Removing forbidden (half-)edges...");
  toremove := [];
  for e in [1..Length(s.halfedges)] do
      he1 := s.halfedges[e];
      rel1 := s.relators[he1.relator];
      he2 := s.halfedges[he1.complement];
      rel2 := s.relators[he2.relator];

      # First make the surf word of the hamburger:
      pos1 := he1.start;
      pos2 := ReduceMod(rel2,he2.start + he2.length);
      surf := [];
      pair := [Complement(s.pongo,
                          PongoMult(s.pongo,rel2.primword[pos2][1],
                                            rel1.primword[pos1][1])),0];
      pos1 := ReduceMod(rel1,pos1-1);
      pair[2] := s.invtab[rel1.primword[pos1][2]];
      Add(surf,pair);
      for i in [1..Length(rel1.primword)*rel1.power-he1.length-1] do
          pair := [Complement(s.pongo,rel1.primword[pos1][1]),0];
          pos1 := ReduceMod(rel1,pos1-1);
          pair[2] := s.invtab[rel1.primword[pos1][2]];
          Add(surf,pair);
      od;
      pos2 := he2.start;
      pair := [Complement(s.pongo,
                          PongoMult(s.pongo,rel1.primword[pos1][1],
                                            rel2.primword[pos2][1])),0];
      pos2 := ReduceMod(rel2,pos2-1);
      pair[2] := s.invtab[rel2.primword[pos2][2]];
      Add(surf,pair);
      for i in [1..Length(rel2.primword)*rel2.power-he2.length-1] do
          pair := [Complement(s.pongo,rel2.primword[pos2][1]),0];
          pos2 := ReduceMod(rel2,pos2-1);
          pair[2] := s.invtab[rel2.primword[pos2][2]];
          Add(surf,pair);
      od;
      area := CanYouDoThisWithThisArea(s,surf,rel1.area+rel2.area);
      if area <> fail then
          AddSet(toremove,e);
          AddSet(toremove,he1.complement);
      fi;
  od;
  s.halfedgesremoved := s.halfedges{toremove};
  s.halfedges := s.halfedges{Difference([1..Length(s.halfedges)],toremove)};
  Info(InfoSeb,1,"Have removed ",Length(toremove)," halfedges.");
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


