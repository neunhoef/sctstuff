# This implements what is laid out in roughplan.txt

DeclareInfoClass("InfoSeb");
SetInfoLevel(InfoSeb,1);
SetAssertionLevel(1);

# Put Cayley-Pongo-Code here, extend by test for cancellativeness
# and cancellation routine.
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
  # Use rewrites to prove that there is a diagram with this cycword as
  # beach boundary word. Uses the rewrites (how exactly?) and
  # recursion to either answer fail if it cannot do it better
  # or an area value < areabound if it could do it better.

end;

RemoveForbiddenEdges := function(s)
  # Removes (half-)edges which are forbidden by the rewrites given.
  # ?

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


