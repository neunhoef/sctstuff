# This implements what is laid out in roughplan.txt

DeclareInfoClass("InfoSeb");
SetInfoLevel(InfoSeb,1);
SetAssertionLevel(1);

# Put Cayley-Pongo-Code here, extend by test for cancellativeness
# and cancellation routine.
# Possibly rip code to find primitive word and power from somewhere

MakeSebProblem := function(pongo, invtab, relators, rewrites)
  # Essentially just puts together a record, which it returns

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


