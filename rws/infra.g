infra2 := InfraStructure("RST","SRT",[["SS","R"],["RR","S"]],
  function( i, a, b ) 
    local la, lb;
    la := Length(a);
    lb := Length(b);
    if   la < lb then return -1;
    elif la = lb then return 0;
    else              return 1;
    fi;
  end, rec() );

infra := InfraStructure("RST","SRT",[["SS","R"],["RR","S"]],
                        CompareByWeights, rec( weights := [17,18,17] ));

free := InfraStructure("ABab","abAB",[],CompareByWeights,
                       rec( weights := [17,18,17,18] ));

StringAssocWord := function(alph,ialph,w)
  local i,j,s;
  s := "";
  for i in [1,3..Length(w)-1] do
      if w[i+1] > 0 then
          for j in [1..w[i+1]] do
              Add(s,alph[w[i]]);
          od;
      else
          for j in [1..-w[i+1]] do
              Add(s,ialph[w[i]]);
          od;
      fi;
  od;
  return s;
end;
