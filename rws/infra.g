infra2 := InfraStructure("RST","SRT",[["SS","R"],["RR","S"]],
  function( i, a, b ) 
    local la, lb;
    la := Length(a);
    lb := Length(b);
    if   la > lb then return -1;
    elif la = lb then return 0;
    else              return 1;
    fi;
  end, rec() );

infra := InfraStructure("RST","SRT",[["SS","R"],["RR","S"]],
                        CompareByWeights, rec( weights := [17,18,17] ));
