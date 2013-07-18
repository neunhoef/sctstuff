Guck := function(gens,weights,earlyout)
  local bound,done,els,g,grpels,i,j,lows,n,newbound,newgrpels,newwords,
        nrdone,ok,pos,w,words,ww,x,xx;
  # Do not put duplicate generators or identity ones, because this is
  # silly.
  g := Group(gens);
  n := Length(gens);
  els := Elements(g);
  lows := EmptyPlist(Length(els));
  i := Position(els,One(g));
  lows[i] := [0,[]];
  done := BlistList([1..Length(els)],[i]);
  nrdone := 1;
  for i in [1..n] do
    lows[Position(els,gens[i])] := [weights[i],[i]];
  od;
  words := List([1..n],i->[weights[i],[i]]);
  grpels := ShallowCopy(gens);
  bound := Minimum(weights);
  ok := true;
  repeat
    #Print("Number of group elements done: ",nrdone,"\n");
    #Print("Have ",Length(words)," words to consider, minimum weight: ",
    #      bound,".\n");
    newwords := EmptyPlist(1000);
    newgrpels := EmptyPlist(1000);
    newbound := infinity;
    for i in [1..Length(words)] do
      w := words[i];
      x := grpels[i];
      for j in [1..n] do
        ww := [w[1]+weights[j],Concatenation(w[2],[j])];
        xx := x*gens[j];
        pos := Position(els,xx);
        if not(IsBound(lows[pos])) or lows[pos][1] > ww[1] then
          lows[pos] := ShallowCopy(ww);
        elif lows[pos][1] = ww[1] then
          Add(lows[pos],ww[2]);
        fi;
        Add(newwords,ww);
        Add(newgrpels,xx);
        if ww[1] < newbound then newbound := ww[1]; fi;
      od;
    od;
    words := newwords;
    grpels := newgrpels;
    bound := newbound;
    for i in [1..Length(els)] do
      if IsBound(lows[i]) and lows[i][1] < bound and not(done[i]) then
        done[i] := true;
        if Length(lows[i]) > 2 then ok := false; fi;
        nrdone := nrdone + 1;
      fi;
    od;
  until nrdone = Length(els) or (not(ok) and earlyout);
  return rec( g := g, gens := gens, lows := lows, ok := ok,
              els := els, 
              nrbad := Number([1..Length(els)], i->IsBound(lows[i])
                                                   and Length(lows[i])>2));
end;
