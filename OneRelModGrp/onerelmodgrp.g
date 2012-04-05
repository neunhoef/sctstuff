uplimit := 2^22-1;  # Always use 2^n-1
timeout := 2;   # 100;

Flip := function(a)
  local b,i,n;
  n := LogInt(a,2);
  b := 1;
  for i in [1..n] do
    if IsEvenInt(a) then
      b := b * 2;
      a := a / 2;
    else
      b := b * 2 + 1;
      a := (a-1)/2;
    fi;
  od;
  return b;
end;

FlipInv := function(a)
  local b,i,n;
  n := LogInt(a,2);
  b := 1;
  for i in [1..n] do
    if IsEvenInt(a) then
      b := b * 2 + 1;
      a := a / 2;
    else
      b := b * 2;
      a := (a-1)/2;
    fi;
  od;
  return b;
end;

IsoFriend := function(a)
  local b,i,n;
  n := LogInt(a,2);
  b := 2^n;
  for i in [0..n-1] do
    if IsEvenInt(a) then
      b := b + 2^i;
      a := a / 2;
    else
      a := (a-1)/2;
    fi;
  od;
  return b;
end;

Index2Friend := function(a)
  local b,i,n,flip;
  n := LogInt(a,2);
  b := 2^n;
  flip := true;
  for i in [0..n-1] do
    if IsEvenInt(a) then
      if flip then b := b + 2^i; fi;
      a := a / 2;
    else
      if not flip then b := b + 2^i; fi;
      a := (a-1)/2;
    fi;
    flip := not(flip);
  od;
  return b;
end;
Rot := function(a)
  local n;
  n := LogInt(a,2);
  if IsEvenInt(a) then
    return (a/2)+2^(n-1);
  else
    return ((a-1)/2)+2^n;
  fi;
end;

RotateWord := function( w, pos )
    local l;
    if pos = 1 then return ShallowCopy(w); fi;
    l := Length(w);
    return Concatenation(w{[pos..l]},w{[1..pos-1]});
end;

CompareRotation := function( v, a, w, b )
    # v and w two (can be the same) words of equal length.
    # This compares the rotation of v starting at a
    # with the rotation of w starting at b: it returns -1 if the first
    # is lex-smaller, 0 if they are equal and +1 if the second is
    # lex-smaller.
    local i;
    for i in [1..Length(w)] do
      if v[a] < w[b] then return -1;
      elif v[a] > w[b] then return 1; fi;
      a := a + 1; if a > Length(v) then a := 1; fi;
      b := b + 1; if b > Length(w) then b := 1; fi;
    od;
    return 0;
end;

BinaryGroupNumber := function( n )
    local l;
    l := [];
    while n > 1 do
        if IsOddInt(n) then
            Add(l,1);
            n := (n-1)/2;
        else
            Add(l,0);
            n := n/2;
        fi;
    od;
    return Reversed(l);
end;

GroupNumberBinary := function( l )
    local i,n;
    n := 1;
    for i in [1..Length(l)] do
        n := n * 2 + l[i];
    od;
    return n;
end;

NecklaceReduceBinaryString := function(w)
    local i,minrot,minword,wi;
    # Now find the lexicographically smallest rotated one:
    minrot := 1;
    for i in [2..Length(w)] do
      if CompareRotation(w,i,w,minrot) = -1 then
        minrot := i;
      fi;
    od;
    # Now consider the inverse word:
    minword := w;
    wi := 1-Reversed(w);
    for i in [1..Length(wi)] do
      if CompareRotation(wi,i,minword,minrot) = -1 then
        minword := wi;
        minrot := i;
      fi;
    od;
    return RotateWord(minword,minrot);
end;

WithFuncs := function(p,f) return f(p); end;

LoadPackage("orb");
LoadPackage("ace");

MakeOrbits := function(uplimit)
    local a,done,o,orbs;
    orbs := [];
    done := BlistList([1..uplimit],[1]);

    while true do
        a := Position(done,false);
        #Print("Doing ",a,"..., having ", Sum(orbs,Length),".\n");
        if a = fail then return orbs; fi;
        o := Orb([Rot,FlipInv],a,WithFuncs,rec(hashlen := 101));
        Enumerate(o);
        Add(orbs,Set(AsList(o)));
        for a in o do
            done[a] := true;
        od;
    od;
end;

OneRelatorQuotientOfModularGroup := function(n)
  local S,T,f,l,rels;
  f := FreeGroup("S","T");
  S := GeneratorsOfGroup(f)[1];
  T := GeneratorsOfGroup(f)[2];
  rels := [S^3,T^2];
  l := [];
  if n > 1 then
      while n > 1 do
          if IsOddInt(n) then
              Add(l,S^2*T);
              n := (n-1)/2;
          else
              Add(l,S*T);
              n := n/2;
          fi;
      od;
      Add(rels,Product(Reversed(l)));
  fi;
  return [f,rels,f/rels];
end;

TryTC := function(n)
  local ct,g,time,workspace;
  g := OneRelatorQuotientOfModularGroup(n);
  workspace := 10000000;
  time := 60;
  while true do
      #Print("Running ACE, workspace=",workspace,"...\n");
      ct := ACEStats(GeneratorsOfGroup(g[1]),g[2],[]
                     :time := time, workspace := workspace);
      if ct.index <> 0 then 
          ct := ACECosetTable(GeneratorsOfGroup(g[1]),g[2],[]
                     :time := time, workspace := workspace, silent);
          if ct <> fail then return Size(Group(List(ct,PermList))); fi;
      fi;
      workspace := workspace*2;
      if workspace > 1000000000 then workspace := 1000000000; fi;
      time := time + 60;
  od;
end;

TryTCOnce := function(n)
  local ct,g,max,time,workspace;
  g := OneRelatorQuotientOfModularGroup(n);
  workspace := 1000000000;
  time := 120;
  max := 300000000;
  ct := ACEStats(GeneratorsOfGroup(g[1]),g[2],[]
                 :max := max, time := time, workspace := workspace,
                  felsch := true);
  if ct.index <> 0 then 
      return ct.index;
  else
      return fail;
  fi;
end;

TryLI := function(n)
  local ab,g,h,it,lowindex,oldlowindex;
  g := OneRelatorQuotientOfModularGroup(n);
  lowindex := 5;
  oldlowindex := 1;
  ab := AbelianInvariants(g[3]);
  if 0 in ab then return true; fi;
  while true do
      #Print("Running Low Index, limit=",lowindex,"...\n");
      it := LowIndexSubgroupsFpGroupIterator(g[3],lowindex);
      for h in it do
          if Index(g[3],h) > oldlowindex then
              ab := AbelianInvariants(h);
              if 0 in ab then return "infinite"; fi;
          fi;
      od;
      oldlowindex := lowindex;
      lowindex := lowindex + 5;
  od;
end;

Try := function(n,timeout)
  local res;
  res := ParTakeFirstResultByFork([TryTC,TryLI],[[n],[n]],
              rec( TimeOut := rec( tv_sec := timeout, tv_usec := 0 ) ));
  if IsBound(res[1]) then
      return res[1];
  elif IsBound(res[2]) then
      return res[2];
  else
      return fail;
  fi;
end;

orbs := [];
reps := [];
res := [];

Initwork := function()
    orbs := MakeOrbits(uplimit);
    reps := List(orbs,x->x[1]);
    res := EmptyPlist(Length(reps));
    Print("Have a total of ",Length(reps)," representatives to check.\n");
end;

Dowork := function(r)
  local i,n;
  for i in r do
    if not IsBound(res[i]) or res[i] = fail then
        n := reps[i];
        Print("n=",n," \c");
        r := Try(n,timeout);
        res[i] := r;
        Print("Result: ",r,"\n");
    fi;
  od;
end;

DoworkTC := function(r)
  local i,n;
  for i in r do
    if not IsBound(res[i]) or res[i] = fail then
        n := reps[i];
        Print("n=",n," \c");
        r := TryTCOnce(n);
        res[i] := r;
        Print("Result: ",r,"\n");
    fi;
  od;
end;

Savework := function()
  PrintTo("/home/neunhoef/SCT/OneRelModGrp/result.g",
          "orbs := ",orbs,";\n",
          "reps := ",reps,";\n",
          "res := ",res,";\n");
end;

Loadwork := function()
  Read("/home/neunhoef/SCT/OneRelModGrp/result.g");
end;

Print("Use Initwork(); to start the work.\n");
Print("Use Dowork(RANGE); to do the work.\n");
Print("Use Savework(); to save results to disk.\n");
Print("Use Loadwork(); to load previously saved results from disk.\n");

Canonicalise := function(n)
  local bs,can,pos;
  bs := BinaryGroupNumber(n);
  bs := NecklaceReduceBinaryString(bs);
  can := GroupNumberBinary(bs);
  # Now check:
  pos := Position(reps,can);
  if not(n in orbs[pos] and orbs[pos][1] = can) then
      Error("something stinks");
  fi;
  return can;
end;

PrettyPrintGroup := function(n)
  local bs,friend,friend2,gens,gens2,havesmall,i,isofriend,len,r;
  i := Position(reps,n);
  if i = fail then Error("not a representative"); fi;
  if IsBound(res[i]) then r := res[i]; else r := "notdone"; fi;
  isofriend := Canonicalise(IsoFriend(n));
  if isofriend < n then return; fi;
  bs := BinaryGroupNumber(n);
  len := Length(bs);
  if IsEvenInt(len) then
      friend := Canonicalise(Index2Friend(n));
      friend2 := Canonicalise(IsoFriend(friend));
      if friend < n or friend2 < n then return; fi;
  fi;
  Print(String(n,9)," ",String(r,-9));
  for i in [1..len] do Print(bs[i]); od;
  Print(String(isofriend,9));
  if IsEvenInt(len) then
      Print(String(friend,9),String(friend2,9));
  fi;
  Print("\n               ",Flip(n)," small:");
  havesmall := false;
  gens := [(),(1,2)];
  gens2 := [gens[1]*gens[2],gens[1]^2*gens[2]];
  if IsOne(Product(gens2{bs+1})) then
    if havesmall then Print(","); fi; havesmall := true;
    Print("2");
  fi;
  gens := [(1,2,3),()];
  gens2 := [gens[1]*gens[2],gens[1]^2*gens[2]];
  if IsOne(Product(gens2{bs+1})) then
    if havesmall then Print(","); fi; havesmall := true;
    Print("3");
  fi;
  gens := [(1,2,3),(1,2)];
  gens2 := [gens[1]*gens[2],gens[1]^2*gens[2]];
  if IsOne(Product(gens2{bs+1})) then
    if havesmall then Print(","); fi; havesmall := true;
    Print("S3");
  fi;
  gens := [(2,3,4),(1,2)];
  gens2 := [gens[1]*gens[2],gens[1]^2*gens[2]];
  if IsOne(Product(gens2{bs+1})) then
    if havesmall then Print(","); fi; havesmall := true;
    Print("S4");
  fi;
  gens := [(2,3,5),(1,2)(4,5)];
  gens2 := [gens[1]*gens[2],gens[1]^2*gens[2]];
  if IsOne(Product(gens2{bs+1})) then
    if havesmall then Print(","); fi; havesmall := true;
    Print("A5");
  fi;
  gens := [(2,3,4),(1,2)(3,4)];
  gens2 := [gens[1]*gens[2],gens[1]^2*gens[2]];
  if IsOne(Product(gens2{bs+1})) then
    if havesmall then Print(","); fi; havesmall := true;
    Print("A4");
  fi;
  gens := [(2,3,4)(5,6,7),(1,2)(3,5)];
  gens2 := [gens[1]*gens[2],gens[1]^2*gens[2]];
  if IsOne(Product(gens2{bs+1})) then
    if havesmall then Print(","); fi; havesmall := true;
    Print("L2(7)");
  fi;
  gens := [ (1,2,11)(3,5,10)(6,8,9), (2,10)(3,4)(5,9)(6,7) ];
  gens2 := [gens[1]*gens[2],gens[1]^2*gens[2]];
  if IsOne(Product(gens2{bs+1})) then
    if havesmall then Print(","); fi; havesmall := true;
    Print("L2(11)");
  fi;
  Print("\n");
end;

InterestingResult := function(n)
  local i,r;
  i := Position(reps,n);
  if i = fail then Error("must be a representative"); fi;
  if not(IsBound(res[i])) then r := fail; else r := res[i]; fi;
  return r = fail or r = "infinite" or 
         (IsInt(r) and r > 15000);
end;

