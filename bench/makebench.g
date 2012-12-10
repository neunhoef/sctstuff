MakeBench := function(range,nr)
  local bench,bytes,f,i,k,l,len,n,st,x;

  f := IO_open("/dev/random",IO.O_RDONLY,0);
  
  bench := [];
  for n in range do
      Print("Doing n=",n,"...\n");
      l := [];
      bench[n] := l;
      for k in [1..nr] do
          x := 0;
          st := "";
          bytes := 0;
          len := 6;
          while bytes < len do
              bytes := bytes + IO_read(f,st,bytes,len-bytes);
          od;
          for i in [1..len] do
              x := x * 256 + IntChar(st[i]);
          od;
          x := x mod 2^n + 2^n;
          Add(l,rec( id := x ));
          Print("#\c");
      od;
      Print("\n");
  od;
  IO_close(f);
  return bench;
end;

AddStrings := function(bench)
  local i,n,r,st;
  for i in [1..Length(bench)] do
      if IsBound(bench[i]) then
          for r in bench[i] do
              n := r.id;
              st := "";
              while n > 1 do
                  if IsOddInt(n) then
                      Append(st,"TR");
                      n := (n-1)/2;
                  else
                      Append(st,"TS");
                      n := n/2;
                  fi;
              od;
              r.rel := Reversed(st);
          od;
      fi;
  od;
end;

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

AddPrimWord := function(bench)
  local i,r,st,x;
  for i in [1..Length(bench)] do
      if IsBound(bench[i]) then
          for r in bench[i] do
              st := Filtered(r.rel,x->x <> 'T');
              x := LexLeastRotation(st);
              r.primword := x[1];
              r.power := x[2];
          od;
      fi;
  od;
end;

AddPongoLetterRels := function(bench)
  local i,l,ll,n,r,rels;
  for i in [1..Length(bench)] do
      if IsBound(bench[i]) then
          for r in bench[i] do
              n := r.id;
              rels := [];
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
              r.rels := rels;
          od;
      fi;
  od;
end;
  
WriteBenchPart := function(bench,i)
  local name;
  name := Concatenation("SCTbench",String(i),".g");
  PrintTo(name,"SCTbench[",i,"] := ",bench[i],";\n");
end;

WriteBench := function(bench)
  local SCTbench,i,name;
  PrintTo("SCTbench.g","SCTbench := [];\n");
  for i in [1..Length(bench)] do
      if IsBound(bench[i]) then
          name := Concatenation("SCTbench",String(i),".g");
          AppendTo("SCTbench.g","Read(\"",name,"\");\n");
          WriteBenchPart(bench,i);
      fi;
  od;
end;

# SCTbench := MakeBench([15..50],15);
# AddStrings(SCTbench);
# AddPrimWord(SCTbench);
# AddPongoLetterRels(SCTbench);
# WriteBench(SCTbench);

PrettyPrintBench := function(bench)
  local i,j,r;
  for i in [1..Length(bench)] do
      if IsBound(bench[i]) then
          Print("========================================\n");
          Print(" Benchmark suite for SCT for length ",i,":\n");
          Print("========================================\n");
          Print("Nr|       ID       |",String("Primword",i),"|SIZ|TOM\n");
          for j in [1..Length(bench[i])] do
              r := bench[i][j];
              Print(String(j,2),"|",String(r.id,16),"|",r.primword,"|");
              if IsBound(r.finite) then
                  Print("FIN|");
              elif IsBound(r.infinite) then
                  Print("INF|");
              else
                  Print("???|");
              fi;
              if IsBound(r.tom) then
                  Print(r.tom);
              else
                  Print(" ? ");
              fi;
              Print("\n");
          od;
          Print("\n");
      fi;
  od;
end;
