DeclareInfoClass("InfoLEA");
SetInfoLevel(InfoLEA,1);
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

# Necklaces:
Necklace := function(id, primlen, power, name)
  return rec( id := id, primlen := primlen, power := power, name := name );
end;
IsNecklace := IsRecord;

# Half edge types:
HalfEdgeType := function(necklace, start, len, complement, depot, pongoelm)
  return rec(necklace := necklace, start := start, len := len, 
             complement := complement, depot := depot, pongoelm := pongoelm);
end;
IsHalfEdgeType := IsRecord;

# The following describes a LEA search:

DeclareOperation("LEASearch",
  [IsPongo,           # a pongo
   IsPosInt,          # circle
   IsList,            # list of necklaces
   IsList,            # list of half-edge-types
  ]);

IsLEASearch := IsRecord;

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


CreateHalfEdgeTypeIndex := function(s)
  local endpos,het,i,index,indexr,n;
  n := Length(s.necklaces);
  index := EmptyPlist(n);
  indexr := EmptyPlist(n);
  for i in [1..n] do
      index[i] := List([0..s.necklaces[i].primlen-1],j->[]);
      indexr[i] := List([0..s.necklaces[i].primlen-1],j->[]);
  od;
  for i in [1..Length(s.hetypes)] do
      het := s.hetypes[i];
      Add(index[het.necklace][het.start+1],i);
      endpos := (het.start+het.len) mod s.necklaces[het.necklace].primlen;
      Add(indexr[het.necklace][endpos+1],i);
  od;
  s.index := index;
  s.indexr := indexr;
end;

InstallMethod(LEASearch, "default method",
  [IsPongo, IsPosInt, IsList, IsList],
  function( pongo, circle, necklaces, hetypes )
    local s;
    s := rec( pongo := pongo, circle := circle, necklaces := necklaces,
              hetypes := hetypes, isLEAsearch := true );
    CreateHalfEdgeTypeIndex(s);
    return s;
  end);

ReadLEAInput := function(filename)
  local Get,M,acc,arr,circle,het,hets,i,j,n,neckl,nrnodes,pongo,pos,r,res,s,st;
  s := SplitString(StringFile(filename),""," \n\r\t");
  for i in [1..Length(s)] do
    st := s[i];
    if (st[1] >= '0' and st[1] <= '9') or st[1] = '-' then
      s[i] := Int(st);
    fi;
  od;
  pos := 1;
  Get := function() 
           pos := pos + 1; 
           if pos >= Length(s)+2 then
             return fail;
           else
             return s[pos-1];
           fi;
         end;
  # First read circle and the pongo:
  circle := Get();
  n := Get();
  acc := Get();
  M := EmptyPlist(n);
  for i in [1..n] do
    r := EmptyPlist(n);
    for j in [1..n] do
      Add(r,Get());
    od;
    Add(M,r);
  od;
  pongo := CayleyPongo(M,acc);

  # Now read the necklace types:
  n := Get();
  neckl := EmptyPlist(n);
  for i in [1..n] do
    Add(neckl,Necklace(i,Get(),Get(),Get()));
  od;

  # Now read the half edge types:
  n := Get();
  hets := EmptyPlist(n);
  for i in [1..n] do
    Add(hets,HalfEdgeType(Get(),Get(),Get(),Get(),Get(),Get()));
  od;

  res := LEASearch(pongo,circle,neckl,hets);
  res.filename := filename;

  # The following encodes which edges can precede a given edge round
  # a vertix (F^1E), we might need this later...
  nrnodes := Length(res.hetypes);
  res.nrnodes := nrnodes;
  res.arrows := EmptyPlist(nrnodes);
  res.curv   := List(res.hetypes,x->x.depot);
  for i in [1..nrnodes] do;
      het := res.hetypes[i];
      arr := List(res.indexr[het.necklace][het.start+1],
                  x->res.hetypes[x].complement);
      Add(res.arrows,arr);
  od;
  return res;
end;

MakeRandomPresentation := function(len, nrrels,out)
  # This function makes a truly random presentation of nrrels relators
  # of length len (syllables). This will be a modular group quotient:
  # <S,R,T|T^2=1=S^3=SR>
  # and relators will be STRTSTRT... where each S or R can be either S or R.
  # The inverse relators are given explicitly.
  # The result is written to the file out (IO_File) as presneck input.
  local b,bb,f,i,r,rels,st,bytes;
  Print("Using /dev/random, if this is stuck, type something!\n");
  f := IO_open("/dev/random",IO.O_RDONLY,0);
  rels := [];
  for i in [1..nrrels] do
      st := "";
      bytes := 0;
      while bytes < len do
          bytes := bytes + IO_read(f,st,bytes,len-bytes);
      od;
      b := List(st,x->IntChar(x) >= 128);
      AddSet(rels,b);
      bb := List(Reversed(b),x->not x);
      AddSet(rels,bb);
  od;
  IO_close(f);

  # Now write the result out:
  IO_Write(out,"3\n1\n1 2 3\n2 3 1\n3 1 2\n\n1\n1\n\n");
  IO_Write(out,Length(rels),"\n\n");
  for r in rels do
      IO_Write(out,len," 1\n");  # we just assume it is primitive
      for i in [1..len] do
          if r[i] then IO_Write(out,"2 "); else IO_Write(out,"3 "); fi;
      od;
      IO_Write(out,"\n");
      for i in [1..len] do
          IO_Write(out,"1 ");
      od;
      IO_Write(out,"\n\n");
  od;
end;

PreparePathClassification := function(r,Amax,Slack)
  # This sets up the S function, the M table and the result table P
  # It also computes P[1] and M[1]
  local A,B,arr,c,cur,i,lim,tup;
  r.Amax := Amax;
  r.Slack := Slack;
  r.SExc := [];
  r.S := function(N)
    if IsBound(r.SExc[N]) then return r.SExc[N];
    else return N*r.Amax + Slack; fi;
  end;
  r.M := [];
  r.P := [,rec(Aind := [], Bind := [])];
  # Now fill in r.P[2] by looking at the arrows:
  for A in [1..r.nrnodes] do
      arr := r.arrows[A];
      lim := r.S(1);
      for i in [1..Length(arr)] do
          B := arr[i];
          c := r.curv[A] + r.curv[B]; 
          if c > lim then
              tup := [A,B,c];
              if IsBound(r.P[1].Aind[A]) then
                  Add(r.P[1].Aind[A],tup);
              else
                  r.P[1].Aind[A] := [tup];
              fi;
              if IsBound(r.P[1].Bind[B]) then
                  Add(r.P[1].Bind[B],tup);
              else
                  r.P[1].Bind[B] := [tup];
              fi;
          fi;
      od;
  od;
  for i in [1..Length(r.P[1].Aind)] do
      if IsBound(r.P[1].Aind[i]) then
          Sort(r.P[1].Aind[i],function(x,y) return x[2] < y[2]; end);
      fi;
  od;
  for i in [1..Length(r.P[1].Bind)] do
      if IsBound(r.P[1].Bind[i]) then
          Sort(r.P[1].Bind[i],function(x,y) return x[1] < y[1]; end);
      fi;
  od;
end;

InstallMethod(\+,[IsInt,IsNegInfinity],function(a,b) return -infinity; end);
InstallMethod(\+,[IsNegInfinity,IsInt],function(a,b) return -infinity; end);
InstallMethod(\+,[IsNegInfinity,IsNegInfinity],
              function(a,b) return -infinity; end);
InstallMethod(\/,[IsNegInfinity,IsInt],function(a,b) return -infinity; end);

TropicalPongoZero := function(p)
  # Returns the zero element of the tropical pongo algebra of p
  return ListWithIdenticalEntries(Size(p),-infinity);
end;

ComputeC1 := function(r)
  # First setup a bijection between (necklaceID,start) <-> matrix index:
  local M,het1,het2,i,j,ntnr1,ntnr2,p;
  r.notchtypes := [];
  r.ntnumber := List([1..Length(r.necklaces)],x->[]);
  for i in [1..Length(r.necklaces)] do
      for j in [0..r.necklaces[i].primlen-1] do
          Add(r.notchtypes,[i,j]);
          r.ntnumber[i][j+1] := Length(r.notchtypes);
      od;
  od;
  r.nrnts := Length(r.notchtypes);
  M := List([1..r.nrnts],x->List([1..r.nrnts], y->TropicalPongoZero(r.pongo)));
  r.C := [M];
  for i in [1..Length(r.hetypes)] do
      het1 := r.hetypes[i];
      ntnr1 := r.ntnumber[het1.necklace]
           [(het1.start+het1.len) mod r.necklaces[het1.necklace].primlen +1];
      het2 := r.hetypes[het1.complement];
      ntnr2 := r.ntnumber[het2.necklace][het2.start+1];
      p := het2.pongoelm;
      M[ntnr1][ntnr2][p] := Maximum(M[ntnr1][ntnr2][p],het1.depot);
  od;
end;


TropicalMatMul := function(M1,M2)
  local c,cols,d,i,r,res,row,rows,x;
  rows := Length(M1);
  cols := Length(M2[1]);
  d := Length(M2);
  res := EmptyPlist(rows);
  for r in [1..rows] do
      row := EmptyPlist(cols);
      for c in [1..cols] do
          x := -infinity;
          for i in [1..d] do
              x := Maximum(x,M1[r][i] + M2[i][c]);
          od;
          Add(row,x);
      od;
      Add(res,row);
  od;
  return res;
end;

TropicalPongoAdd := function(p,x,y)
  # p a finite pongo, x and y vectors of tropical integers representing
  # elements of the tropical pongo algebra of p over the integers
  # This computes the sum of x and y.
  local i,res,s;
  s := Size(p);
  res := EmptyPlist(s);
  for i in [1..s] do
      Add(res,Maximum(x[i],y[i]));
  od;
  return res;
end;

TropicalPongoMul := function(p,x,y)
  # p a finite pongo, x and y vectors of tropical integers representing
  # elements of the tropical pongo algebra of p over the integers
  # This computes the product of x and y.
  local i,j,k,res,s;
  s := Size(p);
  res := ListWithIdenticalEntries(s,-infinity);
  for i in [1..s] do
    if x[i] <> -infinity then
      for j in [1..s] do
        if y[j] <> -infinity then
          k := PongoMult(p,i,j);
          if not(IsZero(p,k)) then
            res[k] := Maximum(res[k],x[i]+y[j]);
          fi;
        fi;
      od;
    fi;
  od;
  return res;
end;

  
TropicalPongoMatMul := function(p,M1,M2)
  local c,cols,d,i,r,res,row,rows,x;
  rows := Length(M1);
  cols := Length(M2[1]);
  d := Length(M2);
  res := EmptyPlist(rows);
  for r in [1..rows] do
      row := EmptyPlist(cols);
      for c in [1..cols] do
          x := TropicalPongoZero(p);
          for i in [1..d] do
              x := TropicalPongoAdd(p,x,
                            TropicalPongoMul(p,M1[r][i],M2[i][c]));
          od;
          Add(row,x);
      od;
      Add(res,row);
  od;
  return res;
end;

ComputeSomeCs := function(r,some)
  local i;
  if IsOddInt(some) then some := some + 1; fi;
  for i in [2..some] do
      r.C[i] := TropicalPongoMatMul(r.pongo,r.C[i-1],r.C[1]);
  od;
end;

ComputeAmax := function(r)
  local Amax,C,i,j,k,p,s;
  s := Size(r.pongo);
  Amax := -infinity;
  for k in [Length(r.C)/2..Length(r.C)] do
      C := r.C[k];
      for i in [1..Length(C)] do
          for j in [1..Length(C)] do
              for p in [1..s] do
                  Amax := Maximum(C[i][j][p]/k,Amax);
              od;
          od;
      od;
  od;
  r.Amax := Amax;
end;

ComputeCorners := function(r)
  local N,X,Y,curv,endpos,het1,het1c,het2,het2c,i,j,k,l,neck,neck2c,nt1,nt2,p;
  r.corners := [];
  N := Length(r.C);
  for i in [1..Length(r.hetypes)] do
      if i mod 1000 = 0 then 
          Print("Have done ",i," out of ",Length(r.hetypes),"\n");
      fi;
      het1 := r.hetypes[i];
      neck := r.necklaces[het1.necklace];
      endpos := (het1.start + het1.len) mod neck.primlen;
      l := [];
      for j in r.index[neck.id][endpos+1] do
          het2 := r.hetypes[j];
          # Now compute the maximal vertex contribution from this corner:
          X := het1.depot;
          Y := het2.depot;
          curv := -infinity;
          for k in [1..N] do
              het1c := r.hetypes[het1.complement];
              nt1 := r.ntnumber[het1c.necklace][het1c.start+1];
              het2c := r.hetypes[het2.complement];
              neck2c := r.necklaces[het2c.necklace];
              nt2 := r.ntnumber[het2c.necklace]
                      [(het2c.start+het2c.len) mod neck2c.primlen + 1];
              for p in PongoInverses(r.pongo,
                          PongoMult(r.pongo,het2.pongoelm,het1c.pongoelm)) do
                  curv := Maximum(curv,(X+Y+r.circle+r.C[k][nt1][nt2][p])/(k+2));
              od;
          od;
          if X+Y+r.circle < 2 * r.Amax then
              curv := Maximum(curv,r.Amax);
          else
              curv := Maximum(curv,(X+Y+r.circle+(N+1)*r.Amax)/(N+3));
          fi;
          Add(l,[curv,j]);
      od;
      Sort(l,function(a,b) return b[1] < a[1]; end);
      r.corners[i] := l;
  od;
end;

SunFlower := function(r,flowerlimit,timeout)
  local Y,c,corn,d,e,ee,f,flow,het1,i,j,k,len,n,neck,nn,s,starttime,t;
  starttime := Runtime();
  r.sunflowers := [];
  for i in [1..Length(r.hetypes)] do
      # This investigates whether there is a goes up and stays up sunflower
      # starting with this directed edge.
      het1 := r.hetypes[i];
      neck := r.necklaces[het1.necklace];
      len := neck.primlen * neck.power;
      Y := [[ [i,0,fail] ]];
      for n in [0..len-1] do
          if IsBound(Y[n+1]) then
              for j in [1..Length(Y[n+1])] do
                  t := Y[n+1][j];
                  # Now try to follows this with one more edge:
                  e := t[1];
                  c := t[2];
                  for k in [1..Length(r.corners[e])] do
                      corn := r.corners[e][k];
                      d := c + corn[1];
                      if d < 0 then break; fi;
                      ee := corn[2];
                      nn := n + r.hetypes[e].len;
                      if nn >= len then
                          if nn > len then continue; fi;
                          if ee <> i then continue; fi;
                          # Hurray! We found a sunflower
                          flow := rec( curv := d, edges := []);
                          s := t;
                          while s <> fail do
                              Add(flow.edges,s[1],1);
                              s := s[3];
                          od;
                          Add(r.sunflowers,flow);
                          Info(InfoLEA,1,"Found sunflower, curvature ",d);
                          if Runtime()-starttime > timeout or 
                             Length(r.sunflowers) > flowerlimit then
                              Info(InfoLEA,1,"Giving up, have ",
                                   Length(r.sunflowers)," sunflowers.");
                              return;
                          fi;
                      fi;
                      # Now need to add [ee,d] in Y[nn+1]:
                      if not(IsBound(Y[nn+1])) then
                          Y[nn+1] := [];
                      fi;
                      f := First([1..Length(Y[nn+1])],l->Y[nn+1][l][1]=ee);
                      if f = fail then
                          Add(Y[nn+1],[ee,d,t]);
                      else
                          if d > Y[nn+1][f][2] then
                              Y[nn+1][f][2] := d;
                              Y[nn+1][f][3] := t;
                          fi;
                      fi;
                  od;
              od;
          fi;
      od;
  od;
  if Length(r.sunflowers) = 0 then
      Info(InfoLEA,1,"Completed sunflower successfully, none found.");
  else
      Info(InfoLEA,1,"Completed sunflower, found ",Length(r.sunflowers),
           " sunflowers.");
  fi;
end;

MakeModGrpExample := function(len,name)
  local f;
  f := IO_File(Concatenation(name,".prs"),"w");
  MakeRandomPresentation(len,1,f);
  IO_Close(f);
  Exec(Concatenation("presneck ",name,".prs ",name,".nck"));
  Print("Made ",name,".prs\n");
end;

DoAll := function(name,flowerlimit,timeout)
  local r,t;
  Info(InfoLEA,1,"Reading input...");
  r := ReadLEAInput(name);
  Info(InfoLEA,1,"Computing C1...");
  ComputeC1(r);
  Info(InfoLEA,1,"Computing up to 6th power of C1...");
  ComputeSomeCs(r,6);
  Info(InfoLEA,1,"Computing Amax...");
  ComputeAmax(r);
  Info(InfoLEA,1,"Computing corners...");
  t := Runtime();
  ComputeCorners(r);
  Info(InfoLEA,1,"Computed corners in ",Runtime()-t," milliseconds.");
  Info(InfoLEA,1,"Running sunflower...");
  t := Runtime();
  SunFlower(r,flowerlimit,timeout);
  Info(InfoLEA,1,"Needed ",Runtime()-t," milliseconds for sunflower.");
  PrintTo(Concatenation(name,".result"),
          "# Flowerlimit was: ",flowerlimit,"\n",
          "# Timeout was: ",timeout,"\n",
          "# Found ",Length(r.sunflowers),
          " sunflowers, here they are:\n",
          "sunflowers := ",r.sunflowers,";\n");
  return r;
end;

InstallMethod( ViewObj, "for a LEAsearch object",
  [ IsRecord ],
  function(r)
    if IsBound(r.isLEAsearch) and r.isLEAsearch = true then
      Print("<a LEA search object");
      if IsBound(r.C) then Print(", C"); fi;
      if IsBound(r.Amax) then Print(", Amax"); fi;
      if IsBound(r.corners) then Print(", corners"); fi;
      if IsBound(r.sunflowers) then 
        Print(", ",Length(r.sunflowers)," sunflowers found");
      fi;
      Print(">");
    else
      TryNextMethod();
    fi;
  end );

TrySeveral := function(n,len,flowerlimit,timeout)
  local r,i,sunflowers;
  sunflowers := [];
  for i in [1..n] do
    MakeModGrpExample(len,"_try_");
    r := DoAll("_try_.nck",flowerlimit,timeout);
    Add(sunflowers,r.sunflowers);
  od;
  Print("Sunflowers Lengths = ", List(sunflowers,Length));
end;

 
