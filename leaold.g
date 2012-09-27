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
  function( p ) return [1..p![2]]; end );

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
              hetypes := hetypes );
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

  # Now make the graph with its nodes and arrows:
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
  local b,bb,f,i,r,rels,st;
  Print("Using /dev/random, if this is stuck, type something!\n");
  f := IO_open("/dev/random",IO.O_RDONLY,0);
  rels := [];
  for i in [1..nrrels] do
      st := "";
      IO_read(f,st,0,len);
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
  local A,B,arr,cur,i,lim,tup;
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
