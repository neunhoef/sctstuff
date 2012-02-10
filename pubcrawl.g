DeclareInfoClass("InfoCrawl");
SetInfoLevel(InfoCrawl,2);

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

# Rows of partical coset tables:
PCTRow := function(id,E,F,L,het)
  return rec( id := id, E := E, F := F, L := L, hetype := het );
end;
IsPCTRow := IsRecord;
IsPCT := IsList;

# a partial coset table is just a list of these where the id entry is
# the position in the list. The hetype entry is a position in the list
# of half edge types.

# The following describes a pubcrawl search node:

CrawlNode := function(crawl, start, pct)
  return rec( crawl := crawl, start := start, pct := pct );
end;
IsCrawlNode := IsRecord;

CreateHalfEdgeTypeIndex := function(s)
  local het,i,index,n;
  n := Length(s.necklaces);
  index := EmptyPlist(n);
  for i in [1..n] do
      index[i] := List([0..s.necklaces[i].primlen-1],j->[]);
  od;
  for i in [1..Length(s.hetypes)] do
      het := s.hetypes[i];
      Add(index[het.necklace][het.start+1],i);
  od;
  s.index := index;
end;

# The following describes a pubcrawl search:

DeclareOperation("CrawlSearch",
  [IsPongo,           # a pongo
   IsPosInt,          # circle
   IsList,            # list of necklaces
   IsList,            # list of half-edge-types
   IsStringRep,       # the pubcrawl string
  ]);
InstallMethod(CrawlSearch, "default method",
  [IsPongo, IsPosInt, IsList, IsList, IsStringRep ],
  function( pongo, circle, necklaces, hetypes, crawl )
    local s;
    s := rec( pongo := pongo, circle := circle, necklaces := necklaces,
              hetypes := hetypes, crawl := crawl );
    CreateHalfEdgeTypeIndex(s);
    return s;
  end);
IsCrawlSearch := IsRecord;


DeclareOperation("ShowPCT", [IsList]);

DeclareOperation("DoCrawlLayer0", [IsCrawlSearch]);

DeclareOperation("DoCrawl",[IsCrawlSearch, IsCrawlNode, IsList, IsList]);
  # --> the descendants of one node (the record) are added to the
  #     list in the 3rd argument, if the node is a completed pubcrawl
  #     it is added to the 4th argument. It returns either fail
  #     for a failure or the number of descendants.

DeclareOperation("DoCrawls",[IsCrawlSearch, IsList, IsList, IsList]);
  # --> run the above on multiple search nodes



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

ReadCrawlInput := function(filename,crawl)
  local Get,M,acc,circle,hets,i,j,n,neckl,pongo,pos,r,s,st;
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

  return CrawlSearch(pongo,circle,neckl,hets,crawl);
end;

InstallMethod( ShowPCT, "default method", [IsList], ViewObj );

InstallMethod( DoCrawlLayer0, "default method",
  [ IsCrawlSearch ],
  function( s )
    local a,b,het,i,j,nodes;
    nodes := [];
    for i in [1..Length(s.hetypes)] do
        het := s.hetypes[i];
        if het.depot + s.circle/3 >= 0 then
            a := PCTRow(1,2,-1,-1,i);
            b := PCTRow(2,1,-1,-1,het.complement);
            for j in [1..Length(s.crawl)] do
                Add(nodes,CrawlNode(s.crawl,j,[a,b]));
            od;
        fi;
    od;
    return nodes;
  end );

InstallMethod( DoCrawls, "default method",
  [ IsCrawlSearch, IsList, IsList, IsList ],
  function( s, nodes, descendants, failures )
    local n;
    for n in nodes do
      DoCrawl(s, n, descendants, failures);
    od;
  end );

# Here comes the real thing, compute the descendants of one node
# for the backtrack search:

CheckFCycles := function(s,node)
  # Returns fail if node is rejected due to F-cycles and true otherwise
  local cyclecomplete,heti,hetj,i,j,len,n,neckid,neckl,pct,visited;
  pct := node.pct;
  n := Length(pct);
  visited := BlistList([1..n],[]);
  for i in [1..n] do
      if not(visited[i]) then
          visited[i] := true;
          heti := s.hets[pct[i].het];
          len := heti.len;
          j := i;
          cyclecomplete := false;
          neckid := heti.necklace;
          neckl  := s.necklaces[neckid];
          while pct[j].F <> -1 do
              j := pct[j].F;
              visited[j] := true;
              hetj := s.hets[pct[j].het];
              Assert(1,neckid = hetj.necklace,Error("Bla 1"));
              Assert(1,(heti.start + heti.len) mod neckl.primlen =
                       hetj.start,Error("Bla 2"));
              len := len + hetj.len;
              if j = i then
                  cyclecomplete := true;
                  if len <> neckl.primlen * neckl.power then
                      Info(InfoCrawl,2,"REJECT: Complete F-cycle has wrong ",
                                       "total length");
                      return fail;
                  fi;
                  break;
              fi;
          od;
          if not(cyclecomplete) then
              # Now go in the L direction with the same check, we know
              # here that the F-cycle is incomplete!
              j := i;
              while pct[j].L <> -1 do
                  j := pct[j].L;
                  visited[j] := true;
                  hetj := s.hets[pct[j].het];
                  Assert(1,neckid = hetj.necklace,Error("Bla 3"));
                  Assert(1,heti.start =
                           (hetj.start + hetj.len) mod neckl.primlen,
                           Error("Bla 4"));
                  len := len + hetj.len;
              od;
              # Now check the total length:
              if len >= neckl.primlen * neckl.power then
                  Info(InfoCrawl,2,"REJECT: Partial F-cycle has overrun");
                  return fail;
              fi;
          fi;
      fi;
  od;
  return true;
end;

CheckVCycles := function(s,node)
  # Returns fail if node is rejected due to V-cycles and the valency
  # bound otherwise
  local cyclecomplete,heti,hetj,i,j,n,p,pct,val,valencybound,visited;
  pct := node.pct;
  n := Length(pct);
  visited := BlistList([1..n],[]);
  valencybound := EmptyPlist(n);
  for i in [1..n] do
      if not(visited[i]) then
          visited[i] := true;
          valencybound[i] := [fail];
          heti := s.hets[pct[i].het];
          p := heti.pongoelm;
          val := 1;
          j := i;
          cyclecomplete := false;
          # EFV=1 and FL=1=LF thus V=LE and V^-1=EF
          while pct[j].L <> -1 do
              j := pct[pct[j].L].E;
              visited[j] := true;
              valencybound[j] := valencybound[i];
              val := val + 1;
              hetj := s.hets[pct[j].het];
              p := PongoMult(s.pongo,p,hetj.pongoelm);
              if IsZero(s.pongo,p) then
                  Info(InfoCrawl,2,"REJECT: Pongo rejects vertex");
                  return fail;
              fi;
              if j = i then
                  cyclecomplete := true;
                  # Note that we have overcounted the valency by 1 here!
                  val := val - 1;
                  if val < 3 then
                      Info(InfoCrawl,2,"REJECT: complete vertex of valency ",
                                       val);
                      return fail;
                  fi;
                  valencybound[i][1] := val;  # this is exact
                  break;
              fi;
          od;
          if not(cyclecomplete) then
              # Now go in the V^-1 direction with the same check, we know
              # here that the V-cycle is incomplete!
              j := i;
              while pct[pct[j].E].F <> -1 do
                  j := pct[pct[j].E].F;
                  visited[j] := true;
                  valencybound[j] := valencybound[i];
                  val := val + 1;
                  hetj := s.hets[pct[j].het];
                  p := PongoMult(s.pongo,hetj.pongoelm,p);
                  if IsZero(s.pongo,p) then
                      Info(InfoCrawl,2,"REJECT: Pongo rejects vertex");
                      return fail;
                  fi;
              od;
              # Now set the valency bound:
              valencybound[i][1] := Maximum(val + 1,3);
              # because at least one more point is needed to close the
              # V-cycle
          fi;
      fi;
  od;
  return valencybound;
end;

ExtendCrawlByF := function(s,node,d,descendants,failures)
  local het,hetd,hetids,hetx,hetxid,hety,n,neckid,neckl,neckly,newpct,pct,
        pos,rowx,rowy,u,ulist,v,vlist,w,wlist;

  pct := node.pct;
  n := Length(pct);
  hetd := s.hetypes[pct[d].hetype];
  neckid := hetd.necklace;
  neckl := s.necklaces[neckid];
  pos := (hetd.start + hetd.len) mod neckl.primlen;
  # Look up all successor half edge types of hetd
  hetids := s.index[hetd.necklace][pos+1];
  for hetxid in hetids do
    hetx := s.hetypes[hetxid];
    hety := s.hetypes[hetx.complement];
    neckly := s.necklaces[hety.necklace];
    ulist := [0..n]; ulist[1] := -1;
    for u in ulist do
      if u <> d then     # this is because x=dF and u=xF, so u=d is a digon
        if u <> -1 then  # additional checks required here
          if pct[u].L <> -1 then continue; fi;
          het := s.hetypes[pct[u].hetype];
          if het.necklace <> neckid or 
             het.start <> (hetx.start+hetx.len) mod neckl.primlen  then
              continue;
          fi;
        fi;
        wlist := [0..n]; wlist[1] := -1;
        for w in wlist do
          if w <> -1 then    # additional checks required here
            if w = u or      # w and u are F-images of x and y, so different
               pct[w].L <> -1 then continue; fi;
            het := s.hetypes[pct[w].hetype];
            if het.necklace <> hety.necklace or
               het.start <> (hety.start+hety.len) mod neckly.primlen then
                continue;
            fi;
          fi;
          vlist := [0..n]; vlist[1] := -1;
          for v in vlist do
            if v <> -1 then
              if pct[v].F <> -1 then continue; fi;
              het := s.hetypes[pct[v].hetype];
              if het.necklace <> hety.necklace or
                 hety.start <> (het.start+het.len) mod neckly.primlen then
                  continue;
              fi;
            fi;
            rowx := PCTRow(n+1,n+2,u,n,hetxid);
            rowy := PCTRow(n+2,n+1,w,v,hety.id);
            newpct := EmptyPlist(n+2);
            Append(newpct,pct);
            Add(newpct,rowx);
            Add(newpct,rowy);
            if u <> -1 then
              newpct[u] := ShallowCopy(newpct[u]);
              newpct[u].L := n+1;   # which is x
            fi;
            if w <> -1 then
              newpct[w] := ShallowCopy(newpct[w]);
              newpct[w].L := n+2;   # which is y
            fi;
            if v <> -1 then
              newpct[v] := ShallowCopy(newpct[v]);
              newpct[v].F := n+2;   # which is y
            fi;
            Add(descendants, newpct);
          od;
        od;
      fi;
    od;
  od;      
end;

ExtendCrawlByL := function(s,node,d,descendants,failures)
  local het,hetd,hetids,hetx,hetxid,hety,n,neckid,neckl,neckly,newpct,
        pct,rowx,rowy,u,ulist,v,vlist,w,wlist;

  pct := node.pct;
  n := Length(pct);
  hetd := s.hetypes[pct[d].hetype];
  neckid := hetd.necklace;
  neckl := s.necklaces[neckid];
  # Look up all predecessor half edge types of hetd
  hetids := s.indexr[hetd.necklace][hetd.start+1];
  for hetxid in hetids do
    hetx := s.hetypes[hetxid];
    hety := s.hetypes[hetx.complement];
    neckly := s.necklaces[hety.necklace];
    ulist := [0..n]; ulist[1] := -1;
    for u in ulist do
      if u <> d then     # this is because x=dL and u=xL, so u=d is a digon
        if u <> -1 then  # additional checks required here
          if pct[u].F <> -1 then continue; fi;
          het := s.hetypes[pct[u].hetype];
          if het.necklace <> neckid or 
             (het.start+het.len) mod neckl.primlen <> hetx.start then
              continue;
          fi;
        fi;
        wlist := [0..n]; wlist[1] := -1;
        for w in wlist do
          if w <> -1 then    # additional checks required here
            if pct[w].L <> -1 then continue; fi;
            het := s.hetypes[pct[w].hetype];
            if het.necklace <> hety.necklace or
               het.start <> (hety.start+hety.len) mod neckly.primlen then
                continue;
            fi;
          fi;
          vlist := [0..n]; vlist[1] := -1;
          for v in vlist do
            if v <> -1 then
              if v = u or      # v and u are L-images of x and y, so different
                 pct[v].F <> -1 then continue; fi;
              het := s.hetypes[pct[v].hetype];
              if het.necklace <> hety.necklace or
                 hety.start <> (het.start+het.len) mod neckly.primlen then
                  continue;
              fi;
            fi;
            rowx := PCTRow(n+1,n+2,n,u,hetxid);
            rowy := PCTRow(n+2,n+1,w,v,hety.id);
            newpct := EmptyPlist(n+2);
            Append(newpct,pct);
            Add(newpct,rowx);
            Add(newpct,rowy);
            if u <> -1 then
              newpct[u] := ShallowCopy(newpct[u]);
              newpct[u].F := n+1;   # which is x
            fi;
            if w <> -1 then
              newpct[w] := ShallowCopy(newpct[w]);
              newpct[w].L := n+2;   # which is y
            fi;
            if v <> -1 then
              newpct[v] := ShallowCopy(newpct[v]);
              newpct[v].F := n+2;   # which is y
            fi;
            Add(descendants, newpct);
          od;
        od;
      fi;
    od;
  od;      
end;

InstallMethod( DoCrawl, "default method",
  [ IsCrawlSearch, IsCrawlNode, IsList, IsList ],
  function( s, node, descendants, failures )
    local crawl,curv,d,hetd,pct,pos,valencybound;

    # Check (partial) F-cycles  --> could reject
    if CheckFCycles(s,node) then return 0; fi;

    # Check (partial) V-cycles  --> could reject
    #   --> this gives lower bounds for the valencies
    valencybound := CheckVCycles(s,node);
    if valencybound = fail then return 0; fi;

    # Trace pubcrawl, can do:
    #     die because of negativity
    #     find failure (if pubcrawl returns non-negatively)
    #     disjoin cases to make descendants
    d := 1;               # Starting point of the pubcrawl
    crawl := node.crawl;
    pos := node.start;    # this is the position in the pubcrawl string
    pct := node.pct;
    curv := 0;            # here we collect the curvature that has been drunken
    while true do   # is left by return statement in all cases
        hetd := s.hets[pct[d].het];
        curv := curv + hetd.depot + s.circle / valencybound[d][1];
        if curv < 0 then
            Info(InfoCrawl,2,"REJECT: boozer dies");
            return 0;
        fi;
        if crawl[pos] = 'E' then
            d := pct[d].E;   # always defined
        elif crawl[pos] = 'F' then
            if pct[d].F <> -1 then
                d := pct[d].F;
            else
                return ExtendCrawlByF(s,node,d,descendants,failures);
            fi;
        elif crawl[pos] = 'L' then
            if pct[d].L <> -1 then
                d := pct[d].L;
            else
                return ExtendCrawlByL(s,node,d,descendants,failures);
            fi;
        fi;
        pos := pos + 1;
        if pos > Length(crawl) then pos := 1; fi;
        if d = 1 and pos = node.start then
            # boozer returned and still lives!
            Info(InfoCrawl,2,"FAILURE: boozer returned");
            Add(failures,node);
            return fail;
        fi;
    od;
  end );

