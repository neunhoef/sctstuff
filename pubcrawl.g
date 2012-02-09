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
NLId      := r -> r.id;
NLPrimLen := r -> r.primlen;
NLPower   := r -> r.power;
NLName    := r -> r.name;
IsNecklace := IsRecord;

# Half edge types:
HalfEdgeType := function(necklace, start, len, complement, depot, pongoelm)
  return rec(necklace := necklace, start := start, len := len, 
             complement := complement, depot := depot, pongoelm := pongoelm);
end;
HENecklace   := r -> r.necklace;
HEStart      := r -> r.start;
HELen        := r -> r.len;
HEComplement := r -> r.complement;
HEDepot      := r -> r.depot;
HEPongoElm   := r -> r.pongoelm;
IsHalfEdgeType := IsRecord;

# Rows of partical coset tables:
PCTRow := function(id,E,F,L,het)
  return rec( IdxI := id, IdxE := E, IdxF := F, IdxL := L, HEType := het );
end;
IdxI := r -> r.IdxI;
IdxE := r -> r.IdxE;
IdxF := r -> r.IdxF;
IdxL := r -> r.IdxL;
HEType := r -> r.HEType;
IsPCTRow := IsRecord;
IsPCT := IsList;

# a partial coset table is just a list of these where the IdxI entry is
# the position in the list. The HEType entry is a position in the list
# of half edge types.

# The following describes a pubcrawl search node:

CrawlNode := function(crawl, start, pct)
  return rec( crawl := crawl, start := start, pct := pct );
end;
Crawl := r -> r.crawl;
Start := r -> r.start;
PCT :=   r -> r.pct;
IsCrawlNode := IsRecord;

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
    return rec( pongo := pongo, circle := circle, necklaces := necklaces,
                hetypes := hetypes, crawl := crawl );
  end);
CrPongo     := r -> r.pongo;
CrCircle    := r -> r.circle;
CrNecklaces := r -> r.necklaces;
CrHETypes   := r -> r.hetypes;
CrCrawl     := r -> r.crawl;
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
    local a,b,het,hets,i,j,nodes;
    nodes := [];
    hets := CrHETypes(s);
    for i in [1..Length(hets)] do
        het := hets[i];
        if HEDepot(het) + CrCircle(s)/3 >= 0 then
            a := PCTRow(1,2,-1,-1,i);
            b := PCTRow(2,1,-1,-1,HEComplement(het));
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

InstallMethod( DoCrawl, "default method",
  [ IsCrawlSearch, IsCrawlNode, IsList, IsList ],
  function( s, node, descendants, failures )
    # Check (partial) F-cycles  --> could reject
    # Check (partial) V-cycles  --> could reject
    #   --> this gives lower bounds for the valencies
    # Trace pubcrawl, can do:
    #     die because of negativity
    #     find failure (if pubcrawl returns non-negatively)
    #     disjoin cases to make descendants
  end );

