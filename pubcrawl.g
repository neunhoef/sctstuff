DeclareOperation("PongoMult",[IsPongo,IsObject,IsObject]);
DeclareOperation("IsZero",[IsPongo,IsObject]);
DeclareOperation("IsAccepting",[IsPongo,IsObject]);
DeclareOperation("MakeCayleyPongo",[IsList]);
DeclareOperation("Elements",[IsPongo]);

# A necklace:
necklace := rec( id := 1, primlen := 1, power := 7 );

# A half-edge-type:
het := rec( necklace := 1,   # a necklace ID
            start := 0,      # is mod primlen
            len := 10,       # is < primlen*power
            depot := -100,   # depot value
          );

# a Pub-Crawl:
crawl := "FEF";    # we drink before each letter

# a partial coset table row:
pctrow := rec( imgI := 1,    # our own ID
               imgE := 2,    # the other halfedge
               imgF := -1,   # the F-image
               imgL := -1,   # the L-image (L = F^-1)
               het := 1,     # ID of the half-edge type
             );

pct := [pctrows];

# a search node:
node := rec( crawl := "FEF", crawlstart := 1, pct := [pctrows] );

# a search object:
search := rec( pongo := p, circle := 5460, necklaces := [], 
               halfedgetypes := [], pubcrawl := "FEF" );

DeclareOperation("ShowPCT", [IsList]);

DeclareOperation("CrawlSearch",
  [IsPongo,           # a pongo
   IsPosInt,          # circle
   IsList,            # list of necklaces
   IsList,            # list of half-edge-types
   IsStringRep,       # the pubcrawl string
  ]);

DeclareOperation("CrawlLayer0", [IsCrawlSearch]);

DeclareOperation("Crawl",[IsCrawlSearch, IsRecord]);
  # --> list of nodes, the descendants of one node

DeclareOperation("Crawl",[IsCrawlSearch, IsList]);
  # --> list of nodes, the descendants of all nodes

