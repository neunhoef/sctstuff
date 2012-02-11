# This input runs the pubcrawl "EF":
LogTo("crawlEF.log");
Read("pubcrawl.g");
s := ReadCrawlInput("haskell/park/kkk","EF");
l0 := DoCrawlLayer0(s);
for p in l0 do 
  Print(p.crawl, " starting at ", p.start,"\n");
  ViewObj(p.pct); Print("\n\n"); 
od;
l := DoCrawl(s,l0);
Length(l.descendants); Length(l.failures);
for p in l.descendants do 
  Print(p.crawl, " starting at ", p.start,"\n");
  ViewObj(p.pct); Print("\n\n"); 
od;
ll := DoCrawl(s,l.descendants);;
Length(ll.descendants); Length(ll.failures);
for p in ll.descendants do 
  Print(p.crawl, " starting at ", p.start,"\n");
  ViewObj(p.pct); Print("\n\n"); 
od;
ll := DoCrawl(s,ll.descendants);;
Length(ll.descendants); Length(ll.failures);
for p in ll.failures do 
  Print(p.crawl, " starting at ", p.start,"\n");
  ViewObj(p.pct); Print("\n\n"); 
od;
LogTo();

