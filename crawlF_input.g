# This input runs the pubcrawl "F":
LogTo("crawlF.log");
Read("pubcrawl.g");
s := ReadCrawlInput("haskell/park/kkk","F");
l0 := DoCrawlLayer0(s);
for p in l0 do ViewObj(p.pct); Print("\n\n"); od;
l := DoCrawl(s,l0);
Length(l.descendants); Length(l.failures);
for p in l.descendants do ViewObj(p.pct); Print("\n\n"); od;
ll := DoCrawl(s,l.descendants);;
Length(ll.descendants); Length(ll.failures);
for p in ll.descendants do ViewObj(p.pct); Print("\n\n"); od;
ll := DoCrawl(s,ll.descendants);;
Length(ll.descendants); Length(ll.failures);
for p in ll.descendants do ViewObj(p.pct); Print("\n\n"); od;
ll := DoCrawl(s,ll.descendants);;
Length(ll.descendants); Length(ll.failures);
for p in ll.failures do ViewObj(p.pct); Print("\n\n"); od;
LogTo();

