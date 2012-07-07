w := [1,2,3];
c := CyclicWord(w);
c2 := CyclicWord("abcdef");
w2 := "STRTSTSSTT";
r := ["SS","R","RR","S","RS","","SR","","TT","",
      "STSTSTST","TRTRTR","TSTSTSTS","RTRTRT",
      "RTRTRTRT","TSTSTS","TRTRTRTR","STSTST"];
rws := RewriteSystem("RST",r);
w := "STRTST";; ShowRewrite(rws,w,FindOneRewrite(rws,w));
w := "STTRTST";; ShowRewrite(rws,w,FindOneRewrite(rws,w));
w := "SRTTRTST";; ShowRewrite(rws,w,FindOneRewrite(rws,w));
w := "TSTSTSTSTRTTRTST";; ShowRewrite(rws,w,FindOneRewrite(rws,w));
w := "STSTSTSTRTTRTST";; ShowRewrite(rws,w,FindOneRewrite(rws,w));
w := "STRTSTRTSTSTSTSTRTTRTST";; ShowRewrite(rws,w,FindOneRewrite(rws,w));
rww := FindAllRewrites(rws,w);; for rw in rww do ShowRewrite(rws,w,rw); od;
cw := CyclicWord("STRTST");; ShowRewrite(rws,cw,FindOneRewrite(rws,cw));
cw := CyclicWord("STTRTST");; ShowRewrite(rws,cw,FindOneRewrite(rws,cw));
cw := CyclicWord("SRTTRTST");; ShowRewrite(rws,cw,FindOneRewrite(rws,cw));
cw := CyclicWord("TSTSTSTSTRTTRTST");; 
ShowRewrite(rws,cw,FindOneRewrite(rws,cw));
cw := CyclicWord("STSTSTSTRTTRTST");; 
ShowRewrite(rws,cw,FindOneRewrite(rws,cw));
cw := CyclicWord("STRTSTRTSTSTSTSTRTTRTST");; 
ShowRewrite(rws,cw,FindOneRewrite(rws,cw));
rww := FindAllRewrites(rws,cw);; for rw in rww do ShowRewrite(rws,cw,rw); od;
cw := CyclicWord("STRTSTRTSTSTSTSTRTTRTSTS");; 
rww := FindAllRewrites(rws,cw);; for rw in rww do ShowRewrite(rws,cw,rw); od;
cw := CyclicWord("RRTRTS");
rww := FindAllRewrites(rws,cw);; for rw in rww do ShowRewrite(rws,cw,rw); od;

