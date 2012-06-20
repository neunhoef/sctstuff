w := [1,2,3];
c := CyclicWord(w);
c2 := CyclicWord("abcdef");
w2 := "STRTSTSSTT";
r := ["SS","R","RR","S","RS","","SR","","TT","",
      "STSTSTST","TRTRTR","TSTSTSTS","RTRTRT",
      "RTRTRTRT","TSTSTS","TRTRTRTR","STSTST"];
rws := RewriteSystem("RST",r);

