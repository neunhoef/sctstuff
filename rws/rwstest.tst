gap> w := [1,2,3];
[ 1, 2, 3 ]
gap> c := CyclicWord(w);
CyclicWord([ 1, 2, 3 ])
gap> c2 := CyclicWord("abcdef");
CyclicWord("abcdef")
gap> w2 := "STRTSTSSTT";
"STRTSTSSTT"
gap> r := ["SS","R","RR","S","RS","","SR","","TT","",
>       "STSTSTST","TRTRTR","TSTSTSTS","RTRTRT",
>       "RTRTRTRT","TSTSTS","TRTRTRTR","STSTST"];
[ "SS", "R", "RR", "S", "RS", "", "SR", "", "TT", "", "STSTSTST", "TRTRTR", 
  "TSTSTSTS", "RTRTRT", "RTRTRTRT", "TSTSTS", "TRTRTRTR", "STSTST" ]
gap> rws := RewriteSystem("RST",r);
<rewrite system on "RST" with 9 rewrites>
gap> w := "STRTST";; ShowRewrite(rws,w,FindOneRewrite(rws,w));
Word: STRTST
   => No rewrite applies.
gap> w := "STTRTST";; ShowRewrite(rws,w,FindOneRewrite(rws,w));
Word: STTRTST
       TT -> 
   => SRTST
gap> w := "SRTTRTST";; ShowRewrite(rws,w,FindOneRewrite(rws,w));
Word: SRTTRTST
      SR -> 
   => TTRTST
gap> w := "TSTSTSTSTRTTRTST";; ShowRewrite(rws,w,FindOneRewrite(rws,w));
Word: TSTSTSTSTRTTRTST
      TSTSTSTS -> RTRTRT
   => RTRTRTTRTTRTST
gap> w := "STSTSTSTRTTRTST";; ShowRewrite(rws,w,FindOneRewrite(rws,w));
Word: STSTSTSTRTTRTST
      STSTSTST -> TRTRTR
   => TRTRTRRTTRTST
gap> w := "STRTSTRTSTSTSTSTRTTRTST";; ShowRewrite(rws,w,FindOneRewrite(rws,w));
Word: STRTSTRTSTSTSTSTRTTRTST
             TSTSTSTS -> RTRTRT
   => STRTSTRRTRTRTTRTTRTST
gap> rww := FindAllRewrites(rws,w);; for rw in rww do ShowRewrite(rws,w,rw); od;
Word: STRTSTRTSTSTSTSTRTTRTST
             TSTSTSTS -> RTRTRT
   => STRTSTRRTRTRTTRTTRTST
Word: STRTSTRTSTSTSTSTRTTRTST
              STSTSTST -> TRTRTR
   => STRTSTRTTRTRTRRTTRTST
Word: STRTSTRTSTSTSTSTRTTRTST
                       TT -> 
   => STRTSTRTSTSTSTSTRRTST
gap> cw := CyclicWord("STRTST");; ShowRewrite(rws,cw,FindOneRewrite(rws,cw));
CyclicWord("RTSTST")
   => No rewrite applies.
gap> cw := CyclicWord("STTRTST");; ShowRewrite(rws,cw,FindOneRewrite(rws,cw));
CyclicWord("RTSTSTT")
                 TT -> 
 => CyclicWord("RTSTS")
gap> cw := CyclicWord("SRTTRTST");; ShowRewrite(rws,cw,FindOneRewrite(rws,cw));
CyclicWord("RTSTSRTT")
                SR -> 
 => CyclicWord("RTSTTT")
gap> cw := CyclicWord("TSTSTSTSTRTTRTST");; 
gap> ShowRewrite(rws,cw,FindOneRewrite(rws,cw));
CyclicWord("RTSTTSTSTSTSTRTT")
               TT -> 
 => CyclicWord("RTSSTSTSTSTRTT")
gap> cw := CyclicWord("STSTSTSTRTTRTST");; 
gap> ShowRewrite(rws,cw,FindOneRewrite(rws,cw));
CyclicWord("RTSTSTSTSTSTRTT")
             TSTSTSTS -> RTRTRT
 => CyclicWord("RRTRTRTTSTRTT")
gap> cw := CyclicWord("STRTSTRTSTSTSTSTRTTRTST");; 
gap> ShowRewrite(rws,cw,FindOneRewrite(rws,cw));
CyclicWord("RTSTRTSTSTSTSTRTTRTSTST")
                 TSTSTSTS -> RTRTRT
 => CyclicWord("RRTRTRTTRTTRTSTSTRTST")
gap> rww := FindAllRewrites(rws,cw);; for rw in rww do ShowRewrite(rws,cw,rw); od;
CyclicWord("RTSTRTSTSTSTSTRTTRTSTST")
                 TSTSTSTS -> RTRTRT
 => CyclicWord("RRTRTRTTRTTRTSTSTRTST")
CyclicWord("RTSTRTSTSTSTSTRTTRTSTST")
                  STSTSTST -> TRTRTR
 => CyclicWord("RRTTRTSTSTRTSTRTTRTRT")
CyclicWord("RTSTRTSTSTSTSTRTTRTSTST")
                           TT -> 
 => CyclicWord("RRTSTSTRTSTRTSTSTSTST")
gap> cw := CyclicWord("STRTSTRTSTSTSTSTRTTRTSTS");;
gap> rww := FindAllRewrites(rws,cw);; for rw in rww do ShowRewrite(rws,cw,rw); od;
CyclicWord("RTSTRTSTSTSTSTRTTRTSTSST")
                 TSTSTSTS -> RTRTRT
 => CyclicWord("RRTRTRTTRTTRTSTSSTRTST")
CyclicWord("RTSTRTSTSTSTSTRTTRTSTSST")
                  STSTSTST -> TRTRTR
 => CyclicWord("RRTTRTSTSSTRTSTRTTRTRT")
CyclicWord("RTSTRTSTSTSTSTRTTRTSTSST")
                           TT -> 
 => CyclicWord("RRTSTSSTRTSTRTSTSTSTST")
CyclicWord("RTSTRTSTSTSTSTRTTRTSTSST")
                                 SS -> R
 => CyclicWord("RTRTSTRTSTSTSTSTRTTRTST")
gap> cw := CyclicWord("RRTRTS");
CyclicWord("RRTRTS")
gap> rww := FindAllRewrites(rws,cw);; for rw in rww do ShowRewrite(rws,cw,rw); od;
CyclicWord("RRTRTS")
            RR -> S
 => CyclicWord("RTSST")
CyclicWord("RRTRTS")
                 SR -> 
 => CyclicWord("RTRT")
