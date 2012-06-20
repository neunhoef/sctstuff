gap> FindOneRewrite(rws,"STRTST");
fail
gap> FindOneRewrite(rws,"STTRTST");
[ 5, 2 ]
gap> rws!.lefts[last[1]] = "TT";
true
gap> FindOneRewrite(rws,"SRTTRTST");
[ 4, 1 ]
gap> rws!.lefts[last[1]] = "SR";
true
gap> FindOneRewrite(rws,"TSTSTSTSTRTTRTST");
[ 7, 1 ]
gap> rws!.lefts[last[1]] = "TSTSTSTS";
true
gap> FindOneRewrite(rws,"STSTSTSTRTTRTST");
[ 6, 1 ]
gap> rws!.lefts[last[1]] = "STSTSTST";
true
gap> FindOneRewrite(rws,"STRTSTRTSTSTSTSTRTTRTST");
[ 7, 8 ]
gap> rws!.lefts[last[1]] = "TSTSTSTS";
true
