gap> infra;
<infrastructure alph=RST ialph=SRT
 "RR"->"S" "RS"->"" "SR"->"" "SS"->"R" "TT"->"" weights=[ 17, 18, 17 ]>
gap> r := DehnRewrites(infra,[Rep("TS",11),Rep("TSTSTR",6)]);
Error, two reductions compare equal called from
ResolveEquation(  ); called from
<function "unknown">( <arguments> )
 called from read-eval loop at line 48 of *stdin*
you can 'quit;' to quit to outer loop, or
you can 'return;' to continue
brk> eq;
[ "STRTSTRTRTSTRTRTSTS", "RTRTSTSTRTSTSTRTSTR" ]
brk> Length(eq[1]);
19
brk> List([1..18],i->eq[1]{[i,i+1]});
[ "ST", "TR", "RT", "TS", "ST", "TR", "RT", "TR", "RT", "TS", "ST", "TR", 
  "RT", "TR", "RT", "TS", "ST", "TS" ]
brk> Collected(last);
[ [ "RT", 5 ], [ "ST", 4 ], [ "TR", 5 ], [ "TS", 4 ] ]
brk> List([1..18],i->eq[2]{[i,i+1]});
[ "RT", "TR", "RT", "TS", "ST", "TS", "ST", "TR", "RT", "TS", "ST", "TS", 
  "ST", "TR", "RT", "TS", "ST", "TR" ]
brk> Collected(last);
[ [ "RT", 4 ], [ "ST", 5 ], [ "TR", 4 ], [ "TS", 5 ] ]
brk> gap> LogTo();
