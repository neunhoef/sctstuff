##
##  Stuff to check epsilon-confluence of rewrite-systems
##  Copyright (C) 2012 by Max Neunhoeffer
##  This file is free software, see license information at the end.
##

LoadPackage("orb");

# Words and cyclic words.

# Words are just lists, either plain lists or strings
# So letters are either integers or characters

# Some utilities:

DebugRunning := false;

InstallGlobalFunction( Debug,
  function(arg)
    local c,kb;
    if DebugRunning then return; fi;
    for c in arg do ViewObj(c); od; 
    Print("\nDebug:\c");
    kb := InputTextUser();
    c := CharInt(ReadByte(kb));
    Print(c,"\n");
    if c = 'q' then Error(); fi;
    if c = 'r' then DebugRunning := true; fi;
  end);

InstallMethod(EmptyList, "for an integer and a string",
  [ IsInt, IsString and IsStringRep ],
  function(len, l) return EmptyString(len); end );

InstallMethod(EmptyList, "for an integer and a plist",
  [ IsInt, IsList and IsPlistRep ],
  function(len, l) return EmptyPlist(len); end );

InstallMethod( LexLeastRotation, "for a list",
  [ IsList ],
  function( l )
    local a,i,j,k,n,nn;
    if IsEmpty(l) then return [ShallowCopy(l),1]; fi;
    n := Length(l);
    a := EmptyList(2*n,l);
    Append(a,l);
    Append(a,l);
    k := 0;
    nn := 2*n;
    while k < nn do
        i := k+1;
        j := k+2;
        while true do
            if j-1-k = n and n mod (j-i) = 0 then
                return [a{[k+1..k+j-i]},n/(j-i)];
            fi;
            if j <= nn then
                if a[i] < a[j] then
                    i := k+1; j := j+1; continue;
                elif a[i] = a[j] then
                    i := i+1; j := j+1; continue;
                fi;
            fi;
            repeat
                k := k + (j-i);
            until k >= i;
            break;
        od;
    od;
    return fail;
  end );

InstallGlobalFunction( HashFunctionForStrings,
function(v,data)
  return HashKeyBag(v,101,0,Length(v)+GAPInfo.BytesPerVariable) 
         mod data + 1;
end );

InstallMethod( ChooseHashFunction, "for strings",
  [ IsStringRep, IsInt ],
  function( s, len )
    return rec( func := HashFunctionForStrings, data := len );
  end );

InstallMethod( Rep, "for a list and a positive integer",
  [ IsList, IsPosInt ],
  function( s, n )
    local i,t;
    t := EmptyList(Length(s)*n,s);
    for i in [1..n] do 
        Append(t,s);
    od;
    return t;
  end );

# Cyclic words:

InstallMethod(CyclicWord, "for a list", [IsList],
  function( l )
    local i,o,len,ll,lll;
    len := Length(l);
    ll := LexLeastRotation(l);
    lll := EmptyList(Length(ll[1])*ll[2],l);
    for i in [1..ll[2]] do Append(lll,ll[1]); od;
    o := [lll,EmptyList(2*len,l),len];
    Append(o[2],lll);
    Append(o[2],lll);
    MakeImmutable(o);
    return Objectify(CyclicWordType,o);
  end );

InstallMethod(ViewObj, "for a cyclic word",
  [ IsCyclicWordStdRep ],
  function( c )
    Print("CyclicWord(");
    ViewObj(c![1]);
    Print(")");
  end );

InstallMethod(PrintObj, "for a cyclic word",
  [ IsCyclicWordStdRep ],
  function( c )
    Print("CyclicWord(");
    ViewObj(c![1]);
    Print(")");
  end );

InstallMethod(Length, "for a cyclic word",
  [ IsCyclicWordStdRep ],
  function( c )
    return c![3];
  end );

InstallMethod(Word, "for a cyclic word",
  [ IsCyclicWordStdRep ],
  function( c )
    return c![1];
  end );


# Rewrite systems:
InstallMethod( RewriteSystem, "for an alphabet and a list of rewrites",
  [ IsList, IsList ],
  function( a, r )
    return RewriteSystem(a,r,rec());
  end );

InstallMethod( RewriteSystem, "for an alphabet and a list of rewrites",
  [ IsList, IsList, IsList ],
  function( a, l, r )
    return RewriteSystem(a,l,r,rec());
  end );

InstallMethod( RewriteSystem, "for an alphabet and a list of rewrites",
  [ IsList, IsList, IsRecord ],
  function( a, r, opt )
    local len;
    len := Length(r);
    if IsOddInt(len) then
        Error("list of rewrites must be of even length");
        return fail;
    fi;
    return RewriteSystem(a,r{[1,3..len-1]},r{[2,4..len]},opt);
  end );

InstallMethod( RewriteSystem, "for an alphabet, two lists, and a record",
  [ IsList, IsList, IsList, IsRecord ],
  function( alphabet, LHSs, RHSs, opt )
    local L,hashlen,hashlen2,hf,ht,ht2,ht3,i,j,k,len,maxlen,pre,post,rws,
          s,states,sub,tab,w,x;

    if not(IsBound(opt.check)) then opt.check := true; fi;

    len := Length(LHSs);
    if len <> Length(RHSs) then
        Error("LHSs and RHSs must be lists of equal length");
        return fail;
    fi;
    rws := rec( alphabet := alphabet, lefts := LHSs,
                rights := RHSs, prefixhash := fail, 
                subhash := fail, suffixhash := fail,
                fsa := fail, states := fail );
    Objectify(RewriteSystemType, rws);
    # Check that every left hand side does not occur in any other LHS
    # or any right hand side:
    if opt.check then
        Info(InfoRWS,1,"Checking soundness of rewrites...");
        for i in [1..len] do
            L := rws!.lefts[i];
            for j in [1..len] do
                if i <> j then
                    if PositionSublist(rws!.lefts[j],L) <> fail then
                        Error("LHS ",L," is contained in LHS ",rws!.lefts[j]);
                        return fail;
                    fi;
                fi;
                if PositionSublist(rws!.rights[j],L) <> fail then
                    Error("LHS ",L," is contained in RHS ",rws!.rights[j]);
                fi;
            od;
        od;
    fi;

    # Compute prefix hash and make states for prefixes
    rws!.fsa := FSAState(alphabet,EmptyList(0,alphabet),0);
    states := [];
    Add(states,rws!.fsa);
    rws!.states := states;
    maxlen := Maximum(List(rws!.lefts,Length));
    hashlen := NextPrimeInt(QuoInt(maxlen * len * 6,2));
    hashlen2 := NextPrimeInt(QuoInt(maxlen * maxlen * len * 3,2));
    if IsPlistRep(alphabet) then
        hf := MakeHashFunctionForPlainFlatList(hashlen);
        ht := HTCreate(alphabet,rec( hf := hf.func, hfd := hf.data,
                                     hashlen := hashlen ));
        ht2 := HTCreate(alphabet,rec( hf := hf.func, hfd := hf.data,
                                      hashlen := hashlen2 ));
        ht3 := HTCreate(alphabet,rec( hf := hf.func, hfd := hf.data,
                                      hashlen := hashlen ));
    else
        ht := HTCreate(alphabet,rec( hashlen := hashlen ));
        ht2 := HTCreate(alphabet,rec( hashlen := hashlen2 ));
        ht3 := HTCreate(alphabet,rec( hashlen := hashlen ));
    fi;
    for i in [1..len] do
        L := rws!.lefts[i];
        for j in [1..Length(L)] do
            pre := L{[1..j]};
            tab := HTValue(ht,pre);
            if tab = fail then
                if j = Length(L) then
                    tab := [FSAState(alphabet,pre,i),[i]];
                else
                    tab := [FSAState(alphabet,pre,0),[i]];
                fi;
                Add(states,tab[1]);
                HTAdd(ht,pre,tab);
            else
                AddSet(tab[2],i);
            fi;
        od;
        for j in [2..Length(L)-1] do
            for k in [j..Length(L)-1] do
                sub := L{[j..k]};
                tab := HTValue(ht2,sub);
                if tab = fail then
                    tab := [i,j,k];
                    HTAdd(ht2,sub,tab);
                else
                    Append(tab,[i,j,k]);
                fi;
            od;
        od;
        for j in [1..Length(L)] do
            post := L{[j..Length(L)]};
            tab := HTValue(ht3,post);
            if tab = fail then
                tab := [i];
                HTAdd(ht3,post,tab);
            else
                Add(tab,i);
            fi;
        od;
    od;

    # Complete automaton:
    rws!.prefixhash := ht;
    rws!.subhash := ht2;
    rws!.suffixhash := ht3;
    for s in states do
        if s!.complete = 0 then  # otherwise do not bother
            for x in alphabet do
                w := ShallowCopy(s!.prefix);
                Add(w,x);
                tab := HTValue(ht,w);
                if tab <> fail then
                    # a new, longer prefix!
                    LinkFSAStates(s,x,tab[1]);
                else
                    # no longer a prefix, so drop the first letter
                    # until
                    while true do
                        if Length(w) = 1 then
                            LinkFSAStates(s,x,rws!.fsa);
                            break;
                        fi;
                        w := w{[2..Length(w)]};  # this is nonempty
                        tab := HTValue(ht,w);
                        if tab <> fail then
                            # we found another prefix or even a rewrite!
                            LinkFSAStates(s,x,tab[1]);
                            break;
                        fi;
                    od;
                fi;
            od;
        fi;
    od;
    return rws;
  end );

InstallMethod( ViewObj, "for a rewrite system",
  [ IsRewriteSystemStdRep ],
  function( rws )
    Print("<rewrite system on ");
    ViewObj(rws!.alphabet);
    Print(" with ",Length(rws!.lefts)," rewrites>");
  end);

InstallMethod( Display, "for a rewrite system",
  [ IsRewriteSystemStdRep ],
  function( rws )
    local i;
    Print("<rewrite system on ");
    ViewObj(rws!.alphabet);
    Print(" with ",Length(rws!.lefts)," rewrites:\n");
    if IsStringRep(rws!.alphabet) then
        for i in [1..Length(rws!.lefts)] do
            Print("  \"",rws!.lefts[i],"\" -> \"",rws!.rights[i],"\"\n");
        od;
    else
        for i in [1..Length(rws!.lefts)] do
            Print("  [",StringWordStripped(rws!.lefts[i]),"] -> [",
                        StringWordStripped(rws!.rights[i]),"]\n");
        od;
    fi;
    Print(" corresponding FSA has ",Length(rws!.states)," states.>\n");
  end );

InstallMethod( FSAState, "for an alphabet and a prefix and a rewrite number",
  [ IsList, IsList, IsInt ],
  function( alphabet, prefix, complete )
    local s;
    s := rec( prefix := prefix, complete := complete,
              hashels := EmptyList(Length(alphabet),alphabet),
              hashvals := EmptyPlist(Length(alphabet)), 
              alphsize := Length(alphabet) );
    return Objectify(FSAStateType,s);
  end );

InstallMethod( EQ, "for two FSA states",
  [ IsFSAStateStdRep, IsFSAStateStdRep ],
  function( s1, s2 )
    return s1!.prefix = s2!.prefix;
  end );

InstallMethod( LT, "for two FSA states",
  [ IsFSAStateStdRep, IsFSAStateStdRep ],
  function( s1, s2 )
    return s1!.prefix < s2!.prefix;
  end );

InstallMethod( ViewObj, "for an FSAState",
  [ IsFSAStateStdRep ],
  function( s )
    Print("<FSAState ");
    ViewObj(s!.prefix);
    Print(" rw=",s!.complete,">");
  end );

InstallMethod( LookupStep, "for an FSAState and a letter",
  [ IsFSAStateStdRep, IsObject ],
  function( s, x )
    local pos,start;
    if IsInt(x) then
        pos := x mod s!.alphsize + 1;
    elif IsChar(x) then
        pos := IntChar(x) mod s!.alphsize + 1;
    fi;
    start := pos;
    while true do
        if not(IsBound(s!.hashels[pos])) then return fail; fi;
        if x = s!.hashels[pos] then return s!.hashvals[pos]; fi;
        pos := pos + 1;
        if pos > s!.alphsize then pos := 1; fi;
        if pos = start then Error("Letter ",x," not in alphabet!"); fi;
    od;
  end );

InstallMethod( LinkFSAStates, "for an FSAState and a letter and a FSAState",
  [ IsFSAStateStdRep, IsObject, IsFSAStateStdRep ],
  function( s, x, t )
    local pos;
    if IsInt(x) then
        pos := x mod s!.alphsize + 1;
    elif IsChar(x) then
        pos := IntChar(x) mod s!.alphsize + 1;
    fi;
    while true do
        if not(IsBound(s!.hashels[pos])) then 
            s!.hashels[pos] := x;
            s!.hashvals[pos] := t;
            return true;
        fi;
        if x = s!.hashels[pos] then 
            return fail;
        fi;
        pos := pos + 1;
        if pos > s!.alphsize then pos := 1; fi;
    od;
  end );

InstallMethod( FoundRewrite, "for a FSAState",
  [ IsFSAStateStdRep ],
  function( s )
    return s!.complete;
  end );

InstallMethod( FindOneRewrite, "for a RWS and a word",
  [ IsRewriteSystemStdRep, IsList ],
  function( rws, w )
    local i,rw,s;
    s := rws!.fsa;
    i := 0;
    while i < Length(w) do
        i := i + 1;
        s := LookupStep(s,w[i]);
        rw := FoundRewrite(s);
        if rw > 0 then
            return [rw,i-Length(s!.prefix)+1,i];
        fi;
    od;
    return fail;
  end );

InstallMethod( FindAllRewrites, "for a RWS and a word",
  [ IsRewriteSystemStdRep, IsList ],
  function( rws, w )
    local i,res,rw,s;
    s := rws!.fsa;
    i := 0;
    res := [];
    while i < Length(w) do
        i := i + 1;
        s := LookupStep(s,w[i]);
        rw := FoundRewrite(s);
        if rw > 0 then
            Add(res,[rw,i-Length(s!.prefix)+1,i]);
            i := i-Length(s!.prefix)+1;
            s := rws!.fsa;
        fi;
    od;
    return res;
  end );

InstallMethod( ApplyRewrite, "for a RWS, a word and a rewrite desc",
  [ IsRewriteSystemStdRep, IsList, IsList ],
  function( rws, w, r )
    return Concatenation(w{[1..r[2]-1]},
                         rws!.rights[r[1]],
                         w{[r[3]+1..Length(w)]});
  end );

InstallMethod( IsIrreducible, "for a RWS and a word",
  [ IsRewriteSystemStdRep, IsList ],
  function( rws, w )
    local r;
    r := FindOneRewrite(rws,w);
    return r = fail;
  end );

InstallMethod( FindOneRewrite, "for a RWS and a cyclic word",
  [ IsRewriteSystemStdRep, IsCyclicWordStdRep ],
  function( rws, cw )
    local i,len,rw,s,w;
    s := rws!.fsa;
    len := cw![3];
    w := cw![2];
    i := 0;
    while i - Length(s!.prefix) + 1 <= len and Length(s!.prefix) < len do
        i := i + 1;
        s := LookupStep(s,w[i]);
        rw := FoundRewrite(s);
        if rw > 0 then
            return [rw,i-Length(s!.prefix)+1,i];
        fi;
    od;
    return fail;
  end );

InstallMethod( FindAllRewrites, "for a RWS and a cyclic word",
  [ IsRewriteSystemStdRep, IsCyclicWordStdRep ],
  function( rws, cw )
    local i,len,res,rw,s,w;
    s := rws!.fsa;
    len := cw![3];
    w := cw![2];
    i := 0;
    res := [];
    while i - Length(s!.prefix) + 1 <= len and Length(s!.prefix) < len do
        i := i + 1;
        s := LookupStep(s,w[i]);
        rw := FoundRewrite(s);
        if rw > 0 then
            # We might have overrun just now:
            if i - Length(s!.prefix) + 1 > len then break; fi;
            Add(res,[rw,i-Length(s!.prefix)+1,i]);
            i := i-Length(s!.prefix)+1;
            s := rws!.fsa;
        fi;
    od;
    return res;
  end );

InstallMethod( ApplyRewrite, "for a RWS, a cyclic word and a rewrite desc",
  [ IsRewriteSystemStdRep, IsCyclicWordStdRep, IsList ],
  function( rws, cw, r )
    if r[3] <= cw![3] then
        return CyclicWord(Concatenation(cw![2]{[1..r[2]-1]},
                                        rws!.rights[r[1]],
                                        cw![2]{[r[3]+1..cw![3]]}));
    else
        return CyclicWord(Concatenation(cw![2]{[r[3]-cw![3]+1..r[2]-1]},
                                        rws!.rights[r[1]]));
    fi;
  end );

InstallMethod( IsIrreducible, "for a RWS and a word",
  [ IsRewriteSystemStdRep, IsCyclicWordStdRep ],
  function( rws, cw )
    local r;
    r := FindOneRewrite(rws,cw);
    return r = fail;
  end );

InstallMethod( ShowRewrite, "for a rws, a word, and fail",
  [ IsRewriteSystemStdRep, IsList, IsBool ],
  function( rws, w, rw )
    Print("Word: ",w,"\n   => No rewrite applies.\n");
    return;
  end );


InstallMethod( ShowRewrite, "for a rws, a word, and a rewrite spec",
  [ IsRewriteSystemStdRep, IsList, IsList ],
  function( rws, w, rw )
    local i,j,s;
    if w{[rw[2]..rw[3]]} <> rws!.lefts[rw[1]] then
        Error("Wrong rewrite!");
    fi;
    Print("Word: ",w,"\n");
    Print("      ");
    if IsStringRep(w) then
        for i in [1..rw[2]-1] do Print(" "); od;
        Print(w{[rw[2]..rw[3]]});
    else
        Print("  ");
        for i in [1..rw[2]-1] do
            s := String(w[i]);
            for j in [1..Length(s)] do
                Print(" ");
            od;
            Print("  ");
        od;
        for i in [rw[2]..rw[3]-1] do
            Print(w[i],", ");
        od;
        Print(w[rw[3]]);
    fi;
    Print(" -> ",rws!.rights[rw[1]],"\n");
    Print("   => ",ApplyRewrite(rws,w,rw),"\n");
  end );

InstallMethod( ShowRewrite, "for a rws, a cyclic word, and fail",
  [ IsRewriteSystemStdRep, IsCyclicWord, IsBool ],
  function( rws, w, rw )
    Print(w,"\n   => No rewrite applies.\n");
    return;
  end );

InstallMethod( ShowRewrite, "for a rws, a cyclic word, and a rewrite spec",
  [ IsRewriteSystemStdRep, IsCyclicWordStdRep, IsList ],
  function( rws, cw, rw )
    local i,j,s,len,w;
    len := cw![3];
    w := cw![2];
    if w{[rw[2]..rw[3]]} <> rws!.lefts[rw[1]] then
        Error("Wrong rewrite!");
    fi;
    Print(cw,"\n");
    Print("           ");
    if IsStringRep(w) then
        Print(" ");
        for i in [1..rw[2]-1] do Print(" "); od;
        Print(w{[rw[2]..rw[3]]});
    else
        Print("  ");
        for i in [1..rw[2]-1] do
            s := String(w[i]);
            for j in [1..Length(s)] do
                Print(" ");
            od;
            Print("  ");
        od;
        for i in [rw[2]..rw[3]-1] do
            Print(w[i],", ");
        od;
        Print(w[rw[3]]);
    fi;
    Print(" -> ",rws!.rights[rw[1]],"\n");
    Print(" => ",ApplyRewrite(rws,cw,rw),"\n");
  end );

BindGlobal( "RWS_Reduction_Function_Cyclic_and_Words",
  function(rws,w)
    local r;
    #Info(InfoRWS,3,"Reduce");
    while true do
        r := FindOneRewrite(rws,w);
        if r = fail then return w; fi;
        #ShowRewrite(rws,w,r);
        w := ApplyRewrite(rws,w,r);
    od;
  end );

InstallMethod( Reduce, "for a rewrite system and a cyclic word",
  [IsRewriteSystemStdRep, IsCyclicWordStdRep],
  RWS_Reduction_Function_Cyclic_and_Words );

InstallMethod( Reduce, "for a rewrite system and a word",
  [IsRewriteSystemStdRep, IsList],
  RWS_Reduction_Function_Cyclic_and_Words );

# Infrastructures:

InstallMethod( InfraStructure, 
  "for an alphabet, the inverses, some rewrites, a comp function, data",
  [ IsList, IsList, IsList, IsFunction, IsRecord ],
  function( alph, ialph, rws, comp, data )
    # This takes an alphabet, the list of inverses in the corresponding order,
    # a zipped list of additional infrastructure rewrites, a comparison
    # function and a record of additional data for the comparison.
    # The comparison function is called with (infra, a, b) where
    # infra is the infrastructure object. The components of the record
    # are copied into infra. a and b are words (represented as lists).
    local L,R,infra,n,pos,x;
    alph := ShallowCopy(alph);
    ialph := ShallowCopy(ialph);
    if Length(Set(alph)) <> Length(alph) then
        Error("Alphabet must not contain duplicates");
        return fail;
    fi;
    # Complete infrastructure rewrite system:
    rws := Set(ShallowCopy(rws));
    for n in [1..Length(alph)] do
        L := EmptyList(2,alph);
        R := EmptyList(0,alph);
        L[1] := alph[n];
        L[2] := ialph[n];
        AddSet(rws,[L,R]);
    od;
    infra := rec( alph := alph, ialph := ialph, alphsize := Length(alph),
                  alphhash := EmptyList(Length(alph),alph),
                  alphposs := EmptyPlist(Length(alph)),
                  lefts := List(rws,x->x[1]),
                  rights := List(rws,x->x[2]),
                  rws := RewriteSystem(alph,Concatenation(rws)),
                  compare := comp );
    for n in RecFields(data) do
        infra.(n) := data.(n);
    od;
    # Build up hash:
    for n in [1..Length(alph)] do
        x := alph[n];
        if IsInt(x) then
            pos := x mod infra!.alphsize + 1;
        else
            pos := IntChar(x) mod infra!.alphsize + 1;
        fi;
        while true do
            if not(IsBound(infra!.alphhash[pos])) then break; fi;
            pos := pos + 1;
            if pos > infra!.alphsize then pos := 1; fi;
        od;
        infra!.alphhash[pos] := x;
        infra!.alphposs[pos] := n;
    od;
    return Objectify(InfraStructureType, infra);
  end );

InstallMethod( ViewObj, "for an infrastructure",
  [IsInfraStructureStdRep],
  function(i)
    local n;
    Print("<infrastructure alph=",i!.alph," ialph=",i!.ialph,"\n");
    if IsStringRep(i!.alph) then
        for n in [1..Length(i!.lefts)] do
            Print(" "); ViewObj(i!.lefts[n]); 
            Print("->"); ViewObj(i!.rights[n]);
        od;
    else
        for n in [1..Length(i!.lefts)] do
            Print(" [",StringWordStripped(i!.lefts[n]),
                 "]->[",StringWordStripped(i!.rights[n]),"]");
        od;
    fi;
    if IsBound(i!.weights) then
        Print(" weights=", i!.weights);
    fi;
    Print(">");
  end );

InstallMethod( Lookup, "for an infrastructure and a letter",
  [ IsInfraStructureStdRep, IsObject ],
  function(i, x)
    local pos;
    if IsInt(x) then
        pos := x mod i!.alphsize + 1;
    else
        pos := IntChar(x) mod i!.alphsize + 1;
    fi;
    while true do
        if i!.alphhash[pos] = x then return i!.alphposs[pos]; fi;
        pos := pos + 1;
        if pos > i!.alphsize then
            pos := 1;
        fi;
    od;
  end );

InstallMethod( Invert, "for an infrastructure and a word",
  [ IsInfraStructureStdRep, IsList ],
  function( i, w )
    local n,l,wi;
    wi := EmptyList(Length(w),w);
    l := Length(w);
    for n in [1..l] do
        wi[n] := i!.ialph[Lookup(i,w[l+1-n])];
    od;
    return wi;
  end );

InstallMethod( Invert, "for an infrastructure and a cyclic word",
  [ IsInfraStructureStdRep, IsCyclicWordStdRep ],
  function( i, cw )
    return CyclicWord(Invert(i,cw![1]));
  end );

InstallMethod( Cancel, "for an infrastructure and a word",
  [ IsInfraStructureStdRep, IsList ],
  function( i, w )
    return Reduce(i!.rws,w);
  end );

InstallMethod( Cancel, "for an infrastructure and a cyclic word",
  [ IsInfraStructureStdRep, IsCyclicWordStdRep ],
  function( i, cw )
    return Reduce(i!.rws,cw);
  end );

InstallMethod( IsCancelled, "for an infrastructure and a word",
  [ IsInfraStructureStdRep, IsList ],
  function( i, w )
    return IsIrreducible(i!.rws,w);
  end );
 
InstallMethod( IsCancelled, "for an infrastructure and a cyclic word",
  [ IsInfraStructureStdRep, IsCyclicWordStdRep ],
  function( i, cw )
    return IsIrreducible(i!.rws,cw);
  end );
 
InstallGlobalFunction( CompareByWeights,
  function( infra, a, b )
    local wa, wb;
    wa := Sum(a,x->infra!.weights[Lookup(infra,x)]);
    wb := Sum(b,x->infra!.weights[Lookup(infra,x)]);
    return wa - wb;
  end );

InstallMethod( Compare, "for an infrastructure and two words",
  [ IsInfraStructureStdRep, IsList, IsList ],
  function( infra, a, b )
    return infra!.compare(infra,a,b);
  end );

InstallMethod( DehnRewrites, "for an infrastructure and a list of relators",
  [ IsInfraStructureStdRep, IsList ],
  function( infra, rels )
    local AddNewRewrite,CheckOverlap,Reduce,ResolveEquation,
          arws,atocheck,eqeq,eqts,irws,itocheck;

    irws := List([1..Length(infra!.lefts)],
                 i->[infra!.lefts[i],infra!.rights[i]]);
    arws := [];
    eqts := List(rels,r->[r,EmptyList(0,r)]);
    eqeq := [];
    itocheck := 1;
    atocheck := 1;
    
    Reduce := function(w)
        local a,i,pos;
        i := 1;
        a := 1;
        # Print("Newreduce\n");
        while true do
            # Print("Reduce:",w,"\n");
            while i <= Length(irws) do
                pos := PositionSublist(w,irws[i][1]);
                if pos <> fail then
                    w := Concatenation(w{[1..pos-1]},
                                       irws[i][2],
                                       w{[pos+Length(irws[i][1])..Length(w)]});
                    i := 1;
                else
                    i := i + 1;
                fi;
            od;
            if Length(arws) = 0 then return w; fi;
            while true do
                pos := PositionSublist(w,arws[a][1]);
                if pos <> fail then
                    w := Concatenation(w{[1..pos-1]},
                                       arws[a][2],
                                       w{[pos+Length(arws[a][1])..Length(w)]});
                    i := 1;
                    a := 1;
                    break;
                else
                    a := a + 1;
                    if a > Length(arws) then return w; fi;
                fi;
            od;
        od;
    end;

    CheckOverlap := function(i,a)
        local A,I,P,Q,l,lA,lI;
        I := irws[i][1];
        A := arws[a][1];
        #Debug("CheckOverlap",I,A);
        lI := Length(I);
        lA := Length(A);
        for l in [1..Minimum(lI,lA)-1] do  # len of overlap
            if I{[lI-l+1]} = A{[1..l]} then
                P := Reduce(Concatenation(irws[i][2],A{[l+1..lA]}));
                Q := Reduce(Concatenation(I{[1..lI-l]},arws[a][2]));
                if P <> Q then Add(eqts,[P,Q]); fi;
            fi;
            if A{[lA-l+1]} = I{[1..l]} then
                P := Reduce(Concatenation(arws[a][2],I{[l+1..lI]}));
                Q := Reduce(Concatenation(A{[1..lA-l]},irws[i][2]));
                if P <> Q then 
                    Add(eqts,[P,Q]); 
                    #Debug("Adding equation",[P,Q]);
                fi;
            fi;
        od;
    end;
    
    AddNewRewrite := function(L,R)
        local i,pos,pos2;
        #Debug("AddRewrite",[L,R]);
        Add(arws,[L,R]);
        for i in [1..Length(irws)] do
            pos := PositionSublist(irws[i][1],L);
            if pos <> fail then
                Error("LHS of new rewrite is contained in infrastructure LHS");
            fi;
            pos := PositionSublist(irws[i][2],L);
            if pos <> fail then
                Error("LHS of new rewrite is contained in infrastructure RHS");
            fi;
        od;
        i := 1;
        while i < Length(arws) do   # skip ourselves!
            pos := PositionSublist(arws[i][1],L);
            pos2 := PositionSublist(arws[i][2],L);
            if pos <> fail or pos2 <> fail then
                #Debug("Removing rewrite",arws[i]);
                Add(eqts,Remove(arws,i),1);
                if atocheck > i then atocheck := atocheck - 1; fi;
            else
                i := i + 1;
            fi;
        od;
    end;

    ResolveEquation := function()
        local a,b,c,eq;
        eq := Remove(eqts);
        #Debug("ResolveEquation",eq);
        a := Reduce(eq[1]);
        b := Reduce(eq[2]);
        if a = b then return; fi;   # everything OK
        c := Compare(infra,a,b);
        if c = 0 then 
            Info(InfoRWS,1,"Two reductions compare equal:",a," ",b); 
            AddSet(eqeq,Set([a,b]));
            return;
        fi;
        if c < 0 then 
            # a is smaller
            c := a; a := b; b := c;
        fi;
        AddNewRewrite(a,b);
    end;

    while true do
        #Debug("Main loop",irws,arws,eqts);
        while atocheck <= Length(arws) do
            while itocheck <= Length(irws) do
                CheckOverlap(itocheck,atocheck);
                itocheck := itocheck + 1;
            od;
            itocheck := 1;
            atocheck := atocheck + 1;
        od;
        if Length(eqts) = 0 then break; fi;
        ResolveEquation();
    od;

    return rec( rws := Concatenation(irws,arws),
                infra := infra,
                nrirws := Length(irws),
                equations := eqeq );
  end );


InstallMethod( InvertOld, "for a sorted alphabet, its inverses, and a word",
  [IsList and IsSet, IsList, IsList],
  function( alph, ialph, w )
    local i,l,wi;
    wi := EmptyList(Length(w),w);
    l := Length(w);
    for i in [1..l] do
        wi[i] := ialph[Position(alph,w[l+1-i])];
    od;
    return wi;
  end );


InstallMethod( DehnRewrites1,
  "for an alphabet, the inverse alphabet, and a list of relators",
  [ IsList, IsList, IsList ],
  function( alph, ialph, rels )
    local i,inv,l,l2,l3,r,r1,rest,rr,rws,salph,sialph;
    if Length(Set(alph)) <> Length(alph) or
       Length(ialph) <> Length(alph) or
       Set(alph) <> Set(ialph) then
        Error("Inverse alphabet incorrect");
        return fail;
    fi;
    salph := ShallowCopy(alph);
    sialph := ShallowCopy(ialph);
    SortParallel(salph,sialph);
    rws := [];
    for i in [1..Length(salph)] do
        AddSet(rws,[Concatenation(salph{[i]},sialph{[i]}),EmptyList(0,salph)]);
    od;
    for r1 in rels do
        for r in Set([r1,InvertOld(salph,sialph,r1)]) do
            l := Length(r);
            l2 := QuoInt(l,2)+1;
            l3 := l-l2;
            rr := Concatenation(r,r);
            for i in [1..l] do
                rest := rr{[i+l2..i+l-1]};
                inv := InvertOld(salph,sialph,rest);
                AddSet(rws,[rr{[i..i+l2-1]},inv]);
            od;
        od;
    od;
    return rec( alph := salph, ialph := sialph, rws := Concatenation(rws) );
  end );

InstallMethod( DehnRewrites1, "for a record",
  [ IsRecord ],
  function( r )
    return DehnRewrites1(r.alph, r.ialph, r.rels);
  end );

InstallGlobalFunction(CanBeRewrittenToEmptyFunc,
  function( rws, cw )
    local all,res,x;
    if Length(cw) = 0 then
      return [cw];
    fi;
    all := List(FindAllRewrites(rws,cw),x->ApplyRewrite(rws,cw,x));
    for x in all do
      res := CanBeRewrittenToEmpty(rws,x);
      if res <> fail then
        Add(res,cw,1);
        return res;
      fi;
    od;
    return fail;
  end );

InstallMethod( CanBeRewrittenToEmpty, "for a rws and a cyclic word",
  [ IsRewriteSystemStdRep, IsCyclicWordStdRep ],
  CanBeRewrittenToEmptyFunc );

InstallMethod( CanBeRewrittenToEmpty, "for a rws and a word",
  [ IsRewriteSystemStdRep, IsList ],
  CanBeRewrittenToEmptyFunc );

InstallGlobalFunction(DoesAlwaysRewriteToEmptyFunc,
  function( rws, cw)
    local all,res,x;
    if Length(cw) = 0 then return true; fi;
    all := List(FindAllRewrites(rws,cw),x->ApplyRewrite(rws,cw,x));
    if Length(all) = 0 then return [cw]; fi;
    for x in all do
      res := DoesAlwaysRewriteToEmptyFunc(rws,x);
      if res <> true then
        Add(res,cw,1);
        return res;
      fi;
    od;
    return true;
  end );

InstallMethod( DoesAlwaysRewriteToEmpty, "for a rws and a cyclic word",
  [ IsRewriteSystemStdRep, IsCyclicWordStdRep ],
  DoesAlwaysRewriteToEmptyFunc );

InstallMethod( DoesAlwaysRewriteToEmpty, "for a rws and a word",
  [ IsRewriteSystemStdRep, IsList ],
  DoesAlwaysRewriteToEmptyFunc );

# Here comes the implementation of our algorithm proper:

InstallMethod( FindLHSDoubleOverlaps, 
  "for a rewrite system and a word",
  [ IsRewriteSystemStdRep, IsList ],
  function( rws, w )
    # The list is a word. This operation finds all ways in
    # which a left hand side of the rewrite system overlaps the word
    # on both sides, closing a cyclic word. A list of lists is returned,
    # each containing: The complete cyclic word as a word with w at the
    # beginning, the length of the overlap from w to L, the length
    # of the overlap from L to w and finally the complete cyclic word 
    # as a word where the left hand side has been replaced by the right
    # hand side.
    local found,ht,i,j,k,l,len,len2,lhs,res,suf,tab;
    res := [];
    ht := rws!.prefixhash;
    len := Length(w);
    for i in [1..len-1] do
        suf := w{[len-i+1..len]};
        tab := HTValue(ht,suf);
        if tab <> fail then
            for j in tab[2] do    # Those are the LHSs with this as prefix
                lhs := rws!.lefts[j];
                len2 := Length(lhs);
                for k in [1..Minimum(len2-i,len-i)] do
                    # This is the amount of overlap between lhs and w we try
                    found := true;
                    for l in [1..k] do
                        if w[l] <> lhs[len2-k+l] then
                            found := false;
                            break;
                        fi;
                    od;
                    if found then
                      Add(res,[Concatenation(w,lhs{[i+1..len2-k]}),i,k,
                               Concatenation(w{[k+1..Length(w)-i]},
                                             rws!.rights[j])]);
                    fi;
                od;
            od;
        fi;
    od;
    return res;
  end );

InstallMethod( CWPattern, "for a rws and lots of words",
  [IsRewriteSystemStdRep, IsList, IsList, IsList, IsChar ],
  function( rws, W, Pp, Qp, whereeps )
    # The fundamental constructor, W is a list of 5 words [X,A,B,C,Y]
    # AB -> P and BC -> Q are two overlapping rewrites,
    # XPCY => Pp (irreducible) and XAQY => Qp (irreducible)
    # This pattern matches all cyclic words that contain the word XABCY
    # as a subword.
    # We actually look for cyclic words (XABCYV) such that
    #   - (XPCYV) => (eps)    regardless on how we rewrite
    #   - not((XAQYV) => (eps))
    # (case whereeps='L') or vice versa (case whereeps='R'). 
    # In any case this implies that there is no cyclic word (W)
    # such that both (PpV) => (W) and (QpV) => (W), in particular (PpV)<>(QpV).
    # A forteriori, there is no word W with Pp => W and Qp => W and Pp<>Qp
    # Furthermore, YVX is irreducible, so X and Y are irred. in particular.
    # This describes the purpose of this data type, thus the assertions.
    local p;
    p := rec( rws := rws, 
              X := W[1], A := W[2], B := W[3], C := W[4], Y := W[5], 
              Pp := Pp, Qp := Qp, whereeps := whereeps,
              len := Length(W[1])+Length(W[2])+Length(W[3])+Length(W[4])+
                     Length(W[5]) );
    Assert(1, IsIrreducible(rws,p.X) and IsIrreducible(rws,p.Y) and
              IsIrreducible(rws,p.Pp) and IsIrreducible(rws,p.Qp));
    Assert(1, Pp <> Qp);
    return Objectify(CWPatternType,p);
  end );

InstallMethod( WordCWPattern, "for a CW pattern",
  [ IsCWPatternStdRep ],
  function( cw )
    return Concatenation(cw!.X, cw!.A, cw!.B, cw!.C, cw!.Y);
  end );

InstallMethod( EQ, "for two CW patterns",
  [ IsCWPatternStdRep, IsCWPatternStdRep ],
  function( a, b )
    return a!.X = b!.X and a!.A = b!.A and a!.B = b!.B and
           a!.C = b!.C and a!.Y = b!.Y and a!.whereeps = b!.whereeps;
  end );

InstallMethod( LT, "for two CW patterns",
  [ IsCWPatternStdRep, IsCWPatternStdRep ],
  function( a, b )
    return [a!.len,a!.whereeps,a!.X,a!.A,a!.B,a!.C,a!.Y] <
           [b!.len,b!.whereeps,b!.X,b!.A,b!.B,b!.C,b!.Y];
  end );

InstallMethod( StringWordStripped, "for a list of integers",
  [ IsList ],
  function( l )
    local i,s;
    s := EmptyString(3*Length(l));
    for i in l do
        Append(s,String(i));
        Add(s,',');
    od;
    Remove(s);
    return s;
  end );

InstallMethod( ViewObj, "for a CW pattern",
  [IsCWPatternStdRep],
  function( p )
    Print("<CWPat ");
    if IsStringRep(p!.X) then
        Print("(",p!.Pp,"|*) <= ");
        Print("(",p!.X,"<",p!.A,"|",p!.B,"|",p!.C,">",p!.Y,"|*)");
        Print(" => (",p!.Qp,"|*) ");
    else
        Print("(",StringWordStripped(p!.Pp),"|*) <= ");
        Print("(",StringWordStripped(p!.X),"<",
                  StringWordStripped(p!.A),"|",
                  StringWordStripped(p!.B),"|",
                  StringWordStripped(p!.C),">",
                  StringWordStripped(p!.Y),"|*)");
        Print(" => (",StringWordStripped(p!.Qp),"|*) ");
    fi;
    if p!.whereeps = 'L' then
        Print("left eps, len=",p!.len,">");
    else
        Print("right eps, len=",p!.len,">");
    fi;
  end );

 
InstallMethod( FindCriticalPairs, "for a rewrite system",
  [ IsRewriteSystemStdRep, IsCyclotomic ],
  function( rws, maxlen )
    # This finds the initial list of so called critical pairs. That is, these
    # are two left hand sides with a non-trivial overlap, i.e. a word
    # ABC such that AB->P and BC->Q are rewrites. The pair is critical,
    # if there is no W with PC=>W and AQ=>W.
    # This function uses some heuristics to find a list of pairs which contains
    # all critical pairs.
    # It only looks for critical pairs for which the total length of A, B
    # and C together is at most maxlen.
    local A,B,C,L,P,Q,V,Vl,W,conflue,ht,i,j,k,l,l2,r,res,t,tab;
    res := [];
    ht := rws!.prefixhash;
    for i in [1..Length(rws!.lefts)] do
        L := rws!.lefts[i];
        l := Length(L);
        if l < maxlen then
            for j in [2..l] do
                A := L{[1..j-1]};
                B := L{[j..l]};
                P := rws!.rights[i];
                tab := HTValue(rws!.prefixhash,B);
                if tab <> fail then
                    for k in tab[2] do   # this is the list of rewrites with 
                                         # this prefix in its LHS
                        l2 := Length(rws!.lefts[k]);
                        C := rws!.lefts[k]{[Length(B)+1..l2]};
                        if l + Length(C) <= maxlen then
                            Q := rws!.rights[k];
                            V := Concatenation(P,C);
                            W := Concatenation(A,Q);
                            t := Check(rws,V,W);
                            if t <> fail then
                                Add(res,rec( A := A, B := B, C := C, P := P, 
                                             Q := Q, Pp := t[2], Qp := t[3] ));
                            fi;
                        fi;
                    od;
                fi;
            od;
        fi;
    od;
    return res;
  end );

InstallMethod( EQ, "for two cyclic words",
  [ IsCyclicWordStdRep, IsCyclicWordStdRep ],
  function( V, W )
    return V![1] = W![1];
  end );

InstallMethod( LT, "for two cyclic words",
  [ IsCyclicWordStdRep, IsCyclicWordStdRep ],
  function( V, W )
    return V![1] < W![1];
  end );

BindGlobal( "RWS_Check_Func_For_Cyclic_and_Words",
  function( rws, V, W )
    # See whether or not we have found a pair of witnesses
    # This function simply rewrites both (cyclic) words until they
    # are irreducible. If one of them ends in the empty (cyclic) word and the
    # other not, then the pair is a witness and [true,Vp,Wp] is returned,
    # where Vp and Wp are the two irreducible (cyclic) words.
    # Otherwise [false,Vp,Wp] is returned. If some (cyclic) word is found
    # to which both rewrite (for example, if the (cyclic) words are
    # equal), then fail is returned.
    local Vs,r,res;
    if V = W then return fail; fi;
    Vs := [V];
    Info(InfoRWS,3,"Check 1: ",V);
    while true do
        r := FindOneRewrite(rws,V);
        if r = fail then break; fi;
        V := ApplyRewrite(rws,V,r);
        Info(InfoRWS,3,"      -> ",V);
        if V = W then 
            Info(InfoRWS,3,"same as second word --> fail");
            return fail; 
        fi;
        AddSet(Vs,V);
    od;
    Info(InfoRWS,3,"Check 2: ",W);
    while true do
        r := FindOneRewrite(rws,W);
        if r = fail then break; fi;
        W := ApplyRewrite(rws,W,r);
        Info(InfoRWS,3,"      -> ",W);
        if Position(Vs,W) <> fail then 
            Info(InfoRWS,3,"already seen from other word --> fail");
            return fail; 
         fi;
    od;
    res := (Length(V) = 0 and Length(W) > 0) or
           (Length(W) = 0 and Length(V) > 0);
    Info(InfoRWS,3,"Result of check: ",res);
    return [res,V,W];
  end );

InstallMethod( Check, "for a rewrite system and two cyclic words",
  [ IsRewriteSystemStdRep, IsCyclicWordStdRep, IsCyclicWordStdRep ],
  RWS_Check_Func_For_Cyclic_and_Words );

InstallMethod( Check, "for a rewrite system and two words",
  [ IsRewriteSystemStdRep, IsList, IsList ],
  RWS_Check_Func_For_Cyclic_and_Words );

InstallMethod( SetupSearchList, "for a search record and a list",
  [ IsRecord, IsList ],
  function( s, cr )
    # Sets up the main search list by taking the critical pairs in the
    # second argument (coming from FindCriticalPairs) and setting up the
    # data structures for the patterns.
    local c,e,pats,rws;
    rws := s.rws;
    pats := s.pats;
    e := EmptyList(0,rws!.lefts[1]);
    for c in cr do
        Add(pats,CWPattern(rws,[e,c.A,c.B,c.C,e],c.Pp,c.Qp,'L'));
        Add(pats,CWPattern(rws,[e,c.A,c.B,c.C,e],c.Pp,c.Qp,'R'));
    od;
    s.pats := Set(pats);   # Sort and remove duplicates
  end );

InstallMethod( SearchDescendants, "for a search record and a CW pattern",
  [ IsRecord, IsCWPatternStdRep ],
  function( s, cw )
    # Uses Lemma 2.3 to extend the cyclic word patterns.
    # Adds descendants (again cyclic word patterns) to r.pats and 
    # a list of pairs of witnesses found to r.wits.
    local Extend,L,P,Q,d,dd,desc,i,j,l,r,res,rws,start,stop,study,tab;

    Extend := function(cw,pre,post)
        local Pp,Qp,X,Y;
        #Debug(6,cw," Pre:",pre," Post:",post);
        if Length(cw!.X)+Length(cw!.A)+Length(cw!.B)+
           Length(cw!.C)+Length(cw!.Y)+Length(pre)+Length(post) > s!.lenlim then
            return false;
        fi;
        if Length(pre) > 0 then
            X := Concatenation(pre,cw!.X);
            if not(IsIrreducible(rws,X)) then return false; fi;
        else
            X := cw!.X;
        fi;
        if Length(post) > 0 then
            Y := Concatenation(cw!.Y,post);
            if not(IsIrreducible(rws,Y)) then return false; fi;
        else
            Y := cw!.Y;
        fi;
        Pp := Reduce(rws,Concatenation(pre,cw!.Pp,post));
        Qp := Reduce(rws,Concatenation(pre,cw!.Qp,post));
        #Debug(66,Pp,Qp);
        if Pp = Qp then return false; fi;
        Add(desc,CWPattern(rws,[X,cw!.A,cw!.B,cw!.C,Y],
                           Pp,Qp,cw!.whereeps));
        return true;
    end;

    desc := [];   # Here we collect the results
    rws := s.rws;
    if cw!.whereeps = 'L' then
        study := cw!.Pp;
    else
        study := cw!.Qp;
    fi;
    if Length(study) = 0 then
        #Debug(5);
        # First try an empty V:
        r := Check(rws,CyclicWord(cw!.Pp),CyclicWord(cw!.Qp));
        if r <> fail and r[1] = true then
            Add(s.wits,[cw,CyclicWord(cw!.Pp),CyclicWord(cw!.Qp)]);
        fi;
        # Now extend with all possible left hand sides:
        for L in rws!.lefts do
            l := Length(L);
            for i in [1..l-1] do
                Extend(cw,L{[1..i]},L{[i+1..l]});
            od;
        od;
    else
        #Debug(7);
        # This is the nonempty case
        # First find all double overlaps with left hand sides:
        d := FindLHSDoubleOverlaps(rws, study);
        for dd in d do
            if cw!.whereeps = 'L' then
                P := CyclicWord(dd[1]);
                Q := CyclicWord(Concatenation(cw!.Qp,
                                     dd[1]{[Length(cw!.Pp)+1..Length(dd[1])]}));
            else
                Q := CyclicWord(dd[1]);
                P := CyclicWord(Concatenation(cw!.Pp,
                                     dd[1]{[Length(cw!.Qp)+1..Length(dd[1])]}));
            fi;
            res := Check(rws,P,Q);
            if res <> fail and res[1] = true then
                Add(s.wits,[cw,P,Q,"DoubleOverlap"]);
            fi;
        od;
        #Debug(8);
        # Now find all left hand sides that have study as a substring:
        tab := HTValue(rws!.subhash,study);
        if tab <> fail then
            for i in [1,4..Length(tab)-2] do
                # We extend X and Y:
                L := rws!.lefts[tab[i]];
                start := tab[i+1];
                stop := tab[i+2];
                Extend(cw,L{[1..start-1]},L{[stop+1..Length(L)]});
            od;
        fi;
        #Debug(9);
        # Now extend to the right if study ends in a prefix of a LHS:
        l := Length(study);
        for i in [1..l] do
            tab := HTValue(rws!.prefixhash,study{[l-i+1..l]});
            if tab <> fail then
                for j in tab[2] do
                    L := rws!.lefts[j];
                    Extend(cw,EmptyList(0,L),L{[i+1..Length(L)]});
                od;
            fi;
        od;
        #Debug(10);
        # Now extend to the left if study starts with a suffix of a LHS:
        for i in [1..l] do
            tab := HTValue(rws!.suffixhash,study{[1..i]});
            if tab <> fail then
                for j in tab do
                    L := rws!.lefts[j];
                    Extend(cw,L{[1..Length(L)-i]},EmptyList(0,L));
                od;
            fi;
        od;
        #Debug(11);
    fi;
    return desc;
  end );

InstallMethod( CheckCyclicEpsilonConfluence, "for a rws and a pos integer",
  [ IsRewriteSystemStdRep, IsCyclotomic ],
  function( rws, n )
    local L,P,Q,critical,d,dd,i,lens,oldpats,p,res,s,w;

    s := rec( rws := rws, lenlim := n, wits := [], pats := [], stop := false );

    Info( InfoRWS, 1, "Looking for double overlaps of LHSs...");
    for i in [1..Length(rws!.lefts)] do
        L := rws!.lefts[i];
        #Debug(0);
        d := FindLHSDoubleOverlaps(rws, L);
        #Debug(1);
        for dd in d do
            w := dd[1];
            P := CyclicWord(ApplyRewrite(rws,w,[i,1,Length(L)]));
            Q := CyclicWord(dd[4]);
            res := Check(rws,P,Q);
            if res <> fail and res[1] = true then
                Add(s.wits,[L,dd[1],P,Q,"InitialDoubleOverlap"]);
            fi;
        od;
    od;
    Info( InfoRWS, 1, "Found ",Length(s.wits)," witnesses.");

    Info( InfoRWS, 1, "Finding critical pairs...");
    critical := FindCriticalPairs(rws, n);
    Info( InfoRWS, 1, "Found ", Length(critical), " critical pairs.");

    #Debug(2);

    Info( InfoRWS, 1, "Setting up pattern list...");
    SetupSearchList(s,critical);

    while true do
        Info( InfoRWS, 1, "Currently have ",Length(s.pats)," patterns and ",
              Length(s.wits)," witnesses.");
        if Length(s.pats) = 0 or Length(s.wits) > 0 or s.stop then break; fi;
        lens := List(s.pats,x->x!.len);
        Info( InfoRWS, 1, "Lengths: min=",Minimum(lens)," max=",Maximum(lens),
              " avg=",QuoInt(Sum(lens),Length(lens)) );
        oldpats := s.pats;
        s.pats := EmptyPlist(Length(s.pats));
        #Debug("x",Length(oldpats));
        for p in oldpats do
            #Debug(3);
            Append(s.pats,SearchDescendants(s,p));
        od;
    od;
    return s;
  end );

InstallMethod( CheckCyclicEpsilonConfluence2, 
  "for a rws and a pos integer and a record",
  [ IsRewriteSystemStdRep, IsCyclotomic, IsRecord ],
  function( rws, n, opt )
    local count,L,P,Q,critical,d,dd,i,lens,newpats,p,res,s,w;

    s := rec( rws := rws, lenlim := n, wits := [], pats := [], stop := false );
    if IsBound(opt.infra) then
        s.infra := opt.infra;
    fi;

    Info( InfoRWS, 1, "Looking for double overlaps of LHSs...");
    for i in [1..Length(rws!.lefts)] do
        L := rws!.lefts[i];
        #Debug(0,L);
        d := FindLHSDoubleOverlaps(rws, L);
        #Debug(1);
        for dd in d do
            #Debug(2,dd);
            w := dd[1];
            P := CyclicWord(ApplyRewrite(rws,w,[i,1,Length(L)]));
            Q := CyclicWord(dd[4]);
            res := Check(rws,P,Q);
            if res <> fail and res[1] = true then
                Add(s.wits,[L,dd[1],P,Q,"InitialDoubleOverlap"]);
            fi;
        od;
    od;
    Info( InfoRWS, 1, "Found ",Length(s.wits)," witnesses.");

    Info( InfoRWS, 1, "Finding critical pairs...");
    critical := FindCriticalPairs(rws, n);
    Info( InfoRWS, 1, "Found ", Length(critical), " critical pairs.");

    #Debug(2);

    Info( InfoRWS, 1, "Setting up pattern list...");
    SetupSearchList(s,critical);

    count := -1;
    while true do
        count := count + 1;
        if count mod 1000 = 0 then
            Info( InfoRWS, 1, "Currently have ",Length(s.pats)," patterns and ",
                  Length(s.wits)," witnesses.");
        fi;
        if Length(s.pats) = 0 or Length(s.wits) > 0 or s.stop then break; fi;
        lens := List(s.pats,x->x!.len);
        if count mod 1000 = 0 then
            Info( InfoRWS, 1, "Lengths: min=",Minimum(lens)," max=",
                  Maximum(lens)," avg=",QuoInt(Sum(lens),Length(lens)) );
        fi;
        p := Remove(s.pats,1);
        newpats := Set(SearchDescendants(s,p));
        if IsBound(opt.infra) then
            #Debug("pre",Length(newpats));
            newpats := Filtered(newpats,
                                p->IsCancelled(opt.infra,WordCWPattern(p)));
            #Debug("post",Length(newpats));
        fi;
        UniteSet(s.pats,newpats);
    od;
    return s;
  end );

InstallGlobalFunction( OneRelatorQuotientOfModularGroup,
function(n)
  local R,S,T,alph,ialph,l,rels;
  alph := "RST";
  ialph := "SRT";
  R := 'R';
  S := 'S';
  T := 'T';
  rels := ["SSS"];
  l := EmptyString(20);
  if n > 1 then
      while n > 1 do
          if IsOddInt(n) then
              Add(l,T,1);
              Add(l,R,1);
              n := (n-1)/2;
          else
              Add(l,T,1);
              Add(l,S,1);
              n := n/2;
          fi;
      od;
      Add(rels,l);
  fi;
  return rec( alph := alph, ialph := ialph, rels := rels );
end);

# rws := DehnRewriteSystem(OneRelatorQuotientOfModularGroup(1235617232));
# m11 := DehnRewriteSystem("Bab","baB",["bbbb",Rep("ab",11),Rep("abb",6),
#                                       "ababaBababbaBabaBaB"]);
#

# if L -> R and XLY -> Z
# we would replace this by
#    L -> R and XRY -> Z
# ==> all previous V => W remain true, we only do XLY -> XRY -> Z in two steps.
#     however, XRY could no longer be length-reducing and
#              XRY -> Z could previously not have been possible at all!
# 
# if L -> R and M -> XLY
# we would replace this by
#    L -> R and M -> XRY


##
##  This program is free software: you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation, either version 3 of the License, or
##  (at your option) any later version.
##
##  This program is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this program.  If not, see <http://www.gnu.org/licenses/>.
##
