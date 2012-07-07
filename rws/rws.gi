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
  [ IsList, IsList, IsRecord ],
  function( alphabet, rewrites, opt )
    local L,hashlen,hashlen2,hf,ht,ht2,ht3,i,j,k,len,maxlen,pre,post,rws,
          s,states,sub,tab,w,x;

    if not(IsBound(opt.check)) then opt.check := true; fi;

    len := Length(rewrites);
    if IsOddInt(len) then
        Error("rewrites must be a list of even length");
        return fail;
    fi;
    rws := rec( alphabet := alphabet, lefts := rewrites{[1,3..len-1]},
                rights := rewrites{[2,4..len]}, prefixhash := fail, 
                subhash := fail, postfixhash := fail,
                fsa := fail, states := fail );
    Objectify(RewriteSystemType, rws);
    len := len / 2;
    # Check that every left hand side does not occur in any other LHS
    # or any right hand side:
    if opt.check then
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
    hashlen := NextPrimeInt(QuoInt(maxlen * len * 3,2));
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
    rws!.postfixhash := ht3;
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
    while true do
        r := FindOneRewrite(rws,w);
        if r = fail then return w; fi;
        w := ApplyRewrite(rws,w,r);
    od;
  end );

InstallMethod( Reduce, "for a rewrite system and a cyclic word",
  [IsRewriteSystemStdRep, IsCyclicWordStdRep],
  RWS_Reduction_Function_Cyclic_and_Words );

InstallMethod( Reduce, "for a rewrite system and a word",
  [IsRewriteSystemStdRep, IsList],
  RWS_Reduction_Function_Cyclic_and_Words );


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
              Pp := Pp, Qp := Qp, whereeps := whereeps );
    Assert(1, IsIrreducible(rws,p.X) and IsIrreducible(rws,p.Y) and
              IsIrreducible(rws,p.Pp) and IsIrreducible(rws,p.Qp));
    Assert(1, Pp <> Qp);
    return Objectify(CWPatternType,p);
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
        Print("(",p!.X,"|",p!.A,"|",p!.B,"|",p!.C,"|",p!.Y,"|*)");
        Print(" => (",p!.Qp,"|*) ");
    else
        Print("(",StringWordStripped(p!.Pp),"|*) <= ");
        Print("(",StringWordStripped(p!.X),"|",
                  StringWordStripped(p!.A),"|",
                  StringWordStripped(p!.B),"|",
                  StringWordStripped(p!.C),"|",
                  StringWordStripped(p!.Y),"|*)");
        Print(" => (",StringWordStripped(p!.Qp),"|*) ");
    fi;
    if p!.whereeps = 'L' then
        Print(" left eps>");
    else
        Print(" right eps>");
    fi;
  end );

InstallMethod( FindCriticalPairs, "for a rewrite system",
  [ IsRewriteSystemStdRep ],
  function( rws )
    # This finds the initial list of so called critical pairs. That is, these
    # are two left hand sides with a non-trivial overlap, i.e. a word
    # ABC such that AB->P and BC->Q are rewrites. The pair is critical,
    # if there is no W with PC=>W and AQ=>W.
    # This function uses some heuristics to find a list of pairs which contains
    # all critical pairs.
    local A,B,C,L,P,Q,V,Vl,W,conflue,ht,i,j,k,l,l2,r,res,t,tab;
    res := [];
    ht := rws!.prefixhash;
    for i in [1..Length(rws!.lefts)] do
        L := rws!.lefts[i];
        l := Length(L);
        for j in [2..l] do
            A := L{[1..j-1]};
            B := L{[j..l]};
            P := rws!.rights[i];
            tab := HTValue(rws!.prefixhash,B);
            if tab <> fail then
                for k in tab[2] do   # this is the list of rewrites with this
                                     # prefix in its LHS
                    l2 := Length(rws!.lefts[k]);
                    C := rws!.lefts[k]{[Length(B)+1..l2]};
                    Q := rws!.rights[k];
                    V := Concatenation(P,C);
                    W := Concatenation(A,Q);
                    t := Check(rws,V,W);
                    if t <> fail then
                        Add(res,rec( A := A, B := B, C := C, P := P, Q := Q,
                                     Pp := t[2], Qp := t[3] ));
                    fi;
                od;
            fi;
        od;
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
  end );

InstallMethod( SearchDescendants, "for a search record and a CW pattern",
  [ IsRecord, IsCWPatternStdRep ],
  function( s, cw )
    # Uses Lemma 2.3 to extend the cyclic word patterns.
    # Adds descendants (again cyclic word patterns) to r.pats and 
    # a list of pairs of witnesses found to r.wits.
    local Extend,L,P,Pp,Q,Qp,X,Y,d,dd,i,j,l,post,pre,r,res,rws;

    Extend := function(s,cw,pre,post)

    end;

    rws := s.rws;
    if cw!.whereeps = 'L' then
        if Length(cw!.Pp) = 0 then
            # First try an empty V:
            r := Check(rws,CyclicWord(cw!.Pp),CyclicWord(cw!.Qp));
            if r <> fail and r[1] = true then
                Add(s.wits,[CyclicWord(cw!.Pp),CyclicWord(cw!.Qp)]);
            fi;
            # Now extend with all possible left hand sides:
            for L in rws!.lefts do
                l := Length(L);
                for i in [1..l-1] do
                    pre := L{[1..i]};
                    X := Concatenation(pre,cw!.X);
                    if IsIrreducible(rws,X) then
                        for j in [i+1..l] do
                            post := L{[j..l]};
                            Y := Concatenation(cw!.Y,post);
                            if Length(X)+Length(cw!.A)+Length(cw!.B)+
                               Length(cw!.C)+Length(Y) <= s!.lenlim and
                               IsIrreducible(rws,Y) then
                              Pp := Reduce(rws,Concatenation(pre,cw!.Pp,post));
                              Qp := Reduce(rws,Concatenation(pre,cw!.Qp,post));
                              Add(s.pats,
                                  CWPattern(rws,[X,cw!.A,cw!.B,cw!.C,Y],
                                            Pp,Qp,'L'));
                            fi;
                        od;
                    fi;
                od;
            od;
        else
            # This is the nonempty case
            # First find all double overlaps with left hand sides:
            d := FindLHSDoubleOverlaps(rws, cw!.Pp);
            for dd in d do
                P := CyclicWord(dd[1]);
                Q := CyclicWord(Concatenation(cw!.Qp,
                                     dd[1]{[Length(cw!.Pp)+1..Length(dd[1])]}));
                res := Check(rws,P,Q);
                if res <> fail and res[1] = true then
                    Add(s.wits,[P,Q]);
                fi;
            od;
            # Now find all left hand sides that have cw!.Pp as a substring:
            tab := HTValue(rws!.subhash,cw!.Pp);
            if tab <> fail then
                for i in [1,4..Length(tab)-2] do
                    # We extend X and Y:
                    lhs := tab[i];
                    L := rws!.lefts[lhs];
                    start := tab[i+1];
                    stop := tab[i+2];
                    X := Concatenation(L{[1..start-1]},cw!.X);
                    if IsIrreducible(rws,X) then
                        Y := Concatenation(Y,L{[stop+1..Length(L)]});
                        if IsIrreducible(rws,Y) then
                            

                od;
            fi;
        fi;
    else
        Info(InfoRWS,1,"not yet implemented");
    fi;
  end );

InstallMethod( CheckCyclicEpsilonConfluence, "for a rws and a pos integer",
  [ IsRewriteSystemStdRep, IsPosInt ],
  function( rws, n )
    local L,P,Q,critical,d,dd,i,oldpats,p,res,s,w;

    s := rec( rws := rws, lenlim := n, wits := [], pats := [], stop := false );

    Info( InfoRWS, 1, "Looking for double overlaps of LHSs...");
    for i in [1..Length(rws!.lefts)] do
        L := rws!.lefts[i];
        d := FindLHSDoubleOverlaps(rws, L);
        for dd in d do
            w := dd[1];
            P := CyclicWord(ApplyRewrite(rws,w,[i,1,Length(L)]));
            Q := CyclicWord(dd[4]);
            res := Check(rws,P,Q);
            if res <> fail and res[1] = true then
                Add(s.wits,[P,Q]);
            fi;
        od;
    od;
    Info( InfoRWS, 1, "Found ",Length(s.wits)," witnesses.");

    Info( InfoRWS, 1, "Finding critical pairs...");
    critical := FindCriticalPairs(rws);
    Info( InfoRWS, 1, "Found ", Length(critical), " critical pairs.");

    Info( InfoRWS, 1, "Setting up pattern list...");
    SetupSearchList(s,critical);

    while Length(s.pats) > 0 and not(s.stop) do
        Info( InfoRWS, 1, "Currently have ",Length(s.pats)," patterns and ",
              Length(s.wits)," witnesses.");
        oldpats := s.pats;
        s.pats := EmptyPlist(Length(s.pats));
        for p in oldpats do
            SearchDescendants(s,p);
        od;
    od;
    return s;
  end );

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
