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
    if IsEmpty(l) then return ShallowCopy(l); fi;
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
    local o,len,ll;
    len := Length(l);
    ll := LexLeastRotation(l);
    o := [ll[1],EmptyList(2*len,ll),len];
    Append(o[2],ll[1]);
    Append(o[2],ll[1]);
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
  function( alphabet, rewrites )
    local L,hashlen,hf,ht,i,j,len,maxlen,pre,rws,s,states,tab,w,x;

    len := Length(rewrites);
    if IsOddInt(len) then
        Error("rewrites must be a list of even length");
        return fail;
    fi;
    rws := rec( alphabet := alphabet, lefts := rewrites{[1,3..len-1]},
                rights := rewrites{[2,4..len]},
                prefixhash := fail, fsa := fail, states := fail );
    Objectify(RewriteSystemType, rws);
    # Compute prefix hash and make states for prefixes
    rws!.fsa := FSAState(alphabet,EmptyList(0,alphabet),0);
    states := [];
    Add(states,rws!.fsa);
    rws!.states := states;
    maxlen := Maximum(List(rws!.lefts,Length));
    hashlen := NextPrimeInt(QuoInt(maxlen * len * 3,2));
    len := len / 2;
    if IsPlistRep(alphabet) then
        hf := MakeHashFunctionForPlainFlatList(hashlen);
        ht := HTCreate(alphabet,rec( hf := hf.func, hfd := hf.data,
                                     hashlen := hashlen ));
    else
        ht := HTCreate(alphabet,rec( hashlen := hashlen ));
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
    od;

    # Complete automaton:
    rws!.prefixhash := ht;
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
    local pos;
    if IsInt(x) then
        pos := x mod s!.alphsize + 1;
    elif IsChar(x) then
        pos := IntChar(x) mod s!.alphsize + 1;
    fi;
    while true do
        if not(IsBound(s!.hashels[pos])) then return fail; fi;
        if x = s!.hashels[pos] then return s!.hashvals[pos]; fi;
        pos := pos + 1;
        if pos > s!.alphsize then pos := 1; fi;
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
    for i in [1..Length(w)] do
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
    i := 1;
    res := [];
    while i <= Length(w) do
        s := LookupStep(s,w[i]);
        rw := FoundRewrite(s);
        if rw > 0 then
            Add(res,[rw,i-Length(s!.prefix)+1,i]);
            i := i-Length(s!.prefix)+2;
            s := rws!.fsa;
        else
            i := i + 1;
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
    r := FindOneRewrite(rws,w);
    return r = fail;
  end );

InstallMethod( FindOneRewrite, "for a RWS and a cyclic word",
  [ IsRewriteSystemStdRep, IsCyclicWordStdRep ],
  function( rws, w )
    # FIXME: Go on here!
    local i,rw,s;
    s := rws!.fsa;
    for i in [1..Length(w)] do
        s := LookupStep(s,w[i]);
        rw := FoundRewrite(s);
        if rw > 0 then
            return [rw,i-Length(s!.prefix)+1,i];
        fi;
    od;
    return fail;
  end );

InstallMethod( FindAllRewrites, "for a RWS and a word",
  [ IsRewriteSystemStdRep, IsCyclicWordStdRep ],
  function( rws, w )
    local i,res,rw,s;
    s := rws!.fsa;
    i := 1;
    res := [];
    while i <= Length(w) do
        s := LookupStep(s,w[i]);
        rw := FoundRewrite(s);
        if rw > 0 then
            Add(res,[rw,i-Length(s!.prefix)+1,i]);
            i := i-Length(s!.prefix)+2;
            s := rws!.fsa;
        else
            i := i + 1;
        fi;
    od;
    return res;
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
