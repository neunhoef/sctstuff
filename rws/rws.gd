##
##  Stuff to check epsilon-confluence of rewrite-systems
##  Copyright (C) 2012 by Max Neunhoeffer
##  This file is free software, see license information at the end.
##

# Words are just lists, either plain lists or strings
# So letters are either integers or characters

# Some utilities:

DeclareOperation("EmptyList", [IsInt, IsList]);
DeclareOperation("LexLeastRotation", [IsList]);
DeclareGlobalFunction("HashFunctionForStrings");

DeclareInfoClass("InfoRWS");
SetInfoLevel(InfoRWS,3);

SetAssertionLevel( 1 );

# Cyclic words:

BindGlobal("CyclicWordsFamily", NewFamily("CyclicWordsFamily"));
DeclareCategory("IsCyclicWord", IsPositionalObjectRep);
DeclareRepresentation("IsCyclicWordStdRep", IsCyclicWord, [1..3]);
BindGlobal("CyclicWordType", NewType(CyclicWordsFamily, IsCyclicWordStdRep));

DeclareOperation("CyclicWord",[IsList]);  # Constructor
DeclareAttribute("Length",IsCyclicWord);
DeclareAttribute("Word",IsCyclicWord);
DeclareOperation("StringWordStripped",[IsList]);


# Rewrite systems:

BindGlobal("RewriteSystemsFamily", NewFamily("RewriteSystemsFamily"));
DeclareCategory("IsRewriteSystem", IsComponentObjectRep);
DeclareRepresentation("IsRewriteSystemStdRep", IsRewriteSystem, 
       [ "alphabet", "rewrites", "prefixhash", "fsa"] );
BindGlobal("RewriteSystemType", 
           NewType(RewriteSystemsFamily, IsRewriteSystemStdRep));

BindGlobal("FSAStatesFamily", NewFamily("FSAStatesFamily"));
DeclareCategory("IsFSAState", IsComponentObjectRep);
DeclareRepresentation("IsFSAStateStdRep", IsFSAState, 
       [ "prefix", "complete", "hashels", "hashvals"]);
BindGlobal("FSAStateType", NewType(FSAStatesFamily, IsFSAStateStdRep));

DeclareOperation( "RewriteSystem", [IsList, IsList] );
DeclareOperation( "RewriteSystem", [IsList, IsList, IsRecord] );
# Takes an alphabet and a zipped list of pairs of words
# The record is an options record, options (with defaults given):
#   check := true            do a check whether any LHS is contained
#                            in any left or right hand side

DeclareOperation( "FSAState", [IsList, IsList, IsInt] );
# Takes a prefix and an integer, if this is 0, it is incomplete,
# if it is a positive integer, it is the number of a rewrite that
# applies. The hash is cleaned.

DeclareOperation( "LookupStep", [IsFSAState, IsObject]);
# This looks up one step in the FSA and returns another state.

DeclareOperation( "LinkFSAStates", [IsFSAState, IsObject, IsFSAState] );
# This links two nodes.

DeclareOperation( "FoundRewrite", [IsFSAState]);
# This checks whether or not a rewrite applies.

DeclareOperation( "FindOneRewrite", [IsRewriteSystem, IsList]);
DeclareOperation( "FindOneRewrite", [IsRewriteSystem, IsCyclicWord]);
# Returns fail or a pair [REWRITENR, START, END]

DeclareOperation( "FindAllRewrites", [IsRewriteSystem, IsList]);
DeclareOperation( "FindAllRewrites", [IsRewriteSystem, IsCyclicWord]);
# Returns a (possibly empty) list of pairs [REWRITENR, START, END]

DeclareOperation( "ApplyRewrite", [IsRewriteSystem, IsList, IsList] );
DeclareOperation( "ApplyRewrite", [IsRewriteSystem, IsCyclicWord, IsList] );
# Takes a RWS, a word and a pair describing the rewrite and position as above

DeclareOperation( "IsIrreducible", [IsRewriteSystem, IsList]);
DeclareOperation( "IsIrreducible", [IsRewriteSystem, IsCyclicWord]);

DeclareOperation( "ShowRewrite", [IsRewriteSystem, IsList, IsList] );
DeclareOperation( "ShowRewrite", [IsRewriteSystem, IsCyclicWord, IsList] );
DeclareOperation( "ShowRewrite", [IsRewriteSystem, IsList, IsBool] );
DeclareOperation( "ShowRewrite", [IsRewriteSystem, IsCyclicWord, IsBool] );

DeclareOperation( "Reduce", [IsRewriteSystem, IsList]);
DeclareOperation( "Reduce", [IsRewriteSystem, IsCyclicWord]);

# Here comes the implementation of our algorithm proper:

DeclareOperation( "FindLHSDoubleOverlaps", [IsRewriteSystem, IsList]);

DeclareOperation( "FindCriticalPairs", [IsRewriteSystem]);
# This finds the initial list of so called critical pairs. That is, these
# are two left hand sides with a non-trivial overlap, i.e. a word
# ABC such that AB->P and BC->Q are rewrites. The pair is critical,
# if there is no W with PC=>W and AQ=>W.
# This function uses some heuristics to find a list of pairs which contains
# all critical pairs.

DeclareOperation( "SetupSearchList", [IsRecord, IsList]);
# Sets up the main search list by taking the critical pairs in the second
# argument (coming from FindCriticalPairs) and setting up the data structures
# for the patterns.

BindGlobal("CWPatternsFamily", NewFamily("CWPatternsFamily"));
DeclareCategory("IsCWPattern", IsComponentObjectRep);
DeclareRepresentation("IsCWPatternStdRep", IsCWPattern, []);
BindGlobal("CWPatternType", NewType(CWPatternsFamily, IsCWPatternStdRep));

# The constructors:
DeclareOperation("CWPattern", [IsRewriteSystem, IsList, IsList, IsList,IsChar]);

DeclareOperation( "Check", [IsRewriteSystem, IsCyclicWord, IsCyclicWord]);
DeclareOperation( "Check", [IsRewriteSystem, IsList, IsList]);
# See whether or not we have found a pair of witnesses
# This function simply rewrites both (cyclic) words until they
# are irreducible. If one of them ends in the empty (cyclic) word and the
# other not, then the pair is a witness and [true,Vp,Wp] is returned,
# where Vp and Wp are the two irreducible (cyclic) words.
# Otherwise [false,Vp,Wp] is returned. If some (cyclic) word is found
# to which both rewrite (for example, if the (cyclic) words are
# equal), then fail is returned.

DeclareOperation( "SearchDescendants", [IsRecord, IsCWPattern]);
# Uses Lemma 2.3 to extend the cyclic word patterns.
# Adds descendants (again cyclic word patterns) to r.pats and 
# a list of pairs of witnesses found to r.wits.

DeclareOperation( "CheckCyclicEpsilonConfluence", [IsRewriteSystem, IsPosInt]);
# The whole search procedure. It creates a record for the search, this
# contains among other things the rewrite system.

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
