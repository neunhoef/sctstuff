#######################################################
#                                                     #
#  LINEAR PROGRAMING IN GAP USING LRS                 #
#                                                     #
#  Author:  Gabor P. Nagy                             #
#  WWW1:    http://www.math.u-szeged.hu/~nagyg        #
#  WWW2:    http://nagygp.googlepages.com/gaborsgap6  #
#  Date:    Dec 7, 2007                               #
#  Licence: GPL 2                                     #
#                                                     #
#######################################################

#################################################################
# 
# The functions 
# 
# lp_max( A, rhs, obj )
# lp_min( A, rhs, obj )
# 
# return the solutions of the linear program 
# 
# A*x >= rhs
# obj*x -> max/min,
# 
# where <A> is a rational matrix with n rows and m columns, 
# <rhs> is a (column) vector of dimension n and <obj> is
# a (row) vector of dimension m. 
# 
# If the problem has a solution then the function returns 
# the pair [ x, val ], where <x> is the vector of dimension m 
# which realizes the optimum value <val>. 
# 
# If the problem is not feasible or not bounded then the 
# function returns fail and gives an info warning 
# "No feasible solution" or "Unbounded solution", respectively. 
# 
# See http://nagygp.googlepages.com/gaborsgap6 for more details. 
#
#################################################################


#################################################################
#
# This short GAP program is actually an interface to the software
# lrs by David Avis (http://cgm.cs.mcgill.ca/~avis/C/lrs.html). 
# In order to use this program, you need the executables glrs and 
# egrep. 
#
# If glrs is not in your path then put here the full file name. 
# You can use lrs without GNU MP (hence no arbitrary precision 
# rational arithmetics) by replacing this variable by "lrs".
#
LRS_EXE:="glrs";
#
#
#################################################################

#################################################################
#
# lpsolve_glrsNC( A, rhs, obj )
#
# LP: A*x>=rhs, obj*x -> max
#
# Non checking!!!
#
lpsolve_glrsNC:=function(A,rhs,obj)
	local 	tmpdir, prob_file,solv_file,out,
		i,j,x,ret;
	# preparing problem and solution files
	tmpdir:=DirectoryTemporary();
	prob_file:=Filename( tmpdir, "gaplp.ine");
	solv_file:=Filename( tmpdir, "gaplp.sol" );
	out:=OutputTextFile(prob_file,false);
	SetPrintFormattingStatus(out,false);
	# writing down the problem
	AppendTo(out, "Temporary\n", "* Created by GAP\n" );
	AppendTo(out, "H-representation\n", "begin\n" );
	AppendTo(out, Size(A), " ", Size(A[1])+1, " rational\n" );
	for i in [1..Size(A)] do 
		AppendTo(out, -rhs[i]);
		for j in [1..Size(A[1])] do
			AppendTo(out, " ", A[i][j]);
		od;
		AppendTo(out, "\n");
	od;
	AppendTo(out, "end\n" );
	AppendTo(out, "lponly\n" );
	AppendTo(out, "maximize 0" );
	for x in obj do AppendTo(out, " ", x); od;
	AppendTo(out, "\n");
	CloseStream(out);
	# solving the problem 	
	Exec( Concatenation( 
		LRS_EXE, " ", prob_file, 
		" | egrep \"^No feasible|^*Unbounded|^*Primal\" > ",
		solv_file ) );
	# reading in the solution
	out:=InputTextFile( solv_file );
	ret:=ReadAll(out);
	CloseStream(out);
	# deleting the files
	Exec( Concatenation( "rm ", prob_file ) );
	Exec( Concatenation( "rm ", solv_file ) );
	# interpreting and returning the solution
	if ret{[1..3]}="No " then 
		Info( InfoWarning, 1, "No feasible solution" );
		return fail;
	elif ret{[1..3]}="*Un" then 
		Info( InfoWarning, 1, "Unbounded solution" );
		return fail;
	else 
		ret:=ret{[10..Size(ret)-2]};
		ret:=SplitString(ReplacedString(ret,"= ","=")," ");
		ret:=List(ret,x->EvalString(SplitString(x,"=")[2]));
		return [ret,obj*ret];
	fi;
end;
#
#################################################################


#################################################################
#
# lp_inputcheck( A, rhs, obj )
#
lp_inputcheck:=function( A, rhs, obj )
	local nrows,ncols;
	if IsList(rhs) and ForAll(rhs,IsRat) then
		nrows:=Size(rhs);
	else 
		Info( InfoWarning, 1, "Wrong right hand side in LP input" );
		return false;
	fi;
	if IsList(obj) and ForAll(obj,IsRat) then
		ncols:=Size(obj);
	else 
		Info( InfoWarning, 1, "Wrong objective in LP input" );
		return false;
	fi;
	if IsMatrix(A) and ForAll(Concatenation(A),IsRat) then
		if Size(A)=nrows and Size(A[1])=ncols then
			return true;
		else
			Info( InfoWarning, 1, "Wrong dimensions in LP input" );
			return false;
		fi;
	else
		Info( InfoWarning, 1, "Wrong matrix in LP input" );
		return false;
	fi;
end;
#
#################################################################


#################################################################
#
# lp_max( A, rhs, obj )
#
lp_max:=function( A, rhs, obj )
	if lp_inputcheck(A,rhs,obj) then 
		return lpsolve_glrsNC(A,rhs,obj);
	else
		return fail;
	fi;
end;
#
#################################################################

#################################################################
#
# lp_min( A, rhs, obj )
#
lp_min:=function( A, rhs, obj )
	local ret;
	if lp_inputcheck(A,rhs,obj) then 
		ret:=lpsolve_glrsNC(A,rhs,-obj);
		return [ret[1],-ret[2]];
	else
		return fail;
	fi;
end;
#
#################################################################

#################################################################
#
# lp_export_freemps( A, rhs, obj, filename )
#
# This function exports the linear program
#
# A*x >= rhs
# obj*x -> max/min,
#
# to the free MPS format for LP problem data. This format is used
# by several more sophisticated LP solvers, for example the GNU 
# Linear Programming Kit (GLPK, http://www.gnu.org/software/glpk/).
# See the documentation refman.pdf for detailed description of this
# format. Moreover, GLPK can be used to convert to problem data in 
# several other formats. 
#
lp_export_freemps:=function(A,rhs,obj,filename)
	local nrows,ncols,n_nonzeros,out,i,j;
	if not lp_inputcheck(A,rhs,obj) then 
	       return fail;
	fi;
	nrows:=Size(A);
	ncols:=Size(A[1]);
	n_nonzeros:=Number(Flat(A),x->x<>0);
	# HEADER
	out:=OutputTextFile(filename,false);
	SetPrintFormattingStatus(out,false);
	AppendTo(out, "* Problem: Generated by GAP\n" );
	AppendTo(out, "* Class: LP\n" );
	AppendTo(out, "* Rows: ", nrows, "\n" );
	AppendTo(out, "* Columns: ", ncols, "\n" );
	AppendTo(out, "* Non-zeros: ", n_nonzeros, "\n" );
	AppendTo(out, "* Format: Free MPS\n", "*\nNAME\n" );
	# ROWS
	AppendTo(out, "ROWS\n N  R0\n" );
	for i in [1..nrows] do
		AppendTo(out, " G  R", i, "\n");
	od;
	# COLUMNS
	AppendTo(out, "COLUMNS\n" );
	for i in [1..ncols] do
		AppendTo(out, " C", i, " R0 ", obj[i], "\n");
		for j in [1..nrows] do
			AppendTo(out, " C", i, " R", j, " ", A[j][i], "\n");
		od;
	od;
	# RIGHT HAND SIDE
	AppendTo(out, "RHS\n");
	for i in [1..nrows] do
		AppendTo(out, " RHS1 R", i, " ", rhs[i], "\n");
	od;
	# BOUNDS (making the variables free)
	AppendTo(out, "BOUNDS\n");
	for i in [1..ncols] do 
		AppendTo(out, " FR BND1 C", i, "\n");
	od;
	# closing the file
	AppendTo(out, "ENDATA\n");
	CloseStream(out);
	return 0;
end;
#################################################################

