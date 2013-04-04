names := ["s","e","t","b","r","l","il","ir","ol","or","1"];
t := List([1..11],i->0*[1..11]);
rules := [
  "s*t=s",
  "t*s=s",
  "t*t=t",
  "t*l=l",
  "e*b=e",
  "b*e=e",
  "b*b=b",
  "b*r=r",
  "r*t=r",
  "r*l=e",
  "l*b=l",
  "l*r=s",
  # so far this was K6
  "il*ol=1",
  "ol*il=1",
  "ir*or=1",
  "or*ir=1",
  "ir*l=b",
  "l*ir=t",
  "il*r=t",
  "r*il=b",
  "ir*s=r",
  "s*il=l",
  "e*ir=r",
  "il*e=l",
  "s*l=or",
  "s*e=or",
  "l*e=or",
  "e*r=ol",
  "r*s=ol",
  "or*b=or",
  "ol*t=ol",
  "t*or=or",
  "b*ol=ol",
  "t*e=e",
  "s*b=s",
  "t*ol=ol",
  ];
for r in rules do
  x := SplitString(r,"*=");
  t[Position(names,x[1])][Position(names,x[2])] := Position(names,x[3]);
od;

for i in [1..11] do
  for j in [1..11] do
    for k in [1..11] do
      if t[i][j] <> 0 then
          if t[j][k] <> 0 then
              if t[t[i][j]][k] <> t[i][t[j][k]] then 
                  Print("1: ",names[i],"*",names[j],"*",names[k],"\n");
              fi;
          else
              if t[t[i][j]][k] <> 0 then
                  Print("2: ",names[i],"*",names[j],"*",names[k],"\n");
              fi;
          fi;
      else
          if t[j][k] <> 0 then
              if 0 <> t[i][t[j][k]] then
                  Print("3: ",names[i],"*",names[j],"*",names[k],"\n");
              fi;
          fi;
      fi;
    od;
  od;
od;

Print("  |");
for j in [1..11] do
    Print(String(names[j],2),"|");
od;
Print("\n");
for i in [1..11] do
  Print(String(names[i],2),"|");
  for j in [1..11] do
    if t[i][j] = 0 then 
        Print(" 0|");
    else
        Print(String(names[t[i][j]],2),"|");
    fi;
  od;
  Print("\n");
od;

# Is not associative, can it be fixed?
