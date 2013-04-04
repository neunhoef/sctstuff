names := ["s","e","t","b","r","l","el","er"];
t := List([1..8],i->0*[1..8]);
rules := [
  "s*t=s",
  "s*e=el",
  "t*s=s",
  "t*t=t",
  "t*b=er",
  "t*l=l",
  "t*er=er",
  "e*s=er",
  "e*b=e",
  "b*t=el",
  "b*e=e",
  "b*b=b",
  "b*r=r",
  "b*el=el",
  "r*t=r",
  "r*l=e",
  "r*el=b",
  "l*b=l",
  "l*r=s",
  "l*er=t",
  "el*t=el",
  "el*r=t",
  "el*el=el",
  "er*b=er",
  "er*l=b",
  "er*er=er"];
for r in rules do
  x := SplitString(r,"*=");
  t[Position(names,x[1])][Position(names,x[2])] := Position(names,x[3]);
od;

for i in [1..8] do
  for j in [1..8] do
    for k in [1..8] do
      if t[i][j] <> 0 then
          if t[j][k] <> 0 then
              if t[t[i][j]][k] <> t[i][t[j][k]] then Error(1); fi;
          else
              if t[t[i][j]][k] <> 0 then Error(2); fi;
          fi;
      else
          if t[j][k] <> 0 then
              if 0 <> t[i][t[j][k]] then Error(3); fi;
          fi;
      fi;
    od;
  od;
od;
          
