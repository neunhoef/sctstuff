/* presneck.c - presentation to necklace format.  */

#include <stdio.h>
#include <stdlib.h>

int porder;
int pacc;
int p[100][100];
int lets;
int cp[100];

int nrels;
int relprim[200];
int relpow[200];
int relstart[200];
int relc[200];
int pos;
int rpg[10000];
int rlt[10000];
int cpos;
int cpg[1000000];
int clt[1000000];

int nty;
int ntrel[900];
int ntcak[900];
int ntstart[900];

/* buffer for cancellation. pg[0],lt[0],pg[1]...lt[len-1]  */
int pg[1000000];   // pongo elements in buffer
int lt[1000000];   // letters in buffer


int canc(int len)
{
    int dun,im,i,ip,pg1,j;
    int clen;
    clen=len;
    dun=0;
    while(dun==0)
    {
        if(clen<=1) return clen;
        dun=1;
        for(i=0;i<clen;i++)
        {
            if(pg[i]>pacc) continue;
            im=i-1;
            if(im<0) im=clen-1;
            if(cp[lt[i]]!=lt[im]) continue;
            if(clen==2)
            {
                if(pg[im]>pacc) return 2;
                return 0;
            }
            ip=i+1;
            if(ip==clen) ip=0;
            pg1=p[pg[im]][pg[ip]];
            if(pg1==0) continue;
            pg[im]=pg1;
            lt[im]=lt[ip];
            if(ip==0)
            {
                for(j=1;j<clen-1;j++)
                {
                    lt[j-1]=lt[j];
                    pg[j-1]=pg[j];
                }
            }
            else
            {
                for(j=ip+1;j<clen;j++)
                {
                    lt[j-2]=lt[j];
                    pg[j-2]=pg[j];
                }
            }
            clen-=2;
            dun=0;
            break;
        }
    }
}

int main(int argc, char ** argv)
{
    FILE *f1, *f2;
    int r,i,j,rel,rs,circle,maxlen,cak1,cak2;
    int pass,nt1,nt2,rel1,rel2,len,len1,len2;
    int ck1,ck2,pong1,pong2,edges;
    int x1,x2,x3,x4,x5,x6,y1,y2,y6;
    if(argc!=3)
    {
        printf("presneck <PresentationFile> <NecklaceFile>\n");
        return 1;
    }
    f1=fopen(argv[1],"rb");
    if(f1==NULL)
    {
        printf("Cannot open input presentation file %s\n",argv[1]);
        return 2;
    }
    f2=fopen(argv[2],"wb");
    if(f1==NULL)
    {
        printf("Cannot open output necklace file %s\n",argv[2]);
        return 3;
    }
/* presentation file is . . . */
/*  <order>   <accepting>   (always 1...pacc)  */
/* Cayley table of pongo  */
/*  <number of letters>    */
/*  inverse table of letters */
/*  number of relators  */
/*  relprim relpow     */
/* relpg[relprim]      */
/* rellt[relprim]      */
    r=fscanf(f1,"%d",&porder);
    printf("Pongo order is %d\n",porder);
    r=fscanf(f1,"%d",&pacc);
    printf("%d accepting element(s)\n",pacc);
    for(i=1;i<=porder;i++)
        for(j=1;j<=porder;j++)
           r=fscanf(f1,"%d",&p[i][j]);
    r=fscanf(f1,"%d",&lets);
    printf("Number of letters = %d\n",lets);
    for(i=1;i<=lets;i++)
        r=fscanf(f1,"%d",&cp[i]);
    r=fscanf(f1,"%d",&nrels);
    printf("Number of relators = %d\n",nrels);
    pos=0;
    for(rel=0;rel<nrels;rel++)
    {
        r=fscanf(f1,"%d",&relprim[rel]);
        r=fscanf(f1,"%d",&relpow[rel]);
        relstart[rel]=pos;
        for(i=0;i<relprim[rel];i++)
        {
            r=fscanf(f1,"%d",&rpg[pos++]);
        }
        pos=relstart[rel];
        for(i=0;i<relprim[rel];i++)
        {
            r=fscanf(f1,"%d",&rlt[pos++]);
        }
    }
/* bake the cake  */
    cpos=0;
    for(rel=0;rel<nrels;rel++)
    {
        relc[rel]=cpos;
        rs=relstart[rel];
        for(i=0;i<relpow[rel]+1;i++)
        {
            for(j=0;j<relprim[rel];j++)
            {
                cpg[cpos]=rpg[rs+j];
                clt[cpos++]=rlt[rs+j];
            }
        }
    }
    for(i=0;i<cpos;i++) printf(" %d",cpg[i]);
    printf("\n");
    for(i=0;i<cpos;i++) printf(" %d",clt[i]);
    printf("\n");
/* list the notch types  */
    nty=0;
    for(rel=0;rel<nrels;rel++)
    {
        for(i=0;i<relprim[rel];i++)
        {
            ntrel[nty]=rel;
            ntcak[nty]=relc[rel]+i;
            ntstart[nty]=i;
            nty++;
        }
    }
    printf("%d notch-types\n",nty);
/* calculate circle  */
    circle=60;
    for(rel=0;rel<nrels;rel++)
    {
        i=2*relprim[rel]*relpow[rel];
        j=circle;
        while((circle%i)!=0) 
        {
            circle+=j;
            if(circle>100000000)
            {
                printf("Circle value %d too great\n",circle);
                return 4;
            }
        }
    }
    printf("Circle is %d\n",circle);
    edges=0;
    for(pass=0;pass<2;pass++)
    {
        if(pass==1)
        {
            fprintf(f2," %d \n",circle);
            fprintf(f2," %d %d \n",porder,pacc);
            for(i=1;i<=porder;i++)
            {
                for(j=1;j<=porder;j++) fprintf(f2," %d",p[i][j]);
                fprintf(f2,"\n");
            }
            fprintf(f2," %d \n",nrels);
            for(i=0;i<nrels;i++) 
                fprintf(f2," %d %d urg%d\n",relprim[i],relpow[i],i);
            fprintf(f2," %d \n",edges);
        }
        edges=0;
        for(nt1=0;nt1<nty;nt1++)
        {
            rel1=ntrel[nt1];
            len1=relprim[rel1]*relpow[rel1];
            ck1=ntcak[nt1];
            for(nt2=nt1;nt2<nty;nt2++)
            {
                rel2=ntrel[nt2];
                len2=relprim[rel2]*relpow[rel2];
                ck2=ntcak[nt2];
                maxlen=len1;
                if(len2<maxlen)maxlen=len2;
                for(len=1;len<maxlen;len++)
                {
/* first check that the two half-edges are complementary  */
                    pong1=p[cpg[ck1]][cpg[ck2+len]];
                    if(pong1==0) continue;
                    pong2=p[cpg[ck2]][cpg[ck1+len]];
                    if(pong2==0) continue;
                    for(i=0;i<len;i++)
                    {
                        pg[i]=cpg[ck1+i];
                        lt[i]=clt[ck1+i];
                        pg[i+len]=cpg[ck2+i];
                        lt[i+len]=clt[ck2+i];
                    }
                    pg[0]=1;
                    pg[len]=1;
                    i=canc(2*len);
                    if(i!=0) continue;
                    for(i=0;i<len1-len;i++)
                    {
                        pg[i]=cpg[ck1+i+len];
                        lt[i]=clt[ck1+i+len];
                    }
                    for(i=0;i<len2-len;i++)
                    {
                        pg[i+len1-len]=cpg[ck2+i+len];
                        lt[i+len1-len]=clt[ck2+i+len];
                    }
                    pg[0]=pong1;
                    pg[len1-len]=pong2;
                    i=canc(len1+len2-2*len);
                    if(i==0) continue;
                    if(pass==0)
                    {
                        edges++;
                        if(nt1!=nt2) edges++; 
                        continue;
                    }
                    x1=ntrel[nt1];
                    y1=ntrel[nt2];
                    x2=ntstart[nt1];
                    y2=ntstart[nt2];
                    x3=len;
                    x4=edges+1;
                    x5=circle/(relprim[x1]*relpow[x1]) +
                       circle/(relprim[y1]*relpow[y1]);
                    x5=(x5*len - circle)/2;
                    x6=cpg[ck1];
                    y6=cpg[ck2];
                    if(nt1==nt2)
                    {
                        fprintf(f2," %d %d %d %d %d %d \n",x1+1,x2,x3,x4,x5,x6);
                        edges++;
                    }
                    else
                    {
                        fprintf(f2," %d %d %d %d %d %d \n",x1+1,x2,x3,x4+1,x5,x6);
                        fprintf(f2," %d %d %d %d %d %d \n",y1+1,y2,x3,x4,x5,y6);
                        edges+=2;
                    }
                }
            }
        }
    }
    return 0;
}

/* end of presneck.c  */
