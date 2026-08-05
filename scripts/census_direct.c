/* INDEPENDENT direct enumeration over PITCH words.
   Class labelling by rotation-canonical cyclic GAP WORD (not by the
   canonical-rotation-of-pitch-set method used originally).
   No choice functions, no Eulerian circuits anywhere. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n,m;
static int lab[64][64][64];   /* class index 0..m-1, or -1 */
static long long cntS,cntZ;
static int seq[40];
static unsigned long long used;

static int gapclass(int a,int b,int c){
  if(a==b||b==c||a==c) return -1;
  int x[3]={a,b,c};
  for(int i=0;i<2;i++)for(int j=0;j<2-i;j++) if(x[j]>x[j+1]){int t=x[j];x[j]=x[j+1];x[j+1]=t;}
  int g[3]={(x[1]-x[0]+n)%n,(x[2]-x[1]+n)%n,(x[0]-x[2]+n)%n};
  /* rotation-canonical gap word */
  int best[3]={g[0],g[1],g[2]};
  for(int r=1;r<3;r++){
    int c0=g[r],c1=g[(r+1)%3],c2=g[(r+2)%3];
    if(c0<best[0]||(c0==best[0]&&(c1<best[1]||(c1==best[1]&&c2<best[2])))){best[0]=c0;best[1]=c1;best[2]=c2;}
  }
  /* match against {0,1,k} */
  for(int k=2;k<=n-2;k++){
    int y[3]={0,1,k};
    int h[3]={(y[1]-y[0]+n)%n,(y[2]-y[1]+n)%n,(y[0]-y[2]+n)%n};
    int bb[3]={h[0],h[1],h[2]};
    for(int r=1;r<3;r++){
      int c0=h[r],c1=h[(r+1)%3],c2=h[(r+2)%3];
      if(c0<bb[0]||(c0==bb[0]&&(c1<bb[1]||(c1==bb[1]&&c2<bb[2])))){bb[0]=c0;bb[1]=c1;bb[2]=c2;}
    }
    if(bb[0]==best[0]&&bb[1]==best[1]&&bb[2]==best[2]) return k-2;
  }
  return -1;
}
static int isZig(void){
  for(int i=0;i<m;i++){
    int a=seq[i],b=seq[(i+1)%m],c=seq[(i+2)%m];
    if(lab[a][b][c]==0){
      int d1=(b-a+n)%n,d2=(c-b+n)%n;
      return !(d1==d2&&(d1==1||d1==n-1));
    }
  }
  return 0;
}
static void rec(int i){
  if(i==m){
    int k1=lab[seq[m-2]][seq[m-1]][seq[0]];
    if(k1<0||(used>>k1&1))return;
    unsigned long long u=used|(1ULL<<k1);
    int k2=lab[seq[m-1]][seq[0]][seq[1]];
    if(k2<0||(u>>k2&1))return;
    if((u|(1ULL<<k2))!=((1ULL<<m)-1))return;
    used=u|(1ULL<<k2);
    if(isZig())cntZ++;else cntS++;
    used^=(1ULL<<k1)|(1ULL<<k2);
    return;
  }
  int a=seq[i-2],b=seq[i-1];
  for(int c=0;c<n;c++){
    int k=lab[a][b][c];
    if(k<0||(used>>k&1))continue;
    seq[i]=c; used|=1ULL<<k;
    rec(i+1);
    used&=~(1ULL<<k);
  }
}
int main(int argc,char**argv){
  n=atoi(argv[1]); m=n-3;
  for(int a=0;a<n;a++)for(int b=0;b<n;b++)for(int c=0;c<n;c++) lab[a][b][c]=gapclass(a,b,c);
  seq[0]=0; used=0;
  for(int b=0;b<n;b++){ seq[1]=b; rec(2); }
  printf("n=%2d  scalar=%lld  zigzag=%lld  total=%lld\n",n,cntS,cntZ,cntS+cntZ);
  return 0;
}
