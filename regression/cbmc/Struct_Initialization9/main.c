typedef unsigned char u8;
typedef _Bool BOOLEAN;

struct rt_ch_desp {
 u8 FirstChannel;
 u8 NumOfCh;
 char MaxTxPwr;
 u8 Geography;
 BOOLEAN DfsReq;
};

struct rt_ch_region {
 u8 CountReg[3];
 u8 DfsType;
 struct rt_ch_desp ChDesp[10];
};

struct rt_ch_region ChRegion[] = {
 { "AG",
   0,
   { {1, 13, 20, 2, 0},
     {36, 4, 23, 2, 0},
     {52, 4, 23, 2, 0},
     {100, 11, 30, 2, 0},
     {0},
   }
 },
 { "AR",
   0,
   { {1, 13, 20, 2, 0},
     {52, 4, 24, 2, 0},
     {149, 4, 30, 2, 0},
     {0},
   }
 }
};

struct S {
  int f1, f2;
  union U {
    struct Tq { int xq, yq; } q;
    struct Tp { int xp, yp; } p;
  } my_u;
};

struct S s = {
  .f1=1, .f2=2,
  .my_u = { .p= { .xp=10, .yp=20 } }
};

int main()
{
}
