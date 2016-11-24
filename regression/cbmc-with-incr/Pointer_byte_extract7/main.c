struct S
{
  int i;
  int j;
  int l;
};

struct BF
{
  int i;
  unsigned x:1;
};

int main()
{
  struct S s;
  s.i=0;
  s.j=0;
  s.l=0;

  struct BF* ptr=(struct BF*)((char*)&s+1);
  struct BF bf=*ptr;
  __CPROVER_assert(bf.i==0, "");

  return 0;
}

