int f1(void);
int f2(void);
int f3(void);
int f4(void);

int (* const fptbl1[][2])(void) = {
  { f1, f2 },
  { f3, f4 },
};

int g1(void);
int g2(void);

int (* const fptbl2[])(void) = {
  g1, g2
};

int func(int id1, int id2)
{
  int t;
  t = fptbl1[id1][id2]();
  t = fptbl2[id1]();
  return t;
}
