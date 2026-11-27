struct narrow
{
  char a;
  char b;
};
struct wide
{
  int x;
  int y;
};
struct pad
{
  char c;
  short s;
};
struct groups
{
  char g1;
  char g2;
  char g3;
  char g4;
  int i1;
  char h1;
  char h2;
  char h3;
  int i2;
};
struct tail
{
  char t1;
  char t2;
  char t3;
};
int main()
{
  struct narrow n;
  struct wide w;
  struct pad p;
  struct groups g;
  struct tail t;
  n.a = 1;
  w.x = 2;
  p.c = 3;
  g.g1 = 4;
  t.t1 = 5;
  return n.a + w.x + p.c + g.g1 + t.t1;
}
