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
int main()
{
  struct narrow n;
  struct wide w;
  struct pad p;
  n.a = 1;
  w.x = 2;
  p.c = 3;
  return n.a + w.x + p.c;
}
