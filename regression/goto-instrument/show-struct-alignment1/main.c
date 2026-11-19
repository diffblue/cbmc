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
int main()
{
  struct narrow n;
  struct wide w;
  n.a = 1;
  w.x = 2;
  return n.a + w.x;
}
