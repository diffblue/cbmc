union empty {
};

struct S
{
  int x;
  union empty e;
  int y;
};

struct S s = {1};

int main()
{
  assert(s.x == 1 && s.y == 0);
}
