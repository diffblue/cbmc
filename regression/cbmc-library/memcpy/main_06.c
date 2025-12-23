// #include <string.h> is intentionally missing

struct c
{
};

int d()
{
  struct c e;
  memcpy(e);
}
int main()
{
  int (*h)() = d;
  h();
}
