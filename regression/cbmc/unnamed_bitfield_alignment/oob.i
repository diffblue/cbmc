// From #9304: struct A has size 2 on x86-64 Linux, so a has size 6, and the
// write to b[7] is out of bounds.
struct A
{
  char c;
  int : 4;
};

struct A a[3];

int main(void)
{
  char *b = (char *)a;
  b[7] = 1;
  return 0;
}
