// this is permitted - __noop yields a compile-time constant 0
int array[__noop() + 1];

struct S
{
  int x;
};

int main(int argc, char *argv)
{
  struct S s;
  // the arguments to __noop are type checked, and thus the following is not
  // permitted
  __noop((char *)s);
}
