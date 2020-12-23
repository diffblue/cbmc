int main(int argc, char *argv)
{
  int x = 0;
  __noop(++x);
  __CPROVER_assert(x == 0, "__noop ignores side effects");
}
