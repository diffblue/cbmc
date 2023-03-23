int foo(void)
{
}

const int (*const fptrs[])(void) = {&foo};

void unused()
{
  const int (*const fp)(void) = fptrs[0];
  (*fp)();
}

int main()
{
}
