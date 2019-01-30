int main()
{
  struct S
  {
    int x;
  };

  struct S static __attribute__((__section__(".somewhere")))
  elements1[] = {{0}};

  struct
  {
    int a;
    int b;
  } static __attribute__((__section__(".somewhere"))) elements2[] = {{0, 0}};

  return 0;
}
