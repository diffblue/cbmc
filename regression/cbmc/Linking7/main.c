struct S
{
  void *a;
  void *b;
};

typedef void (*fptr)(struct S);

extern void foo(struct S s);

fptr A[] = { foo };

extern void bar();

int main()
{
  bar();
  return 0;
}
