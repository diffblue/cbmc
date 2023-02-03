typedef struct vtable_s
{
  int (*f)(void);
} vtable_t;

int return_0()
{
  return 0;
}

static vtable_t vtable_0 = {.f = &return_0};

void foo(vtable_t *vtable)
  __CPROVER_requires((void *)0 == vtable || &vtable_0 == vtable)
{
  if(vtable->f)
    vtable->f();
}

int main()
{
  vtable_t *vtable;
  foo(vtable);
}
