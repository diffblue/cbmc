struct S1
{
};

struct S2
{
};

typedef union my_union
{
  const int *ip;
  const struct S1 *s1;
  const struct S2 *s2;
} U;

typedef U U2 __attribute__ ((__transparent_union__));

void f(U2 some)
{
}

int main()
{
  struct S1 s1;
  struct S2 s2;
  
  f(&s1);
  f(&s2);
  f(0);
}
