// transparent union is GCC only
#ifdef __GNUC__
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

union my_union2
{
  int i;
  const struct S1 s1;
} __attribute__ ((__transparent_union__));

void f1(U2 some)
{
}

void f2(union my_union2 some)
{
}

int main()
{
  struct S1 s1;
  struct S2 s2;
  
  f1(&s1);
  f1(&s2);
  f1(0);
  
  f2(0);
  f2(1>2); // these are int
}
#else

int main()
{
}

#endif
