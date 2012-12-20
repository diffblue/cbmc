int nondet_int();
void *malloc(unsigned s);

typedef struct {
    int i;
} s;

typedef s *s_t;

int analyze_this()
{
  s_t p;

  p = (s_t)malloc(1);

  // this should fail, as it's too small
  p->i = nondet_int();
}

int main()
{
  analyze_this();
}
