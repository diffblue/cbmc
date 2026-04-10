struct ab
{
  int a, b;
};

struct ab nondet_ab(void);

int main()
{
  struct ab s, q = nondet_ab();

  s = q;

  assert(s.a == q.a);
}
