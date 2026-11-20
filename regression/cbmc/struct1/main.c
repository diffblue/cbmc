/* do empty ones */
struct I_AM_EMPTY
{
};

struct x {
  int f;
  int g;
};

struct y {
  struct x X;
  int h;
  struct I_AM_EMPTY empty_sub;
};

int main()
{
  struct y nondet_y(void);
  struct y Y = nondet_y();

  {
    struct x tmp;
    tmp = Y.X;
    tmp.f = 1;
    Y.X = tmp;
  }

  assert(Y.X.f == 1);
}
