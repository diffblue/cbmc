extern "C" void __CPROVER_assert(bool, const char *);

// [expr.cast]/1 with [dcl.ambig.res]: `(x) - y' and `(x)(y)' are casts
// only if x names a type; otherwise `(x)' is an operand and the operators
// around it group as for any other operand.
typedef int number;
struct stat
{
  int size;
};
static int stat(int a)
{
  return a + 40;
}
static int inc(int a)
{
  return a + 1;
}
static int mul(int a, int b)
{
  return a * b;
}
typedef int (*function)(int);
static function pick(int)
{
  return inc;
}

template <int N>
int minus_parameter(int x)
{
  return (N)-x;
}

template <class T>
int subscript_minus(T *p)
{
  return (p[1]) - 2;
}

int main()
{
  int x = 200, y = 3, z = 5, ff = 0xff;
  int a[2] = {7, 9};
  int *p = a;
  unsigned u = 1;
  double d = 2.5;

  // a cast, then the binary operator
  __CPROVER_assert(
    (signed char)(x)-100 == -156 && (unsigned char)(x) * 2 == 400 &&
      (long)(u)-2 == -1 && (int)(d) * 2 == 4 &&
      ((signed char)(ff) & (0x1ff)) == 0x1ff && (number)(x) + 1 == 201,
    "cast before a binary operator");
  __CPROVER_assert(
    (number)-1 == -1 && (number)*p == 7 && (number) + 1 == 1,
    "cast of a unary expression");

  // a parenthesized operand of a binary operator
  __CPROVER_assert(
    (x)-y * z == 185 && z * (x)-y == 997 && (x)-y - z == 192 &&
      -(x)-y == -203 && (x) * *p == 1400 && ((x) & (y)) == 0 && ((x) && y) &&
      !((x) && 0),
    "parenthesized operand");

  // a call of a parenthesized function name
  __CPROVER_assert(
    (inc)(*p) == 8 && (mul)(x, y) == 600 && (inc)((x, y)) == 4 &&
      (inc)(x)-1 == 200 && (pick)(x)(y)-1 == 3 && (inc)(a[1]) == 10,
    "call");

  // the function hides the class of the same name
  __CPROVER_assert((stat)(2) == 42, "function hides class");

  __CPROVER_assert(
    minus_parameter<10>(3) == 7 && subscript_minus(a) == 7, "in templates");

  {
    int number = 3;
    __CPROVER_assert((number)-1 == 2, "variable hides typedef");
  }

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
