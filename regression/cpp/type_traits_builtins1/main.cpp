// GCC built-in type traits parsing and __attribute__ as statement
struct S
{
  int x;
};

// These are parsed but type-checked as unknown expressions
template <typename T>
struct check
{
  static const bool trivial = __is_trivial(T);
  static const bool pod = __is_pod(T);
};

void f()
{
  // __attribute__ as a statement
  __attribute__((__unused__));
}

int main()
{
  f();
  return 0;
}
