extern "C" void __CPROVER_assert(bool, const char *);

// N5008 [conv.func] + [over.ics.list]: a free function named inside a
// nested braced-init-list decays to a function pointer when the
// corresponding aggregate element is a function-pointer type.  CBMC
// converts the outer constructor call and used to mishandle the inner
// aggregate's decay (fixed 2026-07-21): "address-of code requires a member expression
// (operand id=symbol)".  A plain aggregate initializer with the same
// pair works.  The shape of variable-sensitivity's
// `std::map<irep_idt, assume_function>{{ID_not, assume_not}, ...}`,
// which blocks dog-fooding abstract_environment.cpp.
// g++/clang++ accept and verify at runtime.

using fnt = int (*)(int);

static int twice(int x)
{
  return 2 * x;
}

struct pairt
{
  int key;
  fnt fn;
};

struct mapt
{
  pairt slot;
  explicit mapt(const pairt &p) : slot(p)
  {
  }
};

int main()
{
  auto table = mapt{{1, twice}}; // nested brace: pair from {1, twice}
  __CPROVER_assert(table.slot.fn(21) == 42, "function decay in nested brace");
  return 0;
}
