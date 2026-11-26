// N5008 [meta.const.eval]/1: is_constant_evaluated() is true within a
// manifestly constant-evaluated context, such as the initializer of a
// constexpr variable ([dcl.constexpr]/6, [expr.const]) or a case label
// ([stmt.switch]/2).  libstdc++'s std::__is_constant_evaluated() forwards
// __builtin_is_constant_evaluated(), whose type is _Bool, and its
// string_view::operator[] tests it in the precondition check:
// GCC 16's <format> reads `_Escapes<_CharT>::_S_newline()[0]' in a case
// label of __should_escape_ascii.
extern "C" void __CPROVER_assert(bool, const char *);

constexpr bool in_constant_evaluation() noexcept
{
  return __builtin_is_constant_evaluated();
}

constexpr int which()
{
  if(in_constant_evaluation())
    return 1;
  return 2;
}

struct view
{
  const char *str;
  constexpr char operator[](unsigned long i) const
  {
    if(in_constant_evaluation() && i > 1)
      __builtin_unreachable();
    return str[i];
  }
};

consteval view escapes()
{
  return {"\t\n"};
}

bool should_escape(char c)
{
  switch(c)
  {
  case escapes()[1]:
    return true;
  default:
    return false;
  }
}

int main()
{
  constexpr int at_compile_time = which();
  __CPROVER_assert(at_compile_time == 1, "constant evaluation");
  __CPROVER_assert(which() == 2, "run time");
  __CPROVER_assert(should_escape('\n'), "case label");
  __CPROVER_assert(!should_escape('a'), "default");
  __CPROVER_assert(should_escape('a'), "WRONG (must FAIL)");
  return 0;
}
