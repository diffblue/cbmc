// N5008 [dcl.ambig.res]/1 + [dcl.init.general]/16.9: a constexpr
// enum-typed variable direct-initialized with parentheses from an
// ENUMERATOR (libstdc++'s regex_constants error_type constants).  The
// name-lookup disambiguation correctly re-interprets the vexing parse
// as a variable, but the initializer travelled through the
// constructor-call path and the fold-away macro's value became VOID.
extern "C" void __CPROVER_assert(bool, const char *);

namespace N
{
enum error_type
{
  _S_error_collate,
  _S_error_ctype
};

constexpr error_type error_collate(_S_error_collate);
constexpr error_type error_ctype(_S_error_ctype);
} // namespace N

int main()
{
  __CPROVER_assert(N::error_collate == N::_S_error_collate, "collate");
  __CPROVER_assert(N::error_ctype == N::_S_error_ctype, "ctype");
  return 0;
}
