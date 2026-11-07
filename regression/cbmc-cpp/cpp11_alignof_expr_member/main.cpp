// GNU __alignof__(expression) (the standard [expr.alignof] only has
// the type-id form): libstdc++'s __aligned_membuf spells its storage
// `alignas(__alignof__(_M_t)) unsigned char _M_storage[sizeof(_Tp)]`.
//
// This used to fail: the C++ parser can only parse the parenthesised
// operand as a type-id, so a name denoting an OBJECT mis-parsed as a
// type and resolution failed ("found no match for symbol '_M_t'") --
// silently, in the alignment-specifier position, degrading the
// alignment to 1 and mis-sizing every __aligned_membuf.  Fixed by
// disambiguating exactly like sizeof (resolve with wantt::BOTH).
//
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

struct pairt
{
  int first;
  int second;
};

pairt _M_t;

struct membuft
{
  alignas(__alignof__(_M_t)) char storage;
};

int main()
{
  __CPROVER_assert(__alignof__(_M_t) == 4, "alignof of an lvalue");
  __CPROVER_assert(
    sizeof(membuft) == 4, "alignas(__alignof__(expr)) reaches layout");
  return 0;
}
