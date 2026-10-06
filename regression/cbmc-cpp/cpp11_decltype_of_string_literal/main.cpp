// N5008 [expr.prim.literal]/1, [lex.string]/6, [dcl.type.decltype]/1.5: a
// string literal is an lvalue of type `array of n const char', so
// decltype("a") is const char (&)[2]
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  __CPROVER_assert(__is_same(decltype("a"), const char(&)[2]), "narrow");
  __CPROVER_assert(
    __is_same(decltype(u"ab"), const char16_t(&)[3]), "char16_t");
  __CPROVER_assert(
    __is_same(decltype("a"), const char[2]), "WRONG (must FAIL)");
}
