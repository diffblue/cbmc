extern "C" void __CPROVER_assert(bool, const char *);

// N5008 [dcl.init.list]/3.10: a braced-init-list with a single element
// initializing a reference binds the reference to that element.  CBMC
// used to reject the form ("bad reference initializer") -- fixed
// 2026-07-21.  The shape of
// `symbolt &fb_sym{symbol_table.get_writeable_ref(...)}`, which blocks
// dog-fooding src/statement-list/statement_list_typecheck.cpp.
// g++/clang++ accept and verify at runtime.

int main()
{
  int x = 41;
  int &r{x}; // [dcl.init.list]/3.10: single-element list binds the reference
  r += 1;
  __CPROVER_assert(x == 42, "braced reference binding");
  return 0;
}
