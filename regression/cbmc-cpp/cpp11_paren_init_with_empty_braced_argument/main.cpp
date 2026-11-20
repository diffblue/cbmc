// N5008 [dcl.init.general]/16.6.2: `info i({})' direct-initializes i from
// one argument, the empty braced-init-list, which copy-list-initializes the
// `const fn &' parameter of info's constructor ([over.ics.list]).  It is not
// the value-initialization `info i{}' ([dcl.init.list]/3.5), which needs a
// default constructor info does not have.  The front end treated both
// alike: "found no match for symbol 'info'" (CBMC's own contracts.cpp,
// `function_cfg_infot cfg_info({})', dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct fn
{
  int body = 7;
};
struct info
{
  int got;
  explicit info(const fn &f) : got(f.body)
  {
  }
};
int main()
{
  // N5008 [dcl.init.general]/16.6.2: one argument, the empty
  // braced-init-list, which copy-list-initializes the `const fn &'
  // parameter ([over.ics.list]); info has no default constructor
  info i({});
  __CPROVER_assert(i.got == 7, "constructed from {}");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
