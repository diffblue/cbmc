// A file-local function defined in a shared header: when two translation
// units include it and are compiled with --export-file-local-symbols, both
// mangle `helper` to the same __CPROVER_file_local_lib_h_helper name.  Its
// parameter symbol (helper::x) must be mangled in lockstep, otherwise the
// two TUs carry identically-named parameter symbols that clash at link time.
static int helper(int x)
{
  // A body-local variable exercises the function-local scope chain
  // (helper::...::t), which must be mangled in lockstep with the parameter.
  int t = x + 1;
  return t;
}
