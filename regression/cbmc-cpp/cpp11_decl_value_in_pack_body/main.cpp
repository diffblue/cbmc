// N5008 [dcl.init]/15-16: `S x = "s";` is copy-initialization via S's
// converting constructor; the declarator carries a VALUE, not
// parenthesised init-args.
//
// Regression: the function-template body pack expander created an EMPTY
// ID_init_args entry on every declarator it visited (irept::add
// creates-on-absence), including one initialised with `= value`; the
// block-scope declaration typecheck then crashed on the invariant
// "declarator should not have init_args".  Found by dog-fooding CBMC's
// own util/invariant.h (`std::string backtrace = ...` inside the variadic
// report_invariant_failure chain); the trigger needs an S-typed by-value
// argument forwarded into the pack-taking callee and a `= value`
// declaration in the callee's body.
//
// g++/clang++ accept and verify the value at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

struct S
{
  int tag;
  S(const char *s) : tag(s[0]) {}
};

template <typename... Params>
int inner(const int line, const S &condition, Params &&... params)
{
  S backtrace = "b";
  return backtrace.tag + condition.tag + line;
}

template <typename... Diagnostics>
int outer(int line, S reason, S condition, Diagnostics &&... diagnostics)
{
  return inner(line, reason, condition, 0);
}

int main()
{
  // 'b' = 98, reason "m" ignored by inner's value, condition... inner
  // receives (line, reason, [condition, 0] as pack): condition bound to
  // the S& parameter is `reason` ("m" = 109).
  int r = outer(4, "m", "c", "d");
  __CPROVER_assert(r == 98 + 109 + 4, "copy-init decl in pack body");
  return 0;
}
