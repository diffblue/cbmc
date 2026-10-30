// N5008 [basic.scope.class]/1: the class scope of `outer_b::infot' includes
// its member-specification, not its base-clause, so the base-specifier
// `configt' is looked up in the enclosing scope and names
// outer_b::configt.  The front end attached each base's scope as soon as
// that base was resolved, and found the injected-class-name `configt' of
// outer_a::infot's own base outer_a::configt: outer_b::configt was not a
// base, "symbol 'bound' is unknown" (CBMC's own string_refinementt::infot,
// whose bases bv_refinementt::infot and configt both reach a `configt';
// solver_factory.cpp, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct outer_a
{
  struct configt
  {
    int a = 1;
  };
  struct infot : public configt
  {
    int *p = nullptr;
  };
};
struct outer_b
{
  struct configt
  {
    int bound = 2;
  };
  // two (indirect and direct) bases that are distinct classes with the same
  // name `configt'
  struct infot : public outer_a::infot, public configt
  {
  };
};
int main()
{
  outer_b::infot info;
  info.bound = 5;
  info.a = 3;
  __CPROVER_assert(info.bound == 5 && info.a == 3, "members of both configt");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
