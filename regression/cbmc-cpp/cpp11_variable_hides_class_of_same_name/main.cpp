// N5008 [basic.lookup.general]/4 ([basic.scope.hiding]): a class name is
// hidden by a variable of the same name declared in the same scope, the C
// idiom `typedef struct cfg { ... } cfg_t; cfg_t cfg;'.  With a member of a
// class type with a constructor, cfg has implicit constructors, which were
// found under the class name next to the variable: "symbol 'cfg' does not
// uniquely resolve".
extern "C" void __CPROVER_assert(bool, const char *);
struct member
{
  int x;
  member() : x(0)
  {
  }
};
typedef struct cfg
{
  int field;
  member m;
} cfg_t;
cfg_t cfg;
int main()
{
  cfg.field = 4;
  __CPROVER_assert(cfg.field == 4 && cfg.m.x == 0, "the variable");
  struct cfg other;
  other.field = 1;
  __CPROVER_assert(other.field == 1, "the class, elaborated");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
