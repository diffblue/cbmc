// A static object's initializer must be a compile-time constant.  A compound
// literal that embeds a non-constant value (here a runtime local) is therefore
// rejected.  This pins down the operand recursion in
// c_typecheck_baset::is_constant: ID_compound_literal must not over-approximate
// constancy.  The accepting counterpart is regression/cbmc/
// compound_literal_static_init.  Named types are used deliberately to keep the
// signal on compound-literal constancy (no anonymous-member dependency).
struct inner
{
  int val;
};

struct rl
{
  struct inner lock;
  int interval;
};

int main(void)
{
  int nonconst;
  static struct rl r = {.lock = (struct inner){.val = nonconst}, .interval = 5};
  return r.interval;
}
