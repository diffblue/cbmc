// N5008 [expr.new]/17 + [dcl.init.general]/9: a new-initializer that is
// an empty pair of parentheses value-initializes the object; for a
// scalar that is zero-initialization.  Split from
// cpp11_empty_pack_new_initializer: CBMC's placement new with `int()`
// leaves the storage unchanged (7 survives), independent of templates.
extern "C" void __CPROVER_assert(bool, const char *);
void *operator new(unsigned long, void *) noexcept;
int main()
{
  int v = 7;
  ::new((void *)&v) int();
  __CPROVER_assert(v == 0, "placement new value-init zeroes a scalar");
  return 0;
}
