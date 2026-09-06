// N5008 [class.mem.general]/10 + [dcl.init.aggr]: a default member
// initializer with a braced-init-list applies to an aggregate member
// containing an ARRAY -- `vec v_{{7, 8}};` initializes v_.data_[0..1].
// CBMC converts the initialization into an assignment and rejects it
// ("direct assignments to arrays not permitted").  Found while
// dog-fooding src/util (goto-cc over CBMC's own sources).
extern "C" void __CPROVER_assert(bool, const char *);
struct vec
{
  int data_[2];
};
struct holder
{
  vec v_{{7, 8}};
};
int main()
{
  holder h;
  __CPROVER_assert(h.v_.data_[0] == 7, "array member in default member initializer");
  return 0;
}
