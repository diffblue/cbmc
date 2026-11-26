// N5008 [dcl.pre]: static_assert with a message object providing size() and
// data().
extern "C" void __CPROVER_assert(bool, const char *);
struct M
{
  constexpr int size() const
  {
    return 2;
  }
  constexpr const char *data() const
  {
    return "ok";
  }
};
static_assert(true, M{});
int main()
{
  __CPROVER_assert(true, "static_assert with a user-generated message");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
