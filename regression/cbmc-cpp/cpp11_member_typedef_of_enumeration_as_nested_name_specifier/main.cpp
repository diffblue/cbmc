extern "C" void __CPROVER_assert(bool, const char *);
namespace imp
{
enum class action
{
  destroy,
  copy
};
} // namespace imp
class holder
{
public:
  int last = -1;
  // [class.mem.general]/7: a member function body is a complete-class
  // context -- the member typedef declared below is visible here
  void copy()
  {
    record(action::copy);
  }
  void destroy()
  {
    record(action::destroy);
  }

private:
  typedef imp::action action;
  void record(action a)
  {
    last = static_cast<int>(a);
  }
};
int main()
{
  holder h;
  h.copy();
  __CPROVER_assert(h.last == 1, "enumerator through a later member typedef");
  h.destroy();
  __CPROVER_assert(h.last == 0, "the other enumerator");
  __CPROVER_assert(h.last == 1, "WRONG (must FAIL)");
}
