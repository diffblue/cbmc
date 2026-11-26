extern "C" void __CPROVER_assert(bool, const char *);

// [temp.local]/1: the injected-class-name of a class template
// specialization, followed by `<', names the class template; a derived
// class finds it as a member of its base ([class.member.lookup]), also
// where the template is declared in another namespace
namespace details
{
template <typename Leaf, typename Value>
class quantity
{
public:
  Value value;
  quantity(Value v) : value(v)
  {
  }
};
} // namespace details

class count : public details::quantity<count, unsigned>
{
public:
  count(unsigned v) : quantity(v)
  {
  }
  count(const quantity<count, unsigned> &q) : quantity(q)
  {
  }
  static unsigned get(const quantity<count, unsigned> &q)
  {
    return q.value;
  }
  // a different specialization of the same template
  static long other(const quantity<count, long> &q)
  {
    return q.value;
  }
};

int main()
{
  count c(7);
  count d(static_cast<const details::quantity<count, unsigned> &>(c));
  details::quantity<count, long> l(-3);
  __CPROVER_assert(
    count::get(d) == 7 && count::other(l) == -3, "injected-class-name");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
