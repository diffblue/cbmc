// N5008 [dcl.fct.def.default]/5, [class.access.general]/2: a constructor
// explicitly defaulted on its first declaration is a member of its class;
// its implicit definition initializes the private members from their
// default member initializers.  libstdc++ 13 <format>'s
// formatter<const void *, C> has `formatter() = default;' and a private
// `_Spec<C> _M_spec{}'.
extern "C" void __CPROVER_assert(bool, const char *);

struct spec
{
  int width = 3;
};

template <class T, class C>
struct formatter;

template <class C>
struct formatter<const void *, C>
{
  formatter() = default;
  int width() const
  {
    return s.width;
  }

private:
  spec s{};
};

struct plain
{
  plain() = default;
  int width() const
  {
    return s.width;
  }

private:
  spec s{};
};

int main()
{
  formatter<const void *, char> f;
  plain p;
  __CPROVER_assert(f.width() == 3 && p.width() == 3, "initialized");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
