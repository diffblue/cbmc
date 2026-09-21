extern "C" void __CPROVER_assert(bool, const char *);
#include <functional>
#include <optional>

struct exprt2
{
  int v;
};

struct instr
{
  int val = 5;
  void transform(std::function<std::optional<exprt2>(exprt2)> f)
  {
    exprt2 e{val};
    auto r = f(e);
    if(r.has_value())
      val = r->v;
  }
};

int main()
{
  instr i;
  int bump = 2;
  i.transform(
    [&bump](exprt2 e) -> std::optional<exprt2>
    {
      if(e.v == 5)
      {
        e.v = 5 + bump;
        return e;
      }
      return {};
    });
  __CPROVER_assert(i.val == 7, "transform through optional-returning lambda");
  return 0;
}
