// C++11 alias declarations and template alias declarations
namespace N
{
struct S
{
};
using T = S;
T make();
} // namespace N

template <typename X>
struct wrapper
{
  X val;
};

template <typename X>
using wrap = wrapper<X>;

int main()
{
  wrap<int> w;
  w.val = 42;
  return 0;
}
