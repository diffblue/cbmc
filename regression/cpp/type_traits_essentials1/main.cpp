// variadic template arguments
template<typename...>
struct V;

template<typename>
struct F
{
};

template<typename T, typename... A>
struct F<T(A..., ...)>
{
};

template<typename>
struct G
{
};

template<typename T, typename... A>
struct G<T(A......)>
{
};

// alias-declaration (7.1.3 typedef)
using i=int;
template<typename T> using x=V<T>;

template<typename T>
class C
{
public:
  static constexpr int value=0;
};

// conditional expressions
template<bool x = (
  1 >> 1 > 2 ? true && false :
  0
  + C<C<int>>::value
  + noexcept(true)
  )>
// >> (and >>>) to be parsed as nested closing template brackets
class X
:public C<C<int>>
{
  public:
    bool val()
      noexcept
    {
      return x;
    }

};

int main(int argc, char* argv[])
{
  X<true> x;
  return x.val()?0:1;
}
