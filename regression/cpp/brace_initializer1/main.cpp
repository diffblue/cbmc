struct __invoke_memfun_ref {};
    constexpr bool __call_is_nt(__invoke_memfun_ref)
    {
      return false;
    }

  template<typename _Result>
    struct __call_is_nothrow
    {
      constexpr static bool is_nt =
__call_is_nt(typename _Result::__invoke_type{});
    };

int main(int argc, char * argv[])
{
  struct S {
    S() : x(42)
                 {
                 }

    int x;
  };
  S s = S{};
}
