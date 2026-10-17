// N5008 [temp.variadic]/5: pack expansions in braced-init-lists and call
// argument lists of a function template with only a type parameter pack.
extern "C" void __CPROVER_assert(bool, const char *);

unsigned long g(unsigned long a, unsigned long b, unsigned long c)
{
  return a + b + c;
}

template <typename... Ts>
unsigned long sum_sizes_call()
{
  return g(sizeof(Ts)...);
}

template <typename... Ts>
unsigned long sum_sizes_list()
{
  unsigned long s[] = {sizeof(Ts)...};
  unsigned long r = 0;
  for(unsigned long i = 0; i < sizeof...(Ts); ++i)
    r += s[i];
  return r;
}

template <typename T, typename... Ts>
unsigned long count_same()
{
  const bool found[sizeof...(Ts)] = {__is_same(T, Ts)...};
  unsigned long c = 0;
  for(unsigned long i = 0; i < sizeof...(Ts); ++i)
    c += found[i];
  return c;
}

template <typename... Ts>
struct holder
{
  static unsigned long sum()
  {
    unsigned long s[] = {sizeof(Ts)...};
    return s[0] + s[1] + s[2];
  }
};

int main()
{
  __CPROVER_assert(sum_sizes_call<char, int, double>() == 13, "call");
  __CPROVER_assert(sum_sizes_list<char, int, double>() == 13, "list");
  __CPROVER_assert(count_same<int, char, int, int>() == 2, "is_same list");
  __CPROVER_assert(holder<char, int, double>::sum() == 13, "class member");
  return 0;
}
