// As cpp_list_init_non_viable_init_list_ctor, but exercising the
// variable-declaration form `S s{p};` (in addition to the expression
// form `S{p}`).  Per over.match.list/1, the non-viable initializer-list
// constructor must not be selected; the const char* constructor is.

#include <cassert>
#include <initializer_list>

struct alloc
{
};

struct S
{
  int which;
  S(std::initializer_list<char>, const alloc & = alloc()) : which(1)
  {
  }
  S(const char *) : which(2)
  {
  }
};

int main()
{
  const char *p = "x";
  S s{p};
  assert(s.which == 2);

  S t{'a', 'b', 'c'};
  assert(t.which == 1);
  return 0;
}
