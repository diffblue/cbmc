// Direct-list-initialization overload resolution proceeds in two phases
// (N5008 over.match.list/1): first the initializer-list constructors are
// considered with the braced-init-list as a single argument; only if no
// viable initializer-list constructor is found are all constructors
// considered with the elements as arguments.  Modelled on std::string:
// S has an initializer_list<char> constructor (with a defaulted second
// parameter, like the allocator) and a const char* constructor.  S{p}
// for a const char* p must select S(const char*) because the
// initializer-list constructor is not viable (const char* does not
// convert to char); S{'x','y'} must select the initializer_list
// constructor.

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

S from_cstr(const char *p)
{
  return S{p};
}

int main()
{
  const char *p = "x";
  S a = from_cstr(p);
  assert(a.which == 2);

  S b = S{'x', 'y'};
  assert(b.which == 1);
  return 0;
}
