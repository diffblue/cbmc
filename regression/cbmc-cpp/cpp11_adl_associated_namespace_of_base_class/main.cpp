extern "C" void __CPROVER_assert(bool, const char *);
namespace pipe
{
struct base
{
};
template <class L, class R>
int operator|(L, R)
{
  return 7;
}
} // namespace pipe
struct closure : pipe::base
{
};
struct more_derived : closure
{
};
// N5008 [basic.lookup.argdep]/3.2: the associated entities of a class are the
// class, the class of which it is a member, and its direct and indirect base
// classes; the associated namespaces are their innermost enclosing namespaces
// (the MSVC STL's `arr | views::take(3)', ranges::_Pipe::_Base)
int main()
{
  int arr[3] = {};
  closure c;
  more_derived m;
  __CPROVER_assert((arr | c) == 7 && (1 | m) == 7, "found through the base");
  __CPROVER_assert((arr | c) == 8, "WRONG (must FAIL)");
  return 0;
}
