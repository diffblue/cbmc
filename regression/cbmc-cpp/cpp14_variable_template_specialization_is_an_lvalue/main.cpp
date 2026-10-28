// N5008 [expr.prim.id.unqual]/12: an id-expression naming a variable is an
// lvalue; a specialization of a variable template is a variable
// ([temp.pre]/1), so it can be assigned, incremented and have its address
// taken, and decltype((v<T>)) is a reference type ([dcl.type.decltype]/1.5).
extern "C" void __CPROVER_assert(bool, const char *);

template <class>
int counter = 3;

template <class T, class U>
constexpr bool same = false;
template <class T>
constexpr bool same<T, T> = true;

int main()
{
  __CPROVER_assert(counter<long> == 3, "initialized");
  counter<char> = 5;
  ++counter<char>;
  int *p = &counter<int>;
  *p = 7;
  __CPROVER_assert(counter<char> == 6, "assigned and incremented");
  __CPROVER_assert(counter<int> == 7, "through its address");
  __CPROVER_assert(same<decltype((counter<char>)), int &>, "lvalue");
  __CPROVER_assert(counter<char> == 5, "WRONG (must FAIL)");
  return 0;
}
