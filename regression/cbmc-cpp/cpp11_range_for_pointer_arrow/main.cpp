// Dog-food kernel (src/util/get_module.cpp): iterating a container of
// POINTERS with a range-for and dereferencing the pointer element with
// -> failed with "symbol 'operator->' is unknown".  N5008
// [stmt.ranged]/1: the loop variable is declared with its full
// DECLARATOR (`const symbolt *p` declares a pointer); CBMC's
// desugaring took only the declaration's type, so `p` got the CLASS
// type and `p->name_len` resolved as an overloaded operator->
// ([over.ref]) instead of the built-in pointer access ([expr.ref]).
extern "C" void __CPROVER_assert(bool, const char *);
struct symbolt
{
  int name_len;
};
int main()
{
  symbolt s{3};
  const symbolt *arr[1] = {&s};
  int n = 0;
  for(const symbolt *p : arr)
    n = p->name_len;
  __CPROVER_assert(n == 3, "arrow on pointer element of range-for");
  return 0;
}
