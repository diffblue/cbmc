// N5008 [expr.reinterpret.cast]/1, [expr.const.cast]/1, [expr.cast]: the
// array-to-pointer conversion is applied to the operand before the cast.
// The C-style and reinterpret_cast paths converted the operand and then
// cast the ORIGINAL array value: `(char *)a.s' became a typecast of an array,
// which symbolic execution cannot relate to the object's address (pointer
// differences UNKNOWN, reads through the aligned-storage idiom FAILURE).
extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  unsigned char s[4];
};
struct B
{
  int x;
  unsigned char s[4];
};
template <class T>
struct aligned_storage
{
  alignas(T) unsigned char s[sizeof(T)];
  T *ptr()
  {
    return reinterpret_cast<T *>(s);
  }
};
struct NB
{
  NB *n;
  NB *p;
};
template <class T>
struct node : NB
{
  aligned_storage<T> st;
  T *valptr()
  {
    return st.ptr();
  }
};
int main()
{
  A a;
  B b;
  __CPROVER_assert(
    (char *)a.s - (char *)&a == 0, "C-style cast, other element type");
  __CPROVER_assert(
    (unsigned char *)a.s == &a.s[0], "C-style cast, same element type");
  __CPROVER_assert(
    reinterpret_cast<char *>(a.s) == (char *)&a, "reinterpret_cast");
  __CPROVER_assert(static_cast<unsigned char *>(a.s) == a.s, "static_cast");
  __CPROVER_assert((char *)b.s - (char *)&b == 4, "second member");
  __CPROVER_assert((char *)(int *)a.s - (char *)&a == 0, "two casts");
  node<int> nd;
  NB *base = &nd;
  node<int> *d = static_cast<node<int> *>(base);
  __CPROVER_assert(
    (char *)d->valptr() - (char *)&nd == 16, "aligned storage at 16");
  *d->valptr() = 5;
  __CPROVER_assert(*nd.valptr() == 5, "read through the storage pointer");
  __CPROVER_assert(sizeof(node<int>) == 24, "size");
  return 0;
}
