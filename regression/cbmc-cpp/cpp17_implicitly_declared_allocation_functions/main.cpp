// N5008 [basic.stc.dynamic.general]/2: the global allocation and
// deallocation functions, including the sized and aligned forms, are
// implicitly declared in each translation unit; calling them needs no
// #include <new>.  Only operator new(size_t) and operator delete(void *)
// were declared: the sized delete was "found no match".
extern "C" void __CPROVER_assert(bool, const char *);
struct alignas(64) block
{
  char c[64];
};
int main()
{
  void *p = ::operator new(8);
  ::operator delete(p, 8);
  void *q = ::operator new[](8);
  ::operator delete[](q, 8);
  block *b = new block;
  __CPROVER_assert(b != nullptr, "new-expression");
  delete b;
  block *a = new block[2];
  delete[] a;
  __CPROVER_assert(p != nullptr && q != nullptr, "allocated");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
