// N5008 [dcl.attr.grammar]/1: an attribute-specifier-seq may hold several
// alignment-specifiers; [dcl.align]/4: the strictest of them applies.  The
// MSVC STL's <regex> declares `alignas(A) alignas(B) alignas(C) unsigned
// char _Stackbuf[4096];' in a function body.
extern "C" void __CPROVER_assert(bool, const char *);

struct member
{
  alignas(2) alignas(8) alignas(4) char c;
};

alignas(4) alignas(16) unsigned char global[16];

template <class T>
int local()
{
  alignas(T) alignas(int) unsigned char buffer[16];
  buffer[0] = 1;
  return buffer[0];
}

int main()
{
  alignas(8) alignas(2) char c[2];
  c[0] = 3;
  global[1] = 2;
  __CPROVER_assert(alignof(member) == 8, "the strictest member alignment");
  __CPROVER_assert(sizeof(member) == 8, "padded to it");
  __CPROVER_assert(local<long long>() == 1 && c[0] == 3, "block scope");
  __CPROVER_assert(global[1] == 2, "namespace scope");
  __CPROVER_assert(alignof(member) == 4, "WRONG (must FAIL)");
  return 0;
}
