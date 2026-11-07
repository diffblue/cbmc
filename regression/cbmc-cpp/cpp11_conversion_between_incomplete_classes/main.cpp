// N5008 [conv.ptr]/3, [over.best.ics]: a pointer to one class converts to a
// pointer to another only if the second is a base of the first, which an
// incomplete class has not.  Two incomplete classes were taken for the same
// class (neither carried a name to compare), so `B *' accepted an `A *', and
// clang's __is_convertible(A, B) held: libc++'s iota_view picked the wrong
// iterator concept from derived_from<__iter_concept_cache,
// input_iterator_tag>.
extern "C" void __CPROVER_assert(bool, const char *);

struct A;
struct B;
struct C
{
};
struct D : C
{
};

int f(B *)
{
  return 1;
}
int f(...)
{
  return 2;
}

static_assert(!__is_convertible(A *, B *), "pointers to incomplete classes");
static_assert(__is_convertible(A *, A *), "same incomplete class");
static_assert(__is_convertible(D *, C *), "derived to base");
static_assert(!__is_convertible(C *, D *), "base to derived");

int main()
{
  A *pa = nullptr;
  __CPROVER_assert(f(pa) == 2, "no conversion to B *");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
