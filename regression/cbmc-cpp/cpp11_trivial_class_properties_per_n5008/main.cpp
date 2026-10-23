// N5008 [class.prop]/1: a trivially copyable class has at least one eligible
// copy/move constructor or assignment operator, each eligible one trivial,
// and a trivial, NON-DELETED destructor.  [depr.meta.types]/3: a trivial
// class is trivially copyable and has one or more eligible default
// constructors, all trivial; [special]/6: a deleted function is not
// eligible.
//  * no_dtor (deleted destructor) is not trivially copyable, hence neither
//    trivial nor POD;
//  * with_ref (a reference member) is trivially copyable -- its copy and
//    move constructors are trivial, its copy assignment is deleted
//    ([class.copy.assign]/7.2) and so not eligible -- but not trivial: its
//    default constructor is deleted ([class.default.ctor]/2.1).
// g++ 13 and clang++ 20 answer true for no_dtor's traits and for
// is_trivial(with_ref); the front end follows N5008, so natively assertions
// 1, 2, 3 and 5 fail as well.
extern "C" void __CPROVER_assert(bool, const char *);

struct no_dtor
{
  ~no_dtor() = delete;
  int x;
};
struct with_ref
{
  int &r;
};

int main()
{
  __CPROVER_assert(!__is_trivially_copyable(no_dtor), "deleted destructor");
  __CPROVER_assert(!__is_trivial(no_dtor), "not trivial");
  __CPROVER_assert(!__is_pod(no_dtor), "not POD");
  __CPROVER_assert(__is_trivially_copyable(with_ref), "reference member");
  __CPROVER_assert(!__is_trivial(with_ref), "deleted default constructor");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
