// N5008 [basic.scope.hiding]/2: a class or enumeration name can be hidden by
// the name of a variable, data member, function, or enumerator declared in the
// same scope.  If a class name and a function are declared in the same scope
// with the same name, the class name is hidden wherever the function name is
// visible.  So in an expression the call `box()` names the function, not a
// constructor of the type `box`; the type is only reachable via the elaborated
// form `struct box`.
//
// This is the classic C-library pattern where a struct tag and a function
// share a name -- POSIX `struct stat` / `stat()`, glibc `struct mallinfo` /
// `mallinfo()` (memory_info.cpp uses `struct mallinfo m = mallinfo();`).  CBMC
// used to report "symbol 'box' does not uniquely resolve" because it offered
// both the function and the (hidden) type's implicit constructors as
// candidates for `box()`.
//
// Here `box` is both a struct and a same-named function returning it; `box()`
// must call the function.  g++ and clang++ accept this.
//
// Non-vacuous: assertion.2 must FAIL.

extern "C" void __CPROVER_assert(int, const char *);

struct box
{
  int v;
};

// A function whose name is the same as the struct 'box'.  Per
// [basic.scope.hiding]/2 this hides the type name in ordinary (value) lookup.
struct box box(void);

struct box box(void)
{
  struct box b;
  b.v = 7;
  return b;
}

int main()
{
  struct box m = box(); // must call the function, not construct the type
  __CPROVER_assert(m.v == 7, "same-named function hides the struct type");
  __CPROVER_assert(m.v != 7, "WRONG must FAIL");
  return 0;
}
