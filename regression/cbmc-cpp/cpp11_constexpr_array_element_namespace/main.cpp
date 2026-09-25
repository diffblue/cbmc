// N5008 [dcl.constexpr]/6: "A constexpr specifier used in an object
// declaration declares the object as const."  A constexpr ARRAY lost that
// const (`constexpr int a[] = {1, 2, 3}' had type int[3], unlike `const int
// a[]'), so a static_assert over an element could not be evaluated -- and at
// namespace scope the skipped assertion was SILENT.  Likewise a
// namespace-scope constexpr object of class type built by a constexpr
// constructor (`constexpr P gp(42)') lost its recorded value to the
// constructor call.  Both now fold.
extern "C" void __CPROVER_assert(bool, const char *);

constexpr int arr[] = {1, 2, 3};
constexpr unsigned char bytes[4] = {0xde, 0xad, 0xbe, 0xef};
static_assert(arr[1] == 2, "array element");
static_assert(arr[0] + arr[2] == 4, "two elements");
static_assert(sizeof(arr) / sizeof(arr[0]) == 3, "count");
static_assert(bytes[3] == 0xef, "unsigned char element");

struct P
{
  int v;
  int w = 7;
  constexpr P(int a) : v(a)
  {
  }
  constexpr P() : v(1)
  {
  }
  constexpr int sum() const
  {
    return v + w;
  }
};
constexpr P gp(42);
constexpr P gq = P();
constexpr P gr{};
static_assert(gp.v == 42 && gp.w == 7, "constexpr ctor at namespace scope");
static_assert(gq.v == 1 && gq.sum() == 8, "copy from temporary");
static_assert(gr.v == 1, "list-initialized");

int main()
{
  constexpr int b[] = {4, 5};
  static_assert(b[1] == 5, "block-scope array");
  int x = arr[2] + gp.v;
  __CPROVER_assert(x == 45, "run-time reads");
  __CPROVER_assert(x == 46, "WRONG (must FAIL)");
}
