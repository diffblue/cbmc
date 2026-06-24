// N5008 [class.friend]/3: a friend declaration whose type-specifier designates
// a class type declares that class as a friend.  The type may be named with a
// simple-type-specifier (no `class`/`struct` keyword): `friend B;`.  B then has
// access to A's private members (as libstdc++'s __max_size_type befriends
// __max_diff_type via `friend __max_diff_type;`).
//
// KNOWNBUG: CBMC's parser dropped the `friend B;` form (it recorded only the
// elaborated `friend class B;`), so the befriended class was denied access to
// the private member: "member 'A::secret' is not accessible (private)"
// (CONVERSION ERROR).
struct B;
struct A
{
private:
  int secret;
  friend B; // simple-type-specifier friend declaration (no keyword)

public:
  A() : secret(0) {}
  int get() const { return secret; }
};
struct B
{
  A a;
  void set(int n) { a.secret = n; } // permitted: B is a friend of A
};
int main()
{
  B b;
  b.set(42);
  __CPROVER_assert(b.a.get() == 42, "friend B (no keyword) may write A's private");
  return 0;
}
