extern "C" void __CPROVER_assert(bool, const char *);
struct bits {
  unsigned a : 1;
  unsigned b : 31;
};
struct rec {
  unsigned a;
  unsigned b;
};
struct with_default {
  int x = 3;
  int y;
};
struct user_ctor {
  int z;
  user_ctor() : z(5) {}
};
int by_value(rec r) { return r.a + r.b; }
int by_reference(const rec &r) { return r.a + r.b; }
int main() {
  bits s;
  s.a = 1;
  s = {};
  __CPROVER_assert(s.a == 0 && s.b == 0, "bit-fields");
  rec t;
  t.b = 7;
  t = {};
  __CPROVER_assert(t.a == 0 && t.b == 0, "members");
  with_default w;
  w.x = 1;
  w.y = 1;
  w = {};
  __CPROVER_assert(w.x == 3 && w.y == 0, "default member initializer");
  user_ctor u;
  u.z = 1;
  u = {};
  __CPROVER_assert(u.z == 5, "user-provided constructor");
  __CPROVER_assert(by_value({}) == 0, "argument");
  __CPROVER_assert(by_reference({}) == 0, "reference argument");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
