// [expr.prim.lambda.capture] / [expr.prim.lambda.closure]: `[this]` (and a
// capture-default that odr-uses members) captures the enclosing object by
// reference -- member odr-uses denote the live object and may modify it;
// `[*this]` (C++17) captures the enclosing object by copy -- a snapshot taken
// at capture time.

struct Counter
{
  int v;

  Counter(int start) : v(start) {}

  // [this]: member access is by reference (the live object)
  int peek_via_this() const
  {
    auto f = [this]() { return v; };
    return f();
  }

  // [this]: modify the live object through the lambda
  void bump(int by)
  {
    auto f = [this](int n) { v += n; };
    f(by);
  }

  // [=] in a member: members are captured by reference (this by reference)
  int peek_via_eq() const
  {
    auto f = [=]() { return v; };
    return f();
  }

  // [*this]: by-copy snapshot of the object at capture time
  int snapshot_then_change()
  {
    auto f = [*this]() { return v; };
    v = 999; // does not affect the [*this] snapshot
    return f();
  }
};

int main()
{
  Counter c(10);
  __CPROVER_assert(c.peek_via_this() == 10, "[this] reads the live member");
  __CPROVER_assert(c.peek_via_eq() == 10, "[=] in member reads the live member");

  c.bump(5);
  __CPROVER_assert(c.v == 15, "[this] modifies the live member");
  __CPROVER_assert(c.peek_via_this() == 15, "[this] observes the update");

  Counter d(10);
  __CPROVER_assert(
    d.snapshot_then_change() == 10, "[*this] snapshots at capture time");
  return 0;
}
