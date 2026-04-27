// [basic.lval] p1: derived-to-base conversion on rvalue produces xvalue.
// An xvalue can bind to an rvalue reference parameter.
#include <cassert>
struct Base {
  int val;
  Base(int v) : val(v) {}
};
struct Derived : Base {
  Derived(Base&& b) : Base(static_cast<Base&&>(b)) {}
};
Base make_base() { return Base(42); }
int main() {
  Derived d(make_base());
  assert(d.val == 42);
}
