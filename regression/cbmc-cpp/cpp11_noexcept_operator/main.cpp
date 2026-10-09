// Per [expr.unary.noexcept]/3: the noexcept operator returns true if the
// operand is known not to throw, false if it is potentially-throwing.

// 1. Builtin arithmetic is noexcept
static_assert(noexcept(1 + 1), "builtin arithmetic is noexcept");

// 2. Literal is noexcept
static_assert(noexcept(true), "literal is noexcept");

// 3. Function declared noexcept
void nothrow_fn() noexcept;
static_assert(noexcept(nothrow_fn()), "noexcept function is noexcept");

// 4. Function NOT declared noexcept is potentially-throwing
void throw_fn();
static_assert(!noexcept(throw_fn()), "plain function is potentially throwing");

// 5. Destructors are implicitly noexcept since C++11 (per [except.spec]/2)
struct S
{
  int x;
};
S s;
static_assert(noexcept(s.~S()), "destructor is implicitly noexcept");

// 6. throw-expression is always potentially-throwing per [expr.unary.noexcept]
static_assert(!noexcept(throw 1), "throw-expression is not noexcept");

int main()
{
}
