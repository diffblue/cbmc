// Test case for _Generic with array typedef
// This should reproduce the issue from GitHub issue #8243

typedef struct m_string_s
{
  int s, a;
  char *ptr;
} m_string_t[1];

#define TEST_GENERIC(x)                                                        \
  _Generic((x), struct m_string_s * : 42, int : 1, float : 2, default : 99)

int main(void)
{
  m_string_t s; // Array type that should decay to pointer
  int i = 5;
  float f = 3.14f;
  char c = 'x';

  // Compile-time checks: regression/ansi-c runs under goto-cc, which only
  // compiles, so a wrong _Generic selection must be turned into a translation
  // error via _Static_assert rather than a run-time assert that is never
  // evaluated.

  // The array typedef must decay to a pointer and match `struct m_string_s *`.
  _Static_assert(TEST_GENERIC(s) == 42, "array typedef decays to pointer");

  // Other types match as expected.
  _Static_assert(TEST_GENERIC(i) == 1, "int");
  _Static_assert(TEST_GENERIC(f) == 2, "float");
  _Static_assert(TEST_GENERIC(c) == 99, "char falls to default");

  (void)s;
  (void)i;
  (void)f;
  (void)c;
  return 0;
}
