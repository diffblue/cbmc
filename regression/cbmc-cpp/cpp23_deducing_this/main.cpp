// C++23 deducing this — verify parsing of explicit object parameter
struct S
{
  int x;
  // Explicit object parameter: parsed, not called via member syntax
  int get(this S self)
  {
    return self.x;
  }
};

int main()
{
  // Don't call get() via member syntax (would need type-checker support)
  // Just verify the declaration parses
  __CPROVER_assert(1, "deducing this parses");
  return 0;
}
