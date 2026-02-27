// No quantifiers: --refine-quantifiers should be a no-op.
int main() {
  int x;
  __CPROVER_assume(x >= 0 && x <= 10);
  __CPROVER_assert(x <= 10, "simple bound");
}
