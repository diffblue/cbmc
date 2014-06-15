int main() {
  int a;
  __CPROVER_assume(a >= 4);
  while (a > 0) {
    --a;
  }

  // this one should be reported to fail, even with unwinding assertions turned
  // on (first check all other claims, then unwinding assertions)
  assert(a > 0);
  // once the above is disabled, it should be possible to "prove" this one in
  // that the unwinding assertion fails first
  assert(a <= 0);
}
