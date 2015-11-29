int main() {
  int x = 0;
  x = ++x + x;
  // depending on the order of evaluation, the following may fail
  assert(x == 2);
  return 0;
}
