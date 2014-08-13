// from SV-COMP bitvector-regression/pointer_extension_{true,false}.i

int main() {
  char t = 50;
  char* z1 = &t;
  void* z2 = z1;
  unsigned int* pi = z2;

  // This is probably not ok, but we shall expect it to pass anyway.
  assert(((char)*pi) == 50);

  // This should really, really fail.
  assert(*pi == 50);

  return 0;
}
