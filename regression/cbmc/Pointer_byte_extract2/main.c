// from SV-COMP bitvector-regression/pointer_extension_{true,false}.i

int main() {
  char t = 50;
  char* z1 = &t;
  void* z2 = z1;
  unsigned int* pi = z2;

  assert(((char)*pi) == 50);
  assert(*pi == 50);

  return 0;
}
