void *malloc(__CPROVER_size_t);

// if the implementation of malloc is sound, this one should fail

int main() {
  char * a;
  a = malloc(5);
  assert(a != 0);
  return 0;
}
