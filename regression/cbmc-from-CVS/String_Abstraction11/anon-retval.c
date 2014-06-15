void * malloc(unsigned);

char * foo() {
  char * a;
  a = malloc(2);
  a[1] = 0;
  __CPROVER_is_zero_string(a) = 1;
  return a;
}

int main() {
  __CPROVER_assert(__CPROVER_is_zero_string(foo()), "CBMC failed to track return value");
}
