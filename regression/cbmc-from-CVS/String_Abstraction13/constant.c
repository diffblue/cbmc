
int main() {
  char * x;
  char * y;
  char * z;
  x = (void*) 0;
  __CPROVER_assume(__CPROVER_is_zero_string(x));
  y = "bla";
  z = (char*) 0;
  __CPROVER_assume(__CPROVER_is_zero_string(z));
  assert(__CPROVER_is_zero_string(x));
  assert(__CPROVER_is_zero_string(y));
  assert(__CPROVER_is_zero_string(x));
  return 0;
}

