void * malloc(unsigned);

typedef struct str_struct {
  int a;
  char * str;
  char * str2;
} str_struct_t;

str_struct_t * foo() {
  str_struct_t * retval;
  retval = malloc(sizeof(str_struct_t));
  retval->str = malloc(2);
  retval->str[1] = 0;
  __CPROVER_is_zero_string(retval->str) = 1;
  return retval;
}

int main() {
  str_struct_t * a;
  a = foo();
  __CPROVER_assert(__CPROVER_is_zero_string(a->str), "CBMC failed to track struct");
  // __CPROVER_assert(__CPROVER_is_zero_string(a->str2), "CBMC failed to track struct");
}
