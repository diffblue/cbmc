void * malloc(unsigned);

void use_str(char * s) {
  assert(__CPROVER_is_zero_string(s)); 
}

int main(int argc, char* argv[]) {
  unsigned short len;
  char * str;
  __CPROVER_assume(len > 0);
  str = malloc(len);
  __CPROVER_assume(__CPROVER_buffer_size(str) == len);
  str[len - 1] = '\0';
  // string abstraction takes care of this
  // __CPROVER_is_zero_string(str) = 1;
  // __CPROVER_zero_string_length(str) = len - 1;
  use_str(str);
  return 0;
}
