void *malloc(__CPROVER_size_t);

int main(int argc, char* argv[]) {
  unsigned short len;
  char * str;
  __CPROVER_assume(len > 0);
  str = malloc(len);
  __CPROVER_assert(__CPROVER_buffer_size(str) == len, "buffer size ok");
  return 0;
}
