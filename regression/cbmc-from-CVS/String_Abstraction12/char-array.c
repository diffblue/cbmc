int main(int argc, char* argv[]) {
  char dest[10];
  
  __CPROVER_assert(__CPROVER_buffer_size(dest) == 10, "CBMC failed to track char array size");
  dest[9] = '\0';
  __CPROVER_assert(__CPROVER_is_zero_string(dest), "CBMC failed to track char array (2)");

  return 0;
}

