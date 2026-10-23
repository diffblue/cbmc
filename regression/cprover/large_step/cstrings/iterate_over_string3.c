#define size_t __CPROVER_size_t
#define false 0

_Bool compare(
  const void *const array,
  const size_t array_len,
  const char *const c_str)
{
  //  const unsigned char *array_bytes = array;
  const unsigned char *str_bytes = (const unsigned char *)c_str;

  // jointly iterate over string and array
  for(size_t i = 0; i < array_len; ++i)
    __CPROVER_loop_invariant(__CPROVER_is_cstring(str_bytes + i))
    {
      unsigned char s = str_bytes[i];
      if(s == '\0')
      {
        return false;
      }

      //    if (array_bytes[i] != s) {
      //        return false;
      //    }
    }

  //return str_bytes[array_len] == '\0';
}

int main()
{
  unsigned char array[10];
  size_t array_len = 10;
  const char *c_str;
  __CPROVER_assume(__CPROVER_is_cstring(c_str));
  compare(array, array_len, c_str);
}
