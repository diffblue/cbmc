/* FUNCTION: sleep */

unsigned nondet_uint();

unsigned int sleep(unsigned int seconds)
{
  // do nothing, but return nondet value
  unsigned remaining_time=nondet_uint();
  
  if(remaining_time>seconds) remaining_time=seconds;
  
  return remaining_time;
}

/* FUNCTION: unlink */

void unlink(const char *s)
{
  __CPROVER_hide:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(s), "unlink zero-termination");
  #endif
}

