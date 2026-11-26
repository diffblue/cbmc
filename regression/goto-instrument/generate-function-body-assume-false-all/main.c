void undef(void);
void undef_via_pointer(void);
int nondet(void);

int main(void)
{
  // calls that are jump targets: the first instructions of the branches of an
  // if, and the calls that remove_function_pointers produces
  if(nondet())
    undef();
  else
    undef();

  void (*fp)(void) = nondet() ? undef : undef_via_pointer;
  fp();

  __CPROVER_assert(0, "unreachable");
  return 0;
}
