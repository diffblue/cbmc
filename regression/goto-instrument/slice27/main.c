int nondet_int();
void stop(void);

int main()
{
  int i = nondet_int();
  if(i == 2)
  {
    __CPROVER_assert(i < 100, "before the call");
    // The body of stop is generated using --generate-function-body, it is
    // just ASSUME false.
    stop();
  }
  __CPROVER_assert(i != 2, "only reachable with i != 2");
  return 0;
}
