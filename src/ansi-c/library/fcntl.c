/* FUNCTION: fcntl */

int __VERIFIER_nondet_int();

int fcntl(int fd, int cmd, ...)
{
__CPROVER_HIDE:;
  int return_value=__VERIFIER_nondet_int();
  (void)fd;
  (void)cmd;
  return return_value;
}
