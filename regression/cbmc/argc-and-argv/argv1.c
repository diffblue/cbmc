int main(int main_argc, char **main_argv)
{
  char *x;

  // there is no guarantee that there is at least one,
  // but note that argv is NULL-terminated
  x = main_argv[0];
  assert(main_argc >= 0);

  // last one must be NULL
  assert(main_argv[main_argc] == 0);
}
