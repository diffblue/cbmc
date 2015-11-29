int main(int main_argc, char **main_argv)
{
  char *x;

  // there must be at least one
  x=main_argv[0];
  assert(main_argc>=1);

  // last one must be NULL
  assert(main_argv[main_argc]==0);
}
