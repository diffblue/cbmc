int main(int argc, char **argv) {
  char *x;

  // there must be at least one
  x=argv[0];

  // last one must be NULL
  assert(argv[argc]==0);
}
