int main(int argc, char **argv)
{
  // There is no guarantee that there is at least one, so this
  // program is not memory safe.
  int n;

  for(n = 1; n < argc; n++)
  {
    // nothing
  }

  char *path = argv[n]; // out-of-bounds when argc == 0
}
