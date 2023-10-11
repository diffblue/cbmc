int main(int argc, char *argv[])
{
  // Literal 0 is a valid null-pointer constant, which makes this conditional
  // operator well-formed.
  char *maybe_str = argc > 1 ? "args" : 0;
}
