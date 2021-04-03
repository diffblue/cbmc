int main(int argc, char *argv[])
{
  __CPROVER_assert(
    sizeof(char *) > sizeof(int) || argc < 0x7FFFFFFF,
    "argc cannot reach INT_MAX on 32-bit systems");
}
