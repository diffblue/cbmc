// array size greater than MAX_FLATTENED_ARRAY_SIZE
static unsigned char buffer[10000] = {0};

int main()
{
  __CPROVER_assert(buffer[0] == 0, "");
}
