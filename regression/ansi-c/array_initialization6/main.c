// an array that is larger than MAX_FLATTENED_ARRAY_SIZE
static const unsigned char data[256 * 4] = {0x0, 0x0};

int main()
{
  return data[0];
}
