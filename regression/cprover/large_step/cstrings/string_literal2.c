const char *HEX_CHARS = "0123456789abcdef";

int main()
{
  unsigned char input;
  char output;

  output = HEX_CHARS[input & 0xf];

  return 0;
}
