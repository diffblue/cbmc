// C++17 byte-like scoped enum
enum class byte : unsigned char
{
};
int main()
{
  byte b = static_cast<byte>(0x0F);
  __CPROVER_assert(static_cast<unsigned char>(b) == 15, "byte value");
  return 0;
}
