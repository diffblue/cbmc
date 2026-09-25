// C++17 direct-list-initialization of scoped enum
enum class byte : unsigned char
{
};

int main()
{
  byte b = byte{42};
  __CPROVER_assert(static_cast<int>(b) == 42, "scoped enum brace init");
  return 0;
}
