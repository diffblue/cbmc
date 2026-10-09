// C++11 static_assert with message
static_assert(sizeof(int) >= 4, "int must be at least 4 bytes");
// C++17 static_assert without message
static_assert(sizeof(int) >= 4);
int main()
{
  return 0;
}
