#include <assert.h>

enum hex
{
  V1 = 0x1,
  V10 = 0xA,
  V11 = 11
};

int main()
{
  enum hex h = V10;
  assert(0xca == (unsigned char)(char)0b11001010);
}
