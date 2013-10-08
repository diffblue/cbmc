#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

#include <inttypes.h>

#pragma pack(1)
typedef union RTFLOAT80U
{
    __extension__ struct
    {
        uint64_t u64Mantissa;
        __extension__ uint16_t uExponent : 15;
        __extension__ uint16_t fSign : 1;
    } s;

    uint64_t au64[1];
    uint32_t au32[2];
    uint16_t au16[5];
    uint8_t au8[10];
} RTFLOAT80U;
#pragma pack()

STATIC_ASSERT(sizeof(RTFLOAT80U)==10);

#include <stdio.h>

int main()
{
  printf("RTFLOAT80U: %u\n", sizeof(RTFLOAT80U));
  return 0;
}

