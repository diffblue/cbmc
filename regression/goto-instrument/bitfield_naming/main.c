typedef struct {
  unsigned char b11 : 1;
  unsigned char b22 : 1;
  unsigned char b34 : 2;
  unsigned char b58 : 4;
} bf_t;

typedef union {
  unsigned char val;
  bf_t bf;
} union_bf_t;

int main(void)
{
  union_bf_t bf;
  bf.bf.b11 = 1;
  return 0;
}
