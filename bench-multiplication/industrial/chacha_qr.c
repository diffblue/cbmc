#include <stdint.h>
#define ROTL(x,n) (((x)<<(n))|((x)>>(32-(n))))
void quarter_round(uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d) {
  *a += *b; *d ^= *a; *d = ROTL(*d, 16);
  *c += *d; *b ^= *c; *b = ROTL(*b, 12);
  *a += *b; *d ^= *a; *d = ROTL(*d, 8);
  *c += *d; *b ^= *c; *b = ROTL(*b, 7);
}
int main() {
  uint32_t a,b,c,d, a2,b2,c2,d2;
  a2=a; b2=b; c2=c; d2=d;
  quarter_round(&a,&b,&c,&d);
  quarter_round(&a2,&b2,&c2,&d2);
  __CPROVER_assert(a==a2 && b==b2 && c==c2 && d==d2, "deterministic");
}
