#include <stdio.h>

#include <inttypes.h>


int main() {

	uint32_t a=0;
	uint64_t b=1024L;
	b=b * b * b * b + 1023;

	printf("a=%u b=%lu\n", a, b);
	b=b & ~a;
	printf("a=%u b=%lu\n", a, b);

	uint16_t c=0;
	uint32_t d=256 * 256 + 127;

	printf("c=%u d=%u\n", c, d);
	d=d & ~c;
	printf("c=%u d=%u\n", c, d);

	uint64_t e=3;
	unsigned __int128 f=1024;
	f=f * f * f * f; // >32bit
	f=f * f;         // >64bit

	printf("e=%lu f=hi:%lu lo:%lu\n", e, (uint64_t)(f >> 64), (uint64_t)f);
	f=f & ~e;
	printf("e=%lu f=hi:%lu lo:%lu\n", e, (uint64_t)(f >> 64), (uint64_t)f);
	return 0;
}
