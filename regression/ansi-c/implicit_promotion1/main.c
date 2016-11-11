#include <inttypes.h>
#include <stdio.h>

#define G (1024L*1024L*1024L*1024L)

void broken(unsigned int a, unsigned long b, unsigned long c ) {
	if( a != 2 && a != 4 && a != 8 ) return;
	if ( a == 2 )
		b = (int16_t)b;
	else if ( a == 4 )
		b = (int32_t)b;
	if( (long)b < 0 ) {
		unsigned long d;
		// here, we would like to have some warning like
		// increasing bit width automatically before applying "~" operator
		d = a + (((-b-1) >> 3) & ~(a-1));
		c -= d;
		b = (d << 3) + b;
	} else {
		// increasing bit width automatically before applying "~" operator
		c += (b >> 3) & ~(a - 1);
		b &= (a << 3) - 1;
	}
	printf("b: %ld c: %ld\n", b, c);
}

void fixed(unsigned int a, unsigned long b, unsigned long c ) {
	if( a != 2 && a != 4 && a != 8 ) return;
	if ( a == 2 )
		b = (int16_t)b;
	else if ( a == 4 )
		b = (int32_t)b;
	if( (long)b < 0 ) {
		unsigned long d;
		// the problem is that the 1 (i.e. not 1L) turned the later operand
		// into a 32bit value first, and then the ~ operator turns this
		// back into 64, with many leading 0bits, which are then flipped
		// to 1, and successfully pass the & operator.
		// combinations we might want to look for are hence:
		// (bigger_t) & ~(bigger_t vs smaller_t)
		// but basically, any ~ together with a silent cast looks weird
		d = a + (((-b-1) >> 3) & ~(a-1L));
		c -= d;
		b = (d << 3) + b;
	} else {
		c += (b >> 3) & ~(a - 1L);
		b &= (a << 3) - 1;
	}
	printf("b: %ld c: %ld\n", b, c);
}

void test(unsigned int a, unsigned long b, unsigned long c) {
	printf("broken for %u,%lu,%lu\n",a,b,c);
	broken(a, b, c);
	printf("  and fixed:\n");
	fixed(a,b,c);
}

int main() {
	test(8, G+1023L, 0);
	test(8, -G-1023L, 0);
	return 0;
}
