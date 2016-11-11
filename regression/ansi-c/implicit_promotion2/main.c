#include <inttypes.h>
#include <stdio.h>

int main() {
	unsigned int u=1023;
	unsigned char c=3;
	unsigned long l=1024L*1024L*1024L*1024L*1024L - 1L;
	unsigned long d=l;

	d&=u; // fine, no negation

	d&=c; // fine, no negation

	d&=~u; // dangerous, u<d, negation

	d&=~c; // dangerous, c<d, negation

	u&=d; // fine, u<d

	c&=d; // fine, c<d

	c&=1024L*1024L*1024L*1024L*1024L - 1L; // fine, c < constant

	c&=~d; // fine, c < d

	c&=~1024L*1024L*1024L*1024L*1024L - 1L; // fine, c < constant

	d&=1; // fine, constant

	d=l & 1; // fine, no negation

	d=l & c; // fine, no negation

	d=d & ~1; // dangerous, d>1 and negation

	d=~d & 1; // fine, d>1, but negation on greater bit width

	d=(l&=~u); // dangerous, l>u and negation

	d=(u&=~l); // fine, u < l

	d=(l & ~u); // dangerous, l>u and negation

	d=(u & ~l); // fine, u < l, i.e. ~ on greater bit width

	d=(l&=u); // fine, no negation

	d=(u&=l); // fine, no negation

	d=(~5 & l); // dangerous, negation and 5<l

	d=(~5L & u); // fine, negation on constant, 5L > u, and negation on higher bit width

	return 0;
}
