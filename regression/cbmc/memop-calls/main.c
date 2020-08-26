#include<string.h>
int main()
{
	const int a[2] = {0, 0};
	int b[2];

	memcpy(a, b, 3);
	return 0;
}
