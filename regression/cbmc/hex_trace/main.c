int main()
{
	int a;
	unsigned int b;
	a = 0;
	a = -100;
	a = 2147483647;
	b = a*2;
	a = -2147483647;
	__CPROVER_assert(0,"");

}
