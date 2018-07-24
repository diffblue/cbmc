int function_to_call(int a)
{
	int local = 1;
	return a+local;
}


int main()
{
	int a, c;
	unsigned int b;
	a = 0;
	c = -100;
	a = function_to_call(a) + function_to_call(c);
	if(a < 0)
	  b = function_to_call(b);

	if(c < 0)
	  b = -function_to_call(b);

	__CPROVER_assert(0,"");

}
