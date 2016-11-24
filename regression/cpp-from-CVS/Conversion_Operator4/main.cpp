struct A
{
	static const int* const i = 0;
	operator const int* const ()const
	{
		return i;
	}
};

int main()
{
	A a;
	assert((const int* const)a == A::i);
}
