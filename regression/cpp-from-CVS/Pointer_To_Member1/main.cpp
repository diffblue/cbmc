class A
{
	public:
	int f(char i){return i+1;}
};

A a;
int (A::* paf)(char) = &A::f;
int main()
{
	int v1 = (a.*paf)(0);
	int v2 = ((&a)->*paf)(1);

	assert(v1 == 1);
	assert(v2 == 2);
}
