class A
{
	public:
	int f(){return 1;}
};

int main()
{
	int (A::* paf)() = &A::f;
	A a;
	(*paf)(&a); // ill-formed
}
