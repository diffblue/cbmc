struct A {
	 int* pi;
	
};

int main()
{
	A a;
	const A* cpa = &a;
	
	int* ptr = reinterpret_cast<int*>(cpa->pi);

	return 0;
	
}
