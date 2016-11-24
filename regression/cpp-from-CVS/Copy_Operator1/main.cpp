class A
{
	public:
	int ar[2];
	A& operator=(const A& ref)
	{
		ar[0] = ref.ar[1];
		ar[1] = ref.ar[0];
		return *this;
	}

};

int main()
{
	A a1;
	a1.ar[0]= 1;
	a1.ar[1]= 2;

	A a2;
	a2.ar[0]= 3;
	a2.ar[1]= 4;

	a2 = a1;
	assert(a2.ar[0]==a1.ar[1]);
	assert(a2.ar[1]==a1.ar[0]);
}
