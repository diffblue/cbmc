class A
{
	public:
	int ar[2];
	A(){ar[0]=0; ar[1]=1;}
};

class B
{
	public:
	A as[2];
};

int main()
{
	B b1;
	b1.as[0].ar[0] += 1;
	b1.as[0].ar[1] += 1;
	b1.as[1].ar[0] += 2;
	b1.as[1].ar[1] += 2;

	B b2(b1);
	assert(b2.as[0].ar[0]== 1);
	assert(b2.as[0].ar[1] == 2);
	assert(b2.as[1].ar[0] == 2);
	assert(b2.as[1].ar[1] == 3);
}
