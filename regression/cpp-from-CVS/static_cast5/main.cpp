struct A
{
	int i;
};

struct B:  A
{
};

int get_i1(A& a)
{
	return static_cast<B*>(&a)->i;
}

int get_i2(A* pa)
{
	return static_cast<B*>(pa)->i;
}

int main()
{
	B b;
	b.i = 10;
	int tmp1 = get_i1(b);
        assert(tmp1 == 10);

	int tmp2 = get_i2(&b);
        assert(tmp2 == 10);
}
