struct A
{
	int a;
	A operator++(int zero)
	{
		A obj(*this);
		a++;
		return obj;
	}

	A& operator++()
	{
		a++;
		return *this;
	}

	A operator--(int zero)
	{
		A obj(*this);
		a--;
		return obj;
	}

	A& operator--()
	{
		a--;
		return *this;
	}
};

int main()
{
	A obj;
	obj.a = 0;
	A obj2 = obj++;
	assert(obj2.a == 0 && obj.a==1);
	obj2 = ++obj;
	assert(obj2.a == 2 && obj.a==2);
	obj2 = obj--;
	assert(obj2.a == 2 && obj.a==1);
	obj2 = --obj;
	assert(obj2.a == 0  && obj.a==0);
}
