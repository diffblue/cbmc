struct A
{
	int i;
	A():i(1){}
	
	int& operator* () {return i;}
	int operator+ (int j){return i+j;}
	int operator~ (){return ~i;}
	int operator[] (int k){return i;}
	int operator== (int k){return i=i;}

	void func1()
	{
		A a;
		assert(*a == 1);
		assert(*a + 1 == 2);
		assert(~a == ~1);
		assert(a[2] == *a);
		assert(a == 1);
	}
	
	void func2()
	{
		A a;
		assert((*this) == 1);
		assert((*this) + 1 == 2);
		assert(~(*this) == ~1);
		assert((*this)[2] == *(*this));
		assert((*this) == 1);
	}
		
};


int main()
{
	A o;
	assert(*o == 1);
	assert(*o + 1 == 2);
	assert(~o == ~1);
	assert(o[2] == *o);
	assert(o == 1);

	o.func1();
	o.func2();
}
