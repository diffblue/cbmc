struct C {
	bool b;
	C(bool b):b(b){}
};

struct A {
	C c1;
	
	A():c1(false){}
	const C* operator->() const {return &c1;}
};

struct B : A {
	bool func() const { return (*this)->b;};
};

int main()
{
	const B b1;
	assert(b1.func() == false);
}
