int g;
class A {
	public:
	A(int i){g=i;};
	private:
	A();
};

class B: A {
	public:
	typedef A base_type;
	typedef B this_type;
	B():base_type(10){}
	B(const this_type& b): A(20) {g++;}
};

class C: B
{
	typedef B base_type;
	typedef C this_type;
	public:
	C(): base_type(){}
	C(const base_type& b): base_type(b){g++;}
};


C c;

int main()
{
	assert(g==10);
	B b;
	C c2 = b;
	assert(g==22);
}
