class B;

template <class T>
struct A {
	int get_i(B& b);
};

class B {
	int i;
	public:
	B():i(10){};
	friend class A<int>;
};

template<class T>
int A<T>::get_i(B& b){return b.i;} 

int main()
{
	B b;
	A<int> a;
	assert(a.get_i(b)==10);
}
