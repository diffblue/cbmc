template <class T> struct A
{
	A(T i):i(i){};
	T i;
};

class B
{
	int get(){return i;}
	A<int> func();
	int i;
};

int main()
{
	B b;
}
