template <class T>
struct A
{
	T i;
};


template <class T>
T  get_i(const A<T> a1)
{
	return a1.i;
}


int main()
{
	A<int> a2;
	a2.i = 10;
	assert (a2.i == 10);
	assert(get_i<int>(a2) == 10);
	get_i<int>(a2);
}
