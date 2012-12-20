int main()
{
	int i = 10;
	const int& ri = i;
	const_cast<int&>(ri) = 11;
	assert(i == 11);

	const int* pi = &i;
	*const_cast<int*>(pi) = 12;
	assert(i==12);
}
