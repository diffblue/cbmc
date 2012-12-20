int main()
{
	const char c = 'c';
	const int &i = c;
	assert(i == 'c');
}
