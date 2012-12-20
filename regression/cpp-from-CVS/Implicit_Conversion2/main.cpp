char func1(const char& c)
{
	return c;
}


int main()
{
	assert(func1((char)10)==10);
	
	int i(20);
	assert(func1((char)i)==20);

}
