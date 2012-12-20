bool f(const char *){return true;}
bool f(int){return false;}

int main()
{
	assert(f("hello"));
}
