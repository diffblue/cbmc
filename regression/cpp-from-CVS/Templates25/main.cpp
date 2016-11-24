template <class, int>
bool True(){return true;}

int main()
{
	assert(True<int, 0>()==true);
}
