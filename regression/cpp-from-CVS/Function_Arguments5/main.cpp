bool func(const int& i){return false;}
bool func(const int* i){return true;}

int main()
{
	int k;
	int& rk = k;
	assert(!func(rk));
	assert(func(&k));
}
