extern const char hello [];

bool func(const char* str){return true;}
bool func(char* ){return false;}

int main()
{
	assert(func(hello));
}

const char hello[] = "hello";
