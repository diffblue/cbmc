// Visual Studio does NOT have a built-in 'bool'

#ifdef _MSC_VER

typedef bool _Bool;

#else

#endif

bool some_bool;

int main()
{
}
