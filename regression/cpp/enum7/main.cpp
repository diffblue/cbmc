// Visual Studio permits forward enum tags,
// whereas g++ and clang don't

#ifdef _MSC_VER

enum E1;

E1 some_global_enum; // works!

#endif

int main()
{
}
