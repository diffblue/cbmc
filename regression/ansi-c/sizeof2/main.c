// sizeof is unsigned
_Static_assert( 1 - sizeof(int) >=0, "sizeof is unsigned" );

// same with cast to signed
_Static_assert( 1 - (int)sizeof(int) <0, "int is signed" );

// the size of sizeof!
_Static_assert(sizeof(sizeof(int)) == sizeof(void *), "size of sizeof" );

int main()
{
}
