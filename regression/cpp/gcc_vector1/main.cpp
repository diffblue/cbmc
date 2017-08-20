#ifdef __GNUC__

typedef float __m128 __attribute__ ((__vector_size__ (16), __may_alias__));

__m128 setzero(void)
{
  return (__m128){ 0.0f, 0.0f, 0.0f, 0.0f };
}

#else

void setzero()
{
}

#endif

int main(int argc, char* argv[])
{
  setzero();
  return 0;
}
