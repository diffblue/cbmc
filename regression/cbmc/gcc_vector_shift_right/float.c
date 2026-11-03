typedef float f32x2 __attribute__((vector_size(8)));

int main(void)
{
  f32x2 v = {4.0f, 2.0f};
  f32x2 r = v >> 1;
  return 0;
}
