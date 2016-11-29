typedef struct some_struct
{
  union some_union {
    struct inner_struct {
      int one;
    }; // anonymous member
    long two;
  } three;
} num_t;

int main()
{
  num_t num1 = { 0 };
  num_t num2 = { .three = 0 };
  num_t num4 = { .three = { 0 } };
  num_t num3 = { .three = { .two = 0 } };
}
