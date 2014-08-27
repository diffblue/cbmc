typedef struct some_struct
{
  union some_union {
    struct inner_struct {
      int one;
    };
    long two;
  } three;
} num_t;
 
int main()
{
  num_t num = {0};
}
