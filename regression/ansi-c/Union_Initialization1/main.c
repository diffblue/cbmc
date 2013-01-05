typedef struct
{
  union {
    struct {
      int one;
    };
    long two;
  } three;
} num_t;
 
int main()
{
  num_t num = {0};
}
