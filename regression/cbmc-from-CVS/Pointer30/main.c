// special case of struct of size 1
typedef struct
{
  char index;
} St;

St A[2];

void main()
{
  A[1].index = 7;
  char cp = *(&(A[1].index));
  assert(cp == 7);
}
