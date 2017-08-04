typedef unsigned char u1;
typedef unsigned short u2;
typedef unsigned long long u4;

// Not resolved (as expected)
u4 B[( (u1)( ( (u1)15 ) / ( ( (((sizeof(u4))/(sizeof(u1)))*((u1)15)) > ((u1)64)) ? (0) : (1) ) ) )];

// Correctly resolved
u2 C[( (u1)( ( (u1)11 ) / ( ( (((sizeof(u2))/(sizeof(u1)))*((u1)11)) > ((u1)64)) ? (0) : (1) ) ) )];

int main()
{
  // Correctly resolved
  u2 A[( (u1)( ( (u1)1 ) / ( ( (((sizeof(u2))/(sizeof(u1)))*((u1)1)) > ((u1)64)) ? (0) : (1) ) ) )];

  // Correctly resolved
  static u4 D[( (u1)( ( (u1)4 ) / ( ( (((sizeof(u4))/(sizeof(u1)))*((u1)4)) > ((u1)64)) ? (0) : (1) ) ) )];

  return 0;
}
