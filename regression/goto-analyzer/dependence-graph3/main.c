
struct st { int m1; int m2; };
extern struct st port;

void main(void)
{
  int t = (&port)->m1; // it is result of macro expansion.
}

