int main()
{
  typedef struct onet
  {
    union {
      struct onet *next;
    } abc;
  } onet;

  typedef struct twot
  {
    union {
      struct twot *next;
    } xyz;
  } twot;
  twot two;

  two.xyz.next->xyz.next = 0;
  return 0;
}
