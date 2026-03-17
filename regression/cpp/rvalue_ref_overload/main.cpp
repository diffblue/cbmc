struct S
{
  void move(S &);
  void move(S &&);
};

int main()
{
  S s;
  S s2;
  s.move(s2);
  s.move(static_cast<S &&>(s2));
}
