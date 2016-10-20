int main(void)
{
  enum enum_tag { A = 2 };

  {
     enum enum_tag { A = 3 };
  }
}
