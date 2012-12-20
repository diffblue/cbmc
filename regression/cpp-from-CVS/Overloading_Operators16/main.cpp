class module_name
{
  public:
      operator const char*() ;
      operator int();
      operator char();
      operator long long();
      operator unsigned int();
      operator bool();
};
 
void f (module_name name) {
    (const char*) name;
    name .operator const char *();
    name .operator int();
    name .operator char();
    name .operator bool();
    name.operator unsigned int();
    name.operator long long();
}

int main(int argc, char* argv[])
{
}
