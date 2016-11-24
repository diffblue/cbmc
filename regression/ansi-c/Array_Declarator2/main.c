// Tests a parsing issue regarding array declarators, see Array_Declarator1

// parsing should fail, e.g., gcc says
// error: ‘[*]’ not allowed in other than function prototype scope
void fooStar(int x[*])
{
}


int main(void)
{
    return 0;
}
