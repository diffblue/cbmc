typedef struct {
    int field;
} MyStruct;


void f(MyStruct *s)
{
    int y = s->field;
}

int main() {
	MyStruct s;

	f(&s);
}
