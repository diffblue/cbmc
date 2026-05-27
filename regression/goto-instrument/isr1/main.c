volatile int flag;
void isr(void) { flag = 1; }
int main() { return flag; }
