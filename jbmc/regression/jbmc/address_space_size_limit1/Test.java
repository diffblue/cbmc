public class Test {
    int x;
    Test(int x) { this.x = x; }

    public static void main(String[] args) {
        int i;
        Test[] tests = new Test[30];
        for(i = 0; i < 30; ++i) {
            tests[i] = new Test(i);
        }
        assert i == tests[0].x;
    }
}
