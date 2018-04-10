class params {

    void blub(int a, int b) {
    }

    void log(String x) {
    }

    int f0(int a, int b) {
        try {
            {
                int x = a;
                int y = b;
                int z = x;
                blub(x, y);
            }
            {
                int x = b;
                int y = a;
                blub(x, y);
            }
            return -1;
        }
        catch(Exception e) {
            String s = "foo";
            log(s);
            return 0;
        }
    }
}
