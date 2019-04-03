public class IntToX {
    public void shortCast(int arg) {
        intMethod((byte)arg);
        assert true;
    }

    public void byteCast(int arg) {
        intMethod((short)arg);
        assert true;
    }

    public void charCast(int arg) {
        intMethod((char)arg);
        assert true;
    }

    public void floatCast(int arg) {
        floatMethod((float)arg);
        assert true;
    }

    public float floatMethod(float f) {
        return f;
    }

    public void longCast(int arg) {
        longMethod((long)arg);
        assert true;
    }

    public float longMethod(long f) {
        return f;
    }

    public void doubleCast(int arg) {
        doubleMethod((double)arg);
        assert true;
    }

    public double doubleMethod(double f) {
        return f;
    }

    public int intMethod(int i) {
        return i;
    }
}
