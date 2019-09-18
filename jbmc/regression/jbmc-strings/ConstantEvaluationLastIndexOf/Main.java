public class Main {
    public void lastIndexOf() {
        String str = "abcabcabc";
        assert str.lastIndexOf("b") == 7;
    }

    public void noIndex() {
        String str = "abcabcabc";
        assert str.lastIndexOf("g") == -1;
    }

    public void noprop(String str) {
        assert str.lastIndexOf("b") == 7;
    }

    public void subsetIndex() {
        String str = "abcabcabc";
        assert str.lastIndexOf("b", 5) == 4;
    }

    public void subsetNoIndex() {
        String str = "abcabcabc";
        assert str.lastIndexOf("c", 1) == -1;
    }
}

