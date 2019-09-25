public class Main {
    public void replace() {
        String str = "abded";
        str = str.replace('d', 'c');
        assert str.equals("abcec");
    }

    public void notEqualsReplace() {
        String str = "abded";
        str = str.replace('d', 'c');
        assert !str.equals("abdec");
    }

    public void noReplace() {
        String str = "abcde";
        str = str.replace('z', 'c');
        assert str.equals("abcde");
    }

    public void randomCharReplace(char b) {
        String str = "abcde";
        str = str.replace('a', b);
        assert str.equals("abcde");
    }

    public void randomCharsReplace(char a, char b) {
        String str = "abcde";
        str = str.replace(a, b);
        assert str.equals("abcde");
    }

    public void nopropReplace(String str) {
        str = str.replace('d', 'c');
        assert str.equals("abcec");
    }

    public void stringReplace() {
        String str = "abded";
        str = str.replace("d", "c");
        assert str.equals("abcec");
    }

    public void stringNoReplace() {
        String str = "abded";
        str = str.replace("f", "c");
        assert str.equals("abded");
    }

    public void stringSmallerReplace() {
        String str = "abded";
        str = str.replace("ab", "f");
        assert str.equals("fded");
    }

    public void stringLargerReplace() {
        String str = "abded";
        str = str.replace("ab", "fghj");
        assert str.equals("fghjded");
    }

    public void stringMultiReplace() {
        String str = "abcdab";
        str = str.replace("ab", "gh");
        assert str.equals("ghcdgh");
    }

    public void stringMultiSmallerReplace() {
        String str = "abcdabcd";
        str = str.replace("ab", "z");
        assert str.equals("zcdzcd");
    }

    public void stringMultiLargerReplace() {
        String str = "abcdabcd";
        str = str.replace("ab", "zack");
        assert str.equals("zackcdzackcd");
    }

    public void stringFullReplace() {
        String str = "abcde";
        str = str.replace("abcde", "ttttt");
        assert str.equals("ttttt");
    }

    public void fullReplace() {
        String str = "aaaa";
        str = str.replace('a', 'f');
        assert str.equals("ffff");
    }
}
