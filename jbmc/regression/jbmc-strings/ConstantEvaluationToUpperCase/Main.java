public class Main {
    public void toUpper() {
        String str = "abcde";
        str = str.toUpperCase();
        assert str.equals("ABCDE");
    }

    public void noUpper() {
        String str = "abcde";
        str = str.toUpperCase();
        assert !str.equals("ABCDe");
    }

    public void noprop(String str) {
        str = str.toUpperCase();
        assert str.equals("ABCDE");
    }

    public void nondetArg(String str) {
        str = "dave".toUpperCase();
        assert !str.equals(str);
    }

    public void pi() {
        assert "π".toUpperCase().equals("π");
    }

    public void nonAlpha() {
        assert "^£&$1!".toUpperCase().equals("^£&$1!");
    }

    public void empty() {
        assert "".toLowerCase().equals("");
    }

    public void emptyThis() {
        assert !"".toUpperCase().equals("dave");
    }

    public void emptyArg() {
        assert !"dave".toUpperCase().equals("");
    }
}
