public class Main {
    public void toLower() {
        String str = "ABCDE";
        str = str.toLowerCase();
        assert str.equals("abcde");
    }

    public void noLower() {
        String str = "ABCDE";
        str = str.toLowerCase();
        assert !str.equals("abcdE");
    }

    public void noprop(String str) {
        str = str.toLowerCase();
        assert str.equals("ABCDE");
    }

    public void nondetArg(String str) {
        str = "dave".toLowerCase();
        assert !str.equals(str);
    }

    public void pi() {
        assert "π".toLowerCase().equals("π");
    }

    public void nonAlpha() {
        assert "^£&$1!".toLowerCase().equals("^£&$1!");
    }

    public void empty() {
        assert "".toLowerCase().equals("");
    }

    public void emptyThis() {
        assert !"".toLowerCase().equals("dave");
    }

    public void emptyArg() {
        assert !"dave".toLowerCase().equals("");
    }
}
