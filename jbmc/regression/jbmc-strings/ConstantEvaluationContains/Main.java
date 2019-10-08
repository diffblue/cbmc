public class Main {
    public void contains() {
        String str = "abcde";
        assert str.contains("cd");
    }

    public void doesntContain() {
        String str = "abcde";
        assert !str.contains("cda");
    }

    public void noprop(String str) {
        assert str.contains("cd");
    }

    public void nondetArg(String str) {
        assert "dave".contains(str);
    }

    public void noPi() {
        assert !"dave".contains("π");
    }

    public void pi() {
        assert "dave_loves_π".contains("π");
    }

    public void alphanumeric() {
        assert "ad672naksd3".contains("72n");
    }
}
