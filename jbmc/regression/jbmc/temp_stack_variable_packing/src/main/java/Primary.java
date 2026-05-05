public class Primary {
    private External ex = new External();

    public void Run() {
        this.ex.Accept(new int[]{0, 1, 2});
        assert(false);
    }

    public void main() {
        this.Run();
    }
}
