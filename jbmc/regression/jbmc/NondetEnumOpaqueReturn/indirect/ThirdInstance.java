package indirect;

public abstract class ThirdInstance implements ThirdInterface {

    public ThirdInstance() {
        val = TestEnum.Four;
    }

    private TestEnum val;

    public TestEnum getState() {
        return val;
    }
}
