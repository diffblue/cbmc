package indirect;

public class IndirectVirtualCall {

    public void main() throws ClassNotFoundException, IllegalAccessException, InstantiationException {
        PrimaryInterface primary = (PrimaryInterface)Class.forName("PrimaryInstance").newInstance();
        boolean activated = primary.getState().isActive();
    }
}
