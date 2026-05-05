package indirect;

public enum TestEnum {
    One("Luhman 16A", true),
    Two("α Centauri B", false),
    Three("α Centauri A", true),
    Four("Proxima Centauri", false);

    TestEnum(String name, boolean active) {
        this.name = name;
        this.active = active;
    }

    private String name;
    private boolean active;

    String getName() {
        return name;
    }

    boolean isActive() {
        return active;
    }
}
