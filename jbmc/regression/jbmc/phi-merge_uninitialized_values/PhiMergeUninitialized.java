public class PhiMergeUninitialized {

    public int dynamicAllocationUninitialized(Boolean trigger) {

        Ephemeral obj;
        if (trigger) {
            obj = new Ephemeral(42);
        } else {
            obj = new Aetherial(20);
        }

        assert obj.val == 20;
        return obj.val;
    }

    private Ephemeral field;

    public int fieldUninitialized(Boolean trigger) {
        if (trigger) {
            field = new Ephemeral(42);
        }

        assert field.val == 42;
        return field.val;
    }

    private static Ephemeral staticField;

    public int staticFieldUninitialized(Boolean trigger) {
        if (trigger) {
            staticField = new Ephemeral(42);
        } else {
            staticField = new Aetherial(76);
        }

        assert staticField.val == 76;
        return staticField.val;
    }

    class Ephemeral {
        Ephemeral(int value) {
            val = value;
        }

        int val;
    }

    class Aetherial extends Ephemeral {
        Aetherial(int value) {
            super(value);
        }
    }
}

