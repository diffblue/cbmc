public class generic_field_array_instantiation {

    class generic<T> {
        T gf;
    }

    class genericArray<T> {
        T [] arrayField;
    }

    generic<Float []> f;

    Float [] af;

    genericArray<Float> genericArrayField;
}


