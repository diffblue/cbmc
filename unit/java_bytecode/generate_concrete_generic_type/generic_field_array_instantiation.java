public class generic_field_array_instantiation {

    class generic<T> {
        T gf;
    }

    class genericArray<T> {
        T [] arrayField;

        generic<T> genericClassField;
    }

    generic<Float []> f;
    generic<Integer []> g;
    generic<int []> h;
    generic<float []> i;
    Float [] af;

    genericArray<Float> genericArrayField;
    genericArray<Float []> genericArrayArrayField;
}
