.class stack_typecast
.super java/lang/Object

.field public position I
.field public buffer [B

.method public <init>()V
        aload_0
        invokespecial java/lang/Object/<init>()V
        return
.end method

.method public f()I
        .limit stack 6
        .limit locals 1
        .var 0 is this Lstack_typecast; from begin to end
        .line 0
begin:

        sipush 255

        aload_0
        getfield stack_typecast/buffer [B

        aload_0
        dup
        getfield stack_typecast/position I
        dup_x1
        iconst_1
        iadd
        putfield stack_typecast/position I
        baload
        iand
end:
        ireturn

.end method
