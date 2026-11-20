.class public B
.super A

.method public <init>()V
        aload_0
        invokespecial A/<init>()V
        return
.end method

.method public viaSuper()Ljava/lang/Class;
        .limit stack 1
        .limit locals 1
        aload_0
        invokespecial A/getClass()Ljava/lang/Class;
        areturn
.end method

; assert new B().viaSuper() == new B().getClass();
; assert new B().viaSuper() != new A().getClass();
.method public static test()V
        .limit stack 3
        .limit locals 0
        new B
        dup
        invokespecial B/<init>()V
        invokevirtual B/viaSuper()Ljava/lang/Class;
        new B
        dup
        invokespecial B/<init>()V
        invokevirtual java/lang/Object/getClass()Ljava/lang/Class;
        if_acmpne fail
        new B
        dup
        invokespecial B/<init>()V
        invokevirtual B/viaSuper()Ljava/lang/Class;
        new A
        dup
        invokespecial A/<init>()V
        invokevirtual java/lang/Object/getClass()Ljava/lang/Class;
        if_acmpeq fail
        return
fail:
        new java/lang/AssertionError
        dup
        invokespecial java/lang/AssertionError/<init>()V
        athrow
.end method
