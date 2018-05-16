import java.nio.file.Files;
import java.nio.file.Paths;

import org.objectweb.asm.*;
public class SwapDump implements Opcodes {

public static byte[] dump () throws Exception {

ClassWriter cw = new ClassWriter(0);
FieldVisitor fv;
MethodVisitor mv;

cw.visit(52, ACC_PUBLIC + ACC_SUPER, "Swap", null, "java/lang/Object", null);

cw.visitSource("Swap.java", null);

{
fv = cw.visitField(ACC_FINAL + ACC_STATIC + ACC_SYNTHETIC, "$assertionsDisabled", "Z", null, null);
fv.visitEnd();
}
{
mv = cw.visitMethod(ACC_STATIC, "<clinit>", "()V", null, null);
mv.visitCode();
Label l0 = new Label();
mv.visitLabel(l0);
mv.visitLineNumber(1, l0);
mv.visitLdcInsn(Type.getType("LSwap;"));
mv.visitMethodInsn(INVOKEVIRTUAL, "java/lang/Class", "desiredAssertionStatus", "()Z", false);
Label l1 = new Label();
mv.visitJumpInsn(IFNE, l1);
mv.visitInsn(ICONST_1);
Label l2 = new Label();
mv.visitJumpInsn(GOTO, l2);
mv.visitLabel(l1);
mv.visitFrame(Opcodes.F_SAME, 0, null, 0, null);
mv.visitInsn(ICONST_0);
mv.visitLabel(l2);
mv.visitFrame(Opcodes.F_SAME1, 0, null, 1, new Object[] {Opcodes.INTEGER});
mv.visitFieldInsn(PUTSTATIC, "Swap", "$assertionsDisabled", "Z");
mv.visitInsn(RETURN);
mv.visitMaxs(1, 0);
mv.visitEnd();
}
{
mv = cw.visitMethod(ACC_PUBLIC, "<init>", "()V", null, null);
mv.visitCode();
Label l0 = new Label();
mv.visitLabel(l0);
mv.visitLineNumber(1, l0);
mv.visitVarInsn(ALOAD, 0);
mv.visitMethodInsn(INVOKESPECIAL, "java/lang/Object", "<init>", "()V", false);
mv.visitInsn(RETURN);
Label l1 = new Label();
mv.visitLabel(l1);
mv.visitLocalVariable("this", "LSwap;", null, l0, l1, 0);
mv.visitMaxs(1, 1);
mv.visitEnd();
}
{
mv = cw.visitMethod(ACC_PUBLIC + ACC_STATIC, "main", "([Ljava/lang/String;)V", null, null);
mv.visitCode();
Label l0 = new Label();
mv.visitLabel(l0);
mv.visitLineNumber(3, l0);
mv.visitInsn(ICONST_5);
mv.visitVarInsn(ISTORE, 1);
Label l1 = new Label();
mv.visitLabel(l1);
mv.visitLineNumber(4, l1);
mv.visitVarInsn(ILOAD, 1);
mv.visitInsn(ICONST_2);
mv.visitInsn(SWAP); // Manually added
mv.visitInsn(ISUB);
mv.visitVarInsn(ISTORE, 2);
Label l2 = new Label();
mv.visitLabel(l2);
mv.visitLineNumber(5, l2);
mv.visitFieldInsn(GETSTATIC, "Swap", "$assertionsDisabled", "Z");
Label l3 = new Label();
mv.visitJumpInsn(IFNE, l3);
mv.visitVarInsn(ILOAD, 2);
mv.visitIntInsn(BIPUSH, -3);
mv.visitJumpInsn(IF_ICMPEQ, l3);
mv.visitTypeInsn(NEW, "java/lang/AssertionError");
mv.visitInsn(DUP);
mv.visitMethodInsn(INVOKESPECIAL, "java/lang/AssertionError", "<init>", "()V", false);
mv.visitInsn(ATHROW);
mv.visitLabel(l3);
mv.visitLineNumber(6, l3);
mv.visitFrame(Opcodes.F_APPEND,2, new Object[] {Opcodes.INTEGER, Opcodes.INTEGER}, 0, null);
mv.visitInsn(RETURN);
Label l4 = new Label();
mv.visitLabel(l4);
mv.visitLocalVariable("args", "[Ljava/lang/String;", null, l0, l4, 0);
mv.visitLocalVariable("x", "I", null, l1, l4, 1);
mv.visitLocalVariable("result", "I", null, l2, l4, 2);
mv.visitMaxs(2, 3);
mv.visitEnd();
}
cw.visitEnd();

return cw.toByteArray();
}

public static void main(String[] args) throws Exception {
  Files.write(Paths.get("Swap.class"), dump());
}
}
