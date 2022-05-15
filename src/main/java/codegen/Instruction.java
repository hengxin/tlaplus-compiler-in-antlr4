package codegen;

public enum Instruction {
    LDC("ldc"),
    GETSTATIC("getstatic"),
    // 将常数压入操作数栈
    SIPUSH("sipush"),
    // 将栈顶数值弹出
    POP("POP"),
    IADD("iadd"),
    IMUL("imul"),
    ISUB("isub"),
    IDIV("idiv"),
    INVOKEVIRTUAL("invokevirtual"),
    INVOKESTATIC("invokestatic"),
    // 构造方式使用invokespecial调用
    INVOKESPECIAL("invokespecial"),
    INVOKENONVIRTUAL("invokenonvirtual"),
    RETURN("return"),
    IRETURN("ireturn"),
    ILOAD("iload"),
    ISTORE("istore"),
    NEWARRAY("newarray"),
    NEW("new"),
    DUP("dup"),
    ASTORE("astore"),
    IASTORE("iastore"),
    ALOAD("aload"),
    PUTFIELD("putfield"),
    GETFIELD("getfield"),
    ANEWARRAY("anewarray"),
    AASTORE("aastore"),
    AALOAD("aaload"),
    IF_ICMPEQ("if_icmpeq"),
    IF_ICMPNE("if_icmpne"),
    IF_ICMPLT("if_icmplt"),
    IF_ICMPGE("if_icmpge"),
    IF_ICMPGT("if_icmpgt"),
    IF_ICMPLE("if_icmple"),
    GOTO("goto"),
    IALOAD("iaload");

    private String text;
    Instruction(String text) {
        this.text = text;
    }

    @Override
    public String toString() {
        return text;
    }
}
