.class public TLAByteCode
.super java/lang/Object

.method public <init>()V
	aload	0
	invokespecial	java/lang/Object/<init>()V
	return
.end method

.method public HourClock()V
.limit stack 100
	sipush	1
	istore	0
	loop0:
	getstatic java/lang/System/out Ljava/io/PrintStream;
	iload	0
	invokestatic java/lang/String.valueOf(I)Ljava/lang/String;
	invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V
	iload	0
	sipush	12
	if_icmpeq	Label0
	iload	0
	sipush	1
	iadd
	istore	0
	goto	Label1
	Label0:
	sipush	1
	istore	0
	Label1:
	goto	loop0
.end method

.method public static main([Ljava/lang/String;)V
.limit stack 100
	new	TLAByteCode
	dup
	invokespecial	TLAByteCode/<init>()V
	astore	0
	aload	0
	invokevirtual	TLAByteCode/HourClock()V
	return
.end method
