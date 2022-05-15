# tlaplus-compiler-in-antlr4

A Compiler for TLA+ in ANTLR4

本项目基于ANTLR4实现了一个TLA+的编译器，包括词法分析、语法分析、语义分析和代码生成。

项目使用gradle框架，首先在`build.gradle`文件中运行`generateGrammarSource`，生成词法分析器和语法分析器，以及遍历语法分析树所需的监听器和访问器。

编译器主程序为TLAMain，输入TLA+源程序，编译器会先进行词法、语法和语义的检查，如果没有发现问题，那么将输出目标代码Jasmin汇编语言到`TLAByteCode.j`文件中。

将代码放入Jasmin汇编器运行，可以生成Java字节码文件，然后就可以在JVM虚拟机上运行。
```shell
java -jar jasmin.jar TLAByteCode.j
java TLAByteCode
```