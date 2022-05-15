package codegen;

import java.util.*;

/**
 * @author zzy
 */
public class ProgramGenerator extends CodeGenerator {
    private static ProgramGenerator instance = null;
    private Stack<String> nameStack = new Stack<String>();
    private Map<String, String> arrayNameMap = new HashMap<String, String>();
    private boolean isInitArguments = false;
    private ArrayList<String> structNameList = new ArrayList<String>();
    private int branch_count = 0;
    private int branch_out = 0;
    private String embedded = "";
    private String comparingCmd = "";

    private int loopCount = 0;

    public static ProgramGenerator getInstance() {
        if (instance == null) {
            instance = new ProgramGenerator();
        }

        return instance;
    }

    public int getIfElseEmbedCount() {
        return embedded.length();
    }

    public void incraseIfElseEmbed() {
        embedded += "i";
    }

    public void decraseIfElseEmbed() {
        embedded = embedded.substring(1);
    }

    public void setComparingCommand(String cmd) {
        comparingCmd = cmd;
    }

    public void emitComparingCommand() {
        emitString(comparingCmd);
    }

    public void emitBranchOut() {
        String s = "\n" + embedded + "branch_out" + branch_out + ":\n";
        this.emitString(s);
        branch_out++;
    }

    public String getBranchOut() {
        String s = embedded + "branch_out" + branch_out;
        return s;
    }

    public String getCurrentBranch() {
        String str = embedded + "branch" + branch_count;
        return str;
    }

    public void emitLoopBranch() {
        String s = "\n" + "loop" + loopCount + ":" + "\n";
        emitString(s);
    }

    public String getLoopBranch() {
        return "loop" + loopCount;
    }

    public void increaseLoopCount() {
        loopCount++;
    }

    public void increaseBranch() {
        branch_count++;
    }

    public String getAheadBranch(int ahead) {
        String str = embedded + "branch" + branch_count + ahead + ":";
        this.emitString(str);
        return str;
    }

    public void initFuncArguments(boolean bool) {
        isInitArguments = bool;
    }

    public boolean isPassingArguments() {
        return isInitArguments;
    }

    public void setCurrentFuncName(String name) {
        nameStack.push(name);
    }

    public String getCurrentFuncName() {
        return nameStack.peek();
    }

    public void popFuncName() {
        nameStack.pop();
    }


    private ProgramGenerator() {

    }

    public String getProgramName() {
        return programName;
    }


    /**
     * 生成头部内容 包括类名以及构造函数
     */
    public void generateHeader() {
        emitDirective(Directive.CLASS_PUBLIC, programName);
        emitDirective(Directive.SUPER, "java/lang/Object");
        emitBlankLine();
        emitDirective(Directive.METHOD_PUBLIC, "<init>()V");
        emit(Instruction.ALOAD, "0");
        // 构造方法使用invokespecial调用
        emit(Instruction.INVOKESPECIAL, "java/lang/Object/<init>()V");
        emit(Instruction.RETURN);
        emitDirective(Directive.END_METHOD);
        emitBlankLine();
    }


    /**
     * 生成字节码尾部内容
     */
    @Override
    public void finish() {

        emitBufferedContent();
        emitClassDefinition();
        super.finish();
    }
}
