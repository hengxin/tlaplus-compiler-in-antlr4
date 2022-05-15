package symboltable;

public class Variable extends Symbol {

    /**
     * 变量类型
     */
    private String type;

    /**
     * 代码生成暂时只支持整数
     */
    private int val;
    private boolean hasRange;
    private int startVal;
    private int endVal;
    private boolean isConst;
    private String constVal;
    /**
     * 本地变量表中的位置
     */
    private int index = -1;

    public Variable() {

    }

    public Variable(String name) {
        super(name);
        this.hasRange = false;
        this.isConst = false;
    }

    public String getType() {
        return this.type;
    }

    public void setType(String type) {
        this.type = type;
    }

    public int getVal() {
        return this.val;
    }

    public void setVal(int val) {
        this.val = val;
    }

    public int getStartVal() {
        return this.startVal;
    }

    public void setStartVal(int startVal) {
        this.startVal = startVal;
    }

    public int getEndVal() {
        return this.endVal;
    }

    public void setEndVal(int endVal) {
        this.endVal = endVal;
    }

    public void setRange(int startVal, int endVal) {
        this.hasRange = true;
        this.isConst = false;
        this.startVal = startVal;
        this.endVal = endVal;
    }

    public void setConst(String constVal) {
        this.isConst = true;
        this.constVal = constVal;
    }

    public String getConstVal() {
        return this.constVal;
    }

    public void setIndex(int index) {
        this.index = index;
    }

    public int getIndex() {
        return this.index;
    }

}
