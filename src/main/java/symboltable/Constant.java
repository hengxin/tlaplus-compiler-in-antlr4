package symboltable;

public class Constant extends Symbol {

    /**
     * 常量的类型 根据使用情况推测
     * INT / STRING / ARRAY
     */
    private String type;

    public Constant() {

    }

    public Constant(String name) {
        super(name);
    }

    public void setType(String type) {
        this.type = type;
    }

    public String getType() {
        return this.type;
    }

}
