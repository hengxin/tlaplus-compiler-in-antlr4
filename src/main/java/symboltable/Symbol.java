package symboltable;

public class Symbol {

    private String name;

    private String symbolType;

    public Symbol() {

    }

    public Symbol(String name) {
        this.name = name;
    }

    public String getName() {
        return this.name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getSymbolType() {
        return this.symbolType;
    }

    public void setSymbolType(String symbolType) {
        this.symbolType = symbolType;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }
        if (object == null) {
            return false;
        }
        return getClass() == object.getClass();
    }

}
