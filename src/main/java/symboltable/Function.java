package symboltable;

import java.util.ArrayList;
import java.util.List;

public class Function extends Symbol {

    private Symbol returnType;
    private List<Symbol> paramTypes;


    public Function(String name) {
        super(name);
        paramTypes = new ArrayList<>();
    }

    public Function() {
        paramTypes = new ArrayList<>();
    }

    public Symbol getReturnType() {
        return returnType;
    }

    public void setReturnType(Symbol returnType) {
        this.returnType = returnType;
    }

    public void addParam(Symbol param) {
        paramTypes.add(param);
    }

    public Symbol getParamAt(int i) {
        return paramTypes.get(i);
    }

    public List<Symbol> getParamTypes() {
        return paramTypes;
    }

}
