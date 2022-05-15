import symboltable.Symbol;

import java.util.HashMap;

public class SymbolTable {

    private static SymbolTable instance;

    private HashMap<String, Symbol> symbolTable;

    private SymbolTable() {
        symbolTable = new HashMap<>();
    }

    public static SymbolTable getInstance() {
        if (instance == null) {
            instance = new SymbolTable();
        }
        return instance;
    }

    public boolean addVar(String name, Symbol symbol) {
        symbol.setName(name);
        if (isDuplicate(name)) {
            return false;
        }
        symbolTable.put(name, symbol);
        return true;
    }

    public Symbol getSymbolByName(String name) {
        return symbolTable.get(name);
    }

    public boolean existVar(String name) {
        return symbolTable.containsKey(name);
    }

    public boolean isDuplicate(String name) {
        return symbolTable.containsKey(name);
    }

    public int getSize() {
        return symbolTable.size();
    }

    public void empty() {
        symbolTable.clear();
    }

}
