package symboltable;

import java.util.ArrayList;

public class State extends Symbol {

    private ArrayList<String> instructions;

    public State() {

    }

    public State(String name) {
        super(name);
        instructions = new ArrayList<>();
    }

    public void setInstructions(String str) {
        this.instructions.add(str);
    }

    public ArrayList<String> getInstructions() {
        return this.instructions;
    }
}
