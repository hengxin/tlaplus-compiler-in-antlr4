import codegen.Directive;
import codegen.Instruction;
import codegen.ProgramGenerator;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.TerminalNode;
import symboltable.*;

import java.util.ArrayList;
import java.util.List;

public class TLATranslator implements TLAListener {

    private ProgramGenerator generator = ProgramGenerator.getInstance();

    private int indexOfVar = -1;

    private final int stackSize = 100;

    private String curState;

    private ArrayList<String> bufferedInstruction;

    private String curVar;

    private int branchIndex = 0;

    private int loopIndex = 0;

    private boolean endTheorem = false;

    public void writeBuffer(Instruction opcode) {
        String inst = "\t" + opcode;
        bufferedInstruction.add(inst);
    }

    public void writeBuffer(Instruction opcode, String operand) {
        String inst = "\t" + opcode + "\t" + operand;
        bufferedInstruction.add(inst);
    }

    public void handleIf(String parent, String infixOp) {
        // 如果是if的条件 退出时写入if的指令
        if ("IF".equals(parent)) {
            switch (infixOp) {
                // 不等于
                case "#":
                    bufferedInstruction.add("\t" + Instruction.IF_ICMPEQ + "\t" + "Label" + branchIndex);
                    break;
                case "<":
                    bufferedInstruction.add("\t" + Instruction.IF_ICMPLT + "\t" + "Label" + branchIndex);
                    break;
                case ">":
                    bufferedInstruction.add("\t" + Instruction.IF_ICMPGT + "\t" + "Label" + branchIndex);
                    break;
                case "<=":
                    bufferedInstruction.add("\t" + Instruction.IF_ICMPLE + "\t" + "Label" + branchIndex);
                    break;
                case ">=":
                    bufferedInstruction.add("\t" + Instruction.IF_ICMPGE + "\t" + "Label" + branchIndex);
                    break;
                default:
                    break;
            }
        }
    }

    @Override
    public void enterModule(TLAParser.ModuleContext ctx) {
        generator.generateHeader();
        // 将module作为一个方法
        String name = ctx.IDENTIFIER(0).getText();
        generator.emitDirective(Directive.METHOD_PUBLIC, name + "()V");
        // 设置操作数栈的大小 (不设定就会报错 包括main方法)
        generator.emitDirective(Directive.LIMIT_STACK, stackSize);
    }

    @Override
    public void exitModule(TLAParser.ModuleContext ctx) {
        // 结束module方法
        generator.emitDirective(Directive.END_METHOD);
        generator.emitBlankLine();
        generator.emitDirective(Directive.METHOD_PUBLIC_STATIC, "main([Ljava/lang/String;)V");
        // 不限定栈的数量就会报错
        generator.emitDirective(Directive.LIMIT_STACK, 100);
        // 在main方法中new新的对象并调用方法
        String name = generator.getProgramName();
        generator.emit(Instruction.NEW, name);
        generator.emit(Instruction.DUP);
        generator.emit(Instruction.INVOKESPECIAL, name + "/<init>()V");
        generator.emit(Instruction.ASTORE, "0");
        generator.emit(Instruction.ALOAD, "0");
        generator.emit(Instruction.INVOKEVIRTUAL, name + "/" + ctx.IDENTIFIER(0).getText() + "()V");
        generator.emit(Instruction.RETURN);
        generator.emitDirective(Directive.END_METHOD);
        generator.finish();
    }

    @Override
    public void enterUnit(TLAParser.UnitContext ctx) {}

    @Override
    public void exitUnit(TLAParser.UnitContext ctx) {}

    @Override
    public void enterVariableDeclaration(TLAParser.VariableDeclarationContext ctx) {
        List<TerminalNode> vars = ctx.IDENTIFIER();
        int num = vars.size();
        for (TerminalNode node : vars) {
            Symbol symbol = new Variable(node.getText());
            String key = "Variable_" + symbol.getName();
            SymbolTable.getInstance().addVar(key, symbol);
        }
    }

    @Override
    public void exitVariableDeclaration(TLAParser.VariableDeclarationContext ctx) {}

    @Override
    public void enterConstantDeclaration(TLAParser.ConstantDeclarationContext ctx) {
        List<TLAParser.OpDeclContext> decls = ctx.opDecl();
        for (TLAParser.OpDeclContext decl : decls) {
            TerminalNode constant = decl.IDENTIFIER();
            Symbol symbol = new Constant(constant.getText());
            String key = "Constant" + "_" + symbol.getName();
            SymbolTable.getInstance().addVar(key, symbol);
        }
    }

    @Override
    public void exitConstantDeclaration(TLAParser.ConstantDeclarationContext ctx) {}

    @Override
    public void enterRecursive(TLAParser.RecursiveContext ctx) {}

    @Override
    public void exitRecursive(TLAParser.RecursiveContext ctx) {}

    @Override
    public void enterOpDecl(TLAParser.OpDeclContext ctx) {}

    @Override
    public void exitOpDecl(TLAParser.OpDeclContext ctx) {}

    @Override
    public void enterOperatorDefinition(TLAParser.OperatorDefinitionContext ctx) {}

    @Override
    public void exitOperatorDefinition(TLAParser.OperatorDefinitionContext ctx) {
        // 记录每个状态的操作
        if (curState != null && SymbolTable.getInstance().existVar(curState)) {
            State state = (State) SymbolTable.getInstance().getSymbolByName(curState);
            System.out.println(curState);
            for (String inst : bufferedInstruction) {
                state.setInstructions(inst);
                System.out.println(inst);
            }
            SymbolTable.getInstance().addVar(curState, state);
        }
        else {
            System.err.println("Error: StateNotFound");
        }
        // 清空缓存
        this.curState = null;
        this.bufferedInstruction.clear();
    }

    @Override
    public void enterNonFixLhs(TLAParser.NonFixLhsContext ctx) {
        List<TerminalNode> nodes = ctx.IDENTIFIER();
        // 状态只有一个节点 方法有多个
        if (nodes.size() == 1) {
            for (TerminalNode node : nodes) {
                Symbol symbol = new State(node.getText());
                String key = "State" + "_" + symbol.getName();
                this.curState = key;
                SymbolTable.getInstance().addVar(key, symbol);
            }
        }
        else {
            TerminalNode node = nodes.get(0);
            Symbol symbol = new Function(node.getText());
            String key = "Function_" + symbol.getName();
            for (int i = 1; i < nodes.size(); i++) {
                // 将参数加入对应的参数列表中
            }
        }
        this.bufferedInstruction = new ArrayList<>();
    }

    @Override
    public void exitNonFixLhs(TLAParser.NonFixLhsContext ctx) {}

    @Override
    public void enterFunctionDefinition(TLAParser.FunctionDefinitionContext ctx) {}

    @Override
    public void exitFunctionDefinition(TLAParser.FunctionDefinitionContext ctx) {}

    @Override
    public void enterQuantifierBound(TLAParser.QuantifierBoundContext ctx) {}

    @Override
    public void exitQuantifierBound(TLAParser.QuantifierBoundContext ctx) {}

    @Override
    public void enterInstance(TLAParser.InstanceContext ctx) {}

    @Override
    public void exitInstance(TLAParser.InstanceContext ctx) {}

    @Override
    public void enterSubstitution(TLAParser.SubstitutionContext ctx) {}

    @Override
    public void exitSubstitution(TLAParser.SubstitutionContext ctx) {}

    @Override
    public void enterArgument(TLAParser.ArgumentContext ctx) {}

    @Override
    public void exitArgument(TLAParser.ArgumentContext ctx) {}

    @Override
    public void enterLambda(TLAParser.LambdaContext ctx) {}

    @Override
    public void exitLambda(TLAParser.LambdaContext ctx) {}

    @Override
    public void enterOpname(TLAParser.OpnameContext ctx) {}

    @Override
    public void exitOpname(TLAParser.OpnameContext ctx) {}

    @Override
    public void enterOpargs(TLAParser.OpargsContext ctx) {}

    @Override
    public void exitOpargs(TLAParser.OpargsContext ctx) {}

    @Override
    public void enterInstOrSubexprPrefix(TLAParser.InstOrSubexprPrefixContext ctx) {}

    @Override
    public void exitInstOrSubexprPrefix(TLAParser.InstOrSubexprPrefixContext ctx) {}

    @Override
    public void enterGeneralIdentifier(TLAParser.GeneralIdentifierContext ctx) {}

    @Override
    public void exitGeneralIdentifier(TLAParser.GeneralIdentifierContext ctx) {}

    @Override
    public void enterModuleDefinition(TLAParser.ModuleDefinitionContext ctx) {}

    @Override
    public void exitModuleDefinition(TLAParser.ModuleDefinitionContext ctx) {}

    @Override
    public void enterAssumption(TLAParser.AssumptionContext ctx) {}

    @Override
    public void exitAssumption(TLAParser.AssumptionContext ctx) {}

    @Override
    public void enterTheorem(TLAParser.TheoremContext ctx) {
        if (ctx.ReservedWord_THEOREM() != null) {
            TLAParser.ExpressionContext context = ctx.expression();
            // 形式一般为 Spec => [] State
            endTheorem = true;
        }
    }

    @Override
    public void exitTheorem(TLAParser.TheoremContext ctx) {}

    @Override
    public void enterAssumeProve(TLAParser.AssumeProveContext ctx) {}

    @Override
    public void exitAssumeProve(TLAParser.AssumeProveContext ctx) {}

    @Override
    public void enterInnerAssumeProve(TLAParser.InnerAssumeProveContext ctx) {}

    @Override
    public void exitInnerAssumeProve(TLAParser.InnerAssumeProveContext ctx) {}

    @Override
    public void enterNewG(TLAParser.NewGContext ctx) {}

    @Override
    public void exitNewG(TLAParser.NewGContext ctx) {}

    @Override
    public void enterProof(TLAParser.ProofContext ctx) {}

    @Override
    public void exitProof(TLAParser.ProofContext ctx) {}

    @Override
    public void enterTerminalProof(TLAParser.TerminalProofContext ctx) {}

    @Override
    public void exitTerminalProof(TLAParser.TerminalProofContext ctx) {}

    @Override
    public void enterNonTerminalProof(TLAParser.NonTerminalProofContext ctx) {}

    @Override
    public void exitNonTerminalProof(TLAParser.NonTerminalProofContext ctx) {}

    @Override
    public void enterStep(TLAParser.StepContext ctx) {}

    @Override
    public void exitStep(TLAParser.StepContext ctx) {}

    @Override
    public void enterQedStep(TLAParser.QedStepContext ctx) {}

    @Override
    public void exitQedStep(TLAParser.QedStepContext ctx) {}

    @Override
    public void enterUseOrHide(TLAParser.UseOrHideContext ctx) {}

    @Override
    public void exitUseOrHide(TLAParser.UseOrHideContext ctx) {}

    @Override
    public void enterUseBody(TLAParser.UseBodyContext ctx) {}

    @Override
    public void exitUseBody(TLAParser.UseBodyContext ctx) {}

    @Override
    public void enterAtExp(TLAParser.AtExpContext ctx) {}

    @Override
    public void exitAtExp(TLAParser.AtExpContext ctx) {}

    @Override
    public void enterIn(TLAParser.InContext ctx) {
        List<TLAParser.ExpressionContext> nodes = ctx.expression();
        int num = nodes.size();
        if (num == 2) {
            String key = "Variable_" + nodes.get(0).getText();
            int cnt = nodes.get(1).getChildCount();
            // val' 数值更改的情况
            if (key.charAt(key.length() - 1) == '\'') {
                key = key.substring(0, key.length() - 1);
            }
            // 将变量赋值给变量 如 val \in Data Data一般为constant
            if (cnt == 1) {
                String value = nodes.get(1).getText();
                if (SymbolTable.getInstance().existVar(key)) {
                    Variable variable = (Variable) SymbolTable.getInstance().getSymbolByName(key);
                    variable.setConst(value);
                    SymbolTable.getInstance().addVar(key, variable);
                    // 在in中出现 表示常量是一个范围 即数组
                    ((Constant)SymbolTable.getInstance().getSymbolByName("Constant_" + value)).setType("ARRAY");
                }
            }
            // 将数值范围赋值给变量
            else {
                String range = nodes.get(1).getText();
                range = range.substring(1, range.length() - 1);
                int index = range.indexOf(".");
                int start = Integer.parseInt(range.substring(0, index));
                int end = Integer.parseInt(range.substring(index + 2));
                Variable variable = (Variable) SymbolTable.getInstance().getSymbolByName(key);
                variable.setVal(start);
                variable.setRange(start, end);
                // 如果还没有赋值，则以范围左值赋给变量
                if (variable.getIndex() == -1) {
                    indexOfVar++;
                    variable.setIndex(indexOfVar);
                    // 赋值并存储到局部变量表中
                    writeBuffer(Instruction.SIPUSH, String.valueOf(start));
                    writeBuffer(Instruction.ISTORE, String.valueOf(indexOfVar));
                }
                SymbolTable.getInstance().addVar(key, variable);
            }
        }
        else {
            // TODO 更复杂的赋值情况 暂未实现
        }
    }

    @Override
    public void exitIn(TLAParser.InContext ctx) {}

    @Override
    public void enterInfix(TLAParser.InfixContext ctx) {
        String infixOp = ctx.INFIXOP().getText();
        switch (infixOp) {
            case "=>":
                // Spec => [] State
                if (endTheorem) {
                    String name = "State_" + ctx.expression(0).getText();
                    List<String> instructions = ((State)SymbolTable.getInstance().getSymbolByName(name)).getInstructions();
                    for (String inst : instructions) {
                        if (SymbolTable.getInstance().existVar(inst)) {
                            State state = (State) SymbolTable.getInstance().getSymbolByName(inst);
                            for (String str : state.getInstructions()) {
                                generator.emitString(str);
                            }
                        }
                        else if ("Print".equals(inst)) {
                            generator.emitPrintInt(indexOfVar);
                        }
                        else {
                            generator.emitString(inst);
                        }
                    }
                }
            case "%":
            default:
                break;
        }
    }

    @Override
    public void exitInfix(TLAParser.InfixContext ctx) {
        String infixOp = ctx.INFIXOP().getText();
        String parent = ctx.getParent().getChild(0).getText();
        handleIf(parent, infixOp);
    }

    @Override
    public void enterPrefix(TLAParser.PrefixContext ctx) {
        String prefixOp = ctx.PREFIXOP().getText();
        switch (prefixOp) {
            // 恒成立 即无限循环
            case "[]":
                bufferedInstruction.add("\t" + "loop" + loopIndex + ":");
                bufferedInstruction.add("Print");
            case "~":
            case "<>":
            case "DOMAIN":
            case "ENABLED":
            case "SUBSET":
            case "UNCHANGED":
            case "UNION":
            default:
                break;
        }
    }

    @Override
    public void exitPrefix(TLAParser.PrefixContext ctx) {
        String prefixOp = ctx.PREFIXOP().getText();
        switch (prefixOp) {
            case "[]":
                bufferedInstruction.add("\t" + Instruction.GOTO + "\t" + "loop" + loopIndex);
                loopIndex++;
            case "~":
            case "<>":
            case "DOMAIN":
            case "ENABLED":
            case "SUBSET":
            case "UNCHANGED":
            case "UNION":
            default:
                break;
        }
    }

    @Override
    public void enterRightTupleUnder(TLAParser.RightTupleUnderContext ctx) {}

    @Override
    public void exitRightTupleUnder(TLAParser.RightTupleUnderContext ctx) {}

    @Override
    public void enterIdOpargs(TLAParser.IdOpargsContext ctx) {
        String name = "State_" + ctx.getText();
        if (curState != null && !name.equals(curState) && SymbolTable.getInstance().existVar(name)) {
            bufferedInstruction.add(name);
        }
        name = "Variable_" + ctx.getText();
        if (SymbolTable.getInstance().existVar(name)) {
            curVar = ctx.getText();
        }
    }

    @Override
    public void exitIdOpargs(TLAParser.IdOpargsContext ctx) {}

    @Override
    public void enterBacket(TLAParser.BacketContext ctx) {}

    @Override
    public void exitBacket(TLAParser.BacketContext ctx) {}

    @Override
    public void enterLogic(TLAParser.LogicContext ctx) {}

    @Override
    public void exitLogic(TLAParser.LogicContext ctx) {}

    @Override
    public void enterWF_SF(TLAParser.WF_SFContext ctx) {}

    @Override
    public void exitWF_SF(TLAParser.WF_SFContext ctx) {}

    @Override
    public void enterRsqbracketUnder(TLAParser.RsqbracketUnderContext ctx) {}

    @Override
    public void exitRsqbracketUnder(TLAParser.RsqbracketUnderContext ctx) {}

    @Override
    public void enterNumExp(TLAParser.NumExpContext ctx) {}

    @Override
    public void exitNumExp(TLAParser.NumExpContext ctx) {}

    @Override
    public void enterSqbracket(TLAParser.SqbracketContext ctx) {}

    @Override
    public void exitSqbracket(TLAParser.SqbracketContext ctx) {}

    @Override
    public void enterPostfix(TLAParser.PostfixContext ctx) {}

    @Override
    public void exitPostfix(TLAParser.PostfixContext ctx) {}

    @Override
    public void enterExp2(TLAParser.Exp2Context ctx) {}

    @Override
    public void exitExp2(TLAParser.Exp2Context ctx) {}

    @Override
    public void enterExp1(TLAParser.Exp1Context ctx) {}

    @Override
    public void exitExp1(TLAParser.Exp1Context ctx) {}

    @Override
    public void enterChoose(TLAParser.ChooseContext ctx) {}

    @Override
    public void exitChoose(TLAParser.ChooseContext ctx) {}

    @Override
    public void enterStrExp(TLAParser.StrExpContext ctx) {
        String str = ctx.STRING().getText();
    }

    @Override
    public void exitStrExp(TLAParser.StrExpContext ctx) {}

    @Override
    public void enterTimes(TLAParser.TimesContext ctx) {}

    @Override
    public void exitTimes(TLAParser.TimesContext ctx) {}

    @Override
    public void enterQuantifier(TLAParser.QuantifierContext ctx) {}

    @Override
    public void exitQuantifier(TLAParser.QuantifierContext ctx) {}

    @Override
    public void enterLet(TLAParser.LetContext ctx) {}

    @Override
    public void exitLet(TLAParser.LetContext ctx) {}

    @Override
    public void enterAssign(TLAParser.AssignContext ctx) {
        // 赋值操作 左右两边各有一个表达式 共两个节点
        List<TLAParser.ExpressionContext> nodes = ctx.expression();
        TLAParser.ExpressionContext leftNode = nodes.get(0);
        TLAParser.ExpressionContext rightNode = nodes.get(1);
        curVar = leftNode.getText();
        // 如果是单个节点 则直接赋值 如果是表达式则继续处理
        if (rightNode instanceof TLAParser.NumExpContext) {
            if (curVar.endsWith("'")) {
                curVar = curVar.substring(0, curVar.length() - 1);
            }
            String key = "Variable_" + curVar;
            if (SymbolTable.getInstance().existVar(key)) {
                int i = ((Variable) SymbolTable.getInstance().getSymbolByName(key)).getIndex();
                if (i == -1) {
                    indexOfVar++;
                    ((Variable) SymbolTable.getInstance().getSymbolByName(key)).setIndex(indexOfVar);
                    i = indexOfVar;
                }
                writeBuffer(Instruction.ISTORE, String.valueOf(i));
            }
        }
        else if (rightNode instanceof TLAParser.IdOpargsContext) {
            if (curVar.endsWith("'")) {
                curVar = curVar.substring(0, curVar.length() - 1);
            }
            String rightVal = rightNode.getText();
            if (rightVal.endsWith("'")) {
                rightVal = rightVal.substring(0, rightVal.length() - 1);
            }
            // 如果相同 则值不变 无操作
            // 如果不同 赋值
            if (!curVar.equals(rightVal)) {
                int val = ((Variable) SymbolTable.getInstance().getSymbolByName("Variable_" + rightVal)).getVal();
                ((Variable) SymbolTable.getInstance().getSymbolByName("Variable_" + curVar)).setVal(val);
                int i = ((Variable) SymbolTable.getInstance().getSymbolByName("Variable_" + curVar)).getIndex();
                writeBuffer(Instruction.ILOAD, String.valueOf(i));
                writeBuffer(Instruction.SIPUSH, String.valueOf(val));
                writeBuffer(Instruction.ISTORE, String.valueOf(i));
            }
        }
    }

    @Override
    public void exitAssign(TLAParser.AssignContext ctx) {
        // 清空当前变量
        curVar = null;
    }

    @Override
    public void enterBinary(TLAParser.BinaryContext ctx) {
        TLAParser.ExpressionContext leftNode = ctx.expression(0);
        TLAParser.ExpressionContext rightNode = ctx.expression(1);
        String left = "Variable_" + leftNode.getText();
        String right = "Variable_" + rightNode.getText();
        // var + var
        if (leftNode instanceof TLAParser.IdOpargsContext && rightNode instanceof TLAParser.IdOpargsContext) {
            int index1 = ((Variable) SymbolTable.getInstance().getSymbolByName(left)).getIndex();
            int index2 = ((Variable) SymbolTable.getInstance().getSymbolByName(right)).getIndex();
            writeBuffer(Instruction.ILOAD, String.valueOf(index1));
            writeBuffer(Instruction.ILOAD, String.valueOf(index2));
        }
        // var + num
        else if (leftNode instanceof TLAParser.IdOpargsContext && rightNode instanceof TLAParser.NumExpContext) {
            int index1 = ((Variable) SymbolTable.getInstance().getSymbolByName(left)).getIndex();
            writeBuffer(Instruction.ILOAD, String.valueOf(index1));
            writeBuffer(Instruction.SIPUSH, rightNode.getText());
        }
        // num + var
        else if (leftNode instanceof TLAParser.NumExpContext && rightNode instanceof TLAParser.IdOpargsContext) {
            int index2 = ((Variable) SymbolTable.getInstance().getSymbolByName(right)).getIndex();
            writeBuffer(Instruction.SIPUSH, leftNode.getText());
            writeBuffer(Instruction.ILOAD, String.valueOf(index2));

        }
        // num + num
        else {
            writeBuffer(Instruction.SIPUSH, leftNode.getText());
            writeBuffer(Instruction.SIPUSH, rightNode.getText());
        }
        // 加减乘除
        if (ctx.OP_ASTER() != null) {
            writeBuffer(Instruction.IMUL);
        }
        else if (ctx.OP_DIV() != null) {
            writeBuffer(Instruction.IDIV);
        }
        else if (ctx.OP_DASH() != null) {
            writeBuffer(Instruction.ISUB);
        }
        else {
            writeBuffer(Instruction.IADD);
        }
        // curVal非null即表示为赋值操作
        if (curVar != null) {
            if (curVar.endsWith("'")) {
                curVar = curVar.substring(0, curVar.length() - 1);
            }
            String key = "Variable_" + curVar;
            if (SymbolTable.getInstance().existVar(key)) {
                Variable variable = (Variable) SymbolTable.getInstance().getSymbolByName(key);
                int index = variable.getIndex();
                // 将结果存储到局部变量表
                writeBuffer(Instruction.ISTORE, String.valueOf(index));
            }
        }
    }

    @Override
    public void exitBinary(TLAParser.BinaryContext ctx) {}

    @Override
    public void enterInstOpargs(TLAParser.InstOpargsContext ctx) {}

    @Override
    public void exitInstOpargs(TLAParser.InstOpargsContext ctx) {}

    @Override
    public void enterIf(TLAParser.IfContext ctx) {
        TLAParser.ExpressionContext condition = ctx.expression(0);
        // 处理条件
        if (condition instanceof TLAParser.InfixContext) {
            TLAParser.InfixContext context = (TLAParser.InfixContext) condition;
            String infixOp = context.INFIXOP().getText();
            TLAParser.ExpressionContext leftNode = context.expression(0);
            TLAParser.ExpressionContext rightNode = context.expression(1);
            String key = "Variable_" + leftNode.getText();
            String leftVal = leftNode.getText();
            String rightVal =rightNode.getText();

            if (leftNode instanceof TLAParser.IdOpargsContext) {
                int index = ((Variable) SymbolTable.getInstance().getSymbolByName("Variable_" + leftVal)).getIndex();
                writeBuffer(Instruction.ILOAD, String.valueOf(index));
            }
            else if (leftNode instanceof TLAParser.NumExpContext) {
                writeBuffer(Instruction.SIPUSH, leftVal);
            }

            if (rightNode instanceof TLAParser.IdOpargsContext) {
                int index = ((Variable) SymbolTable.getInstance().getSymbolByName("Variable_" + rightVal)).getIndex();
                writeBuffer(Instruction.ILOAD, String.valueOf(index));
            }
            else if (rightNode instanceof TLAParser.NumExpContext) {
                writeBuffer(Instruction.SIPUSH, rightVal);
            }
        }

    }

    @Override
    public void exitIf(TLAParser.IfContext ctx) {
        bufferedInstruction.add("\t" + Instruction.GOTO + "\t" + "Label" + (branchIndex + 1));
        bufferedInstruction.add("\t" + "Label" + branchIndex + ":");
        if (curVar != null && ctx.expression(2) instanceof TLAParser.NumExpContext) {
            String key = "Variable_" + curVar;
            int index = ((Variable) SymbolTable.getInstance().getSymbolByName(key)).getIndex();
            writeBuffer(Instruction.SIPUSH, ctx.expression(2).getText());
            writeBuffer(Instruction.ISTORE, String.valueOf(index));
        }
        // 跳出if-then-else
        branchIndex++;
        bufferedInstruction.add("\t" + "Label" + branchIndex + ":");
        // 下一个if-else
        branchIndex++;
    }

    @Override
    public void enterTuple(TLAParser.TupleContext ctx) {}

    @Override
    public void exitTuple(TLAParser.TupleContext ctx) {}

    @Override
    public void enterParen(TLAParser.ParenContext ctx) {}

    @Override
    public void exitParen(TLAParser.ParenContext ctx) {}

    @Override
    public void visitTerminal(TerminalNode node) {}

    @Override
    public void visitErrorNode(ErrorNode node) {}

    @Override
    public void enterEveryRule(ParserRuleContext ctx) {}

    @Override
    public void exitEveryRule(ParserRuleContext ctx) {}
}
