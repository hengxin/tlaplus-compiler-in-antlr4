import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.TerminalNode;
import symboltable.*;

import java.util.List;

public class TLASemantics implements TLAListener{

    private static final int UNDEFINED_VAR = 1;
    private static final int UNDEFINED_FUNC = 2;
    private static final int UNDEFINED_STATE = 3;
    private static final int REDEFINED_VAR = 4;
    private static final int REDEFINED_CONST = 5;
    private static final int REDEFINED_FUNC = 6;
    private static final int REDEFINED_STATE = 7;
    private static final int MISMATCHED_ASSIGN = 8;
    private static final int WRONG_LEFT_VAL = 9;
    private static final int MISMATCHED_OP = 10;
    private static final int NOT_FUNCTION = 11;
    private static final int WRONG_PARAM = 12;

    public TLASemantics() {
        Flag.lastErroredLine = 0;
    }

    private void reportError(int errorNo, int line, String msg) {
        if (Flag.lastErroredLine != line) {
            Flag.semanticError = true;
            Flag.lastErroredLine = line;
            System.err.println("Semantic error type " + errorNo + " at line " + line + " : " + msg + ".");
        }
    }

    @Override
    public void enterModule(TLAParser.ModuleContext ctx) {

    }

    @Override
    public void exitModule(TLAParser.ModuleContext ctx) {

    }

    @Override
    public void enterUnit(TLAParser.UnitContext ctx) {

    }

    @Override
    public void exitUnit(TLAParser.UnitContext ctx) {

    }

    @Override
    public void enterVariableDeclaration(TLAParser.VariableDeclarationContext ctx) {
        for (TerminalNode node : ctx.IDENTIFIER()) {
            Symbol symbol = new Variable(node.getText());
            String key = node.getText();
            if (!SymbolTable.getInstance().addVar(key, symbol)) {
                reportError(REDEFINED_VAR, node.getSymbol().getLine(), "Redefined variable \"" + key + "\".");
            }
        }
    }

    @Override
    public void exitVariableDeclaration(TLAParser.VariableDeclarationContext ctx) {

    }

    @Override
    public void enterConstantDeclaration(TLAParser.ConstantDeclarationContext ctx) {
        for (TLAParser.OpDeclContext decl : ctx.opDecl()) {
            TerminalNode node = decl.IDENTIFIER();
            Symbol symbol = new Constant(node.getText());
            String key = node.getText();
            if (!SymbolTable.getInstance().addVar(key, symbol)) {
                reportError(REDEFINED_CONST, node.getSymbol().getLine(), "Redefined constant \"" + key + "\".");
            }
        }
    }

    @Override
    public void exitConstantDeclaration(TLAParser.ConstantDeclarationContext ctx) {

    }

    @Override
    public void enterRecursive(TLAParser.RecursiveContext ctx) {

    }

    @Override
    public void exitRecursive(TLAParser.RecursiveContext ctx) {

    }

    @Override
    public void enterOpDecl(TLAParser.OpDeclContext ctx) {

    }

    @Override
    public void exitOpDecl(TLAParser.OpDeclContext ctx) {

    }

    @Override
    public void enterOperatorDefinition(TLAParser.OperatorDefinitionContext ctx) {

    }

    @Override
    public void exitOperatorDefinition(TLAParser.OperatorDefinitionContext ctx) {

    }

    @Override
    public void enterNonFixLhs(TLAParser.NonFixLhsContext ctx) {
        TerminalNode node = ctx.IDENTIFIER(0);
        if (ctx.LPAREN() == null) {
            Symbol symbol = new State(node.getText());
            String key = symbol.getName();
            if (!SymbolTable.getInstance().addVar(key, symbol)) {
                reportError(REDEFINED_STATE, node.getSymbol().getLine(), "Redefined state \"" + key + "\".");
            }
        }
        // 有括号则为方法 且必定有一个参数
        else {
            Symbol symbol = new Function(node.getText());
            String key = symbol.getName();
            if (!SymbolTable.getInstance().addVar(key, symbol)) {
                reportError(REDEFINED_FUNC, node.getSymbol().getLine(), "Redefined function \"" + key + "\".");
            }
            else {
                // 将参数加入参数列表中
                for (int i = 1; i < ctx.IDENTIFIER().size(); i++) {
                    ((Function) SymbolTable.getInstance().getSymbolByName(key)).addParam(new Symbol(ctx.IDENTIFIER(i).getText()));
                }
            }
        }
    }

    @Override
    public void exitNonFixLhs(TLAParser.NonFixLhsContext ctx) {

    }

    @Override
    public void enterFunctionDefinition(TLAParser.FunctionDefinitionContext ctx) {

    }

    @Override
    public void exitFunctionDefinition(TLAParser.FunctionDefinitionContext ctx) {

    }

    @Override
    public void enterQuantifierBound(TLAParser.QuantifierBoundContext ctx) {

    }

    @Override
    public void exitQuantifierBound(TLAParser.QuantifierBoundContext ctx) {

    }

    @Override
    public void enterInstance(TLAParser.InstanceContext ctx) {

    }

    @Override
    public void exitInstance(TLAParser.InstanceContext ctx) {

    }

    @Override
    public void enterSubstitution(TLAParser.SubstitutionContext ctx) {

    }

    @Override
    public void exitSubstitution(TLAParser.SubstitutionContext ctx) {

    }

    @Override
    public void enterArgument(TLAParser.ArgumentContext ctx) {

    }

    @Override
    public void exitArgument(TLAParser.ArgumentContext ctx) {

    }

    @Override
    public void enterLambda(TLAParser.LambdaContext ctx) {

    }

    @Override
    public void exitLambda(TLAParser.LambdaContext ctx) {

    }

    @Override
    public void enterOpname(TLAParser.OpnameContext ctx) {

    }

    @Override
    public void exitOpname(TLAParser.OpnameContext ctx) {

    }

    @Override
    public void enterOpargs(TLAParser.OpargsContext ctx) {

    }

    @Override
    public void exitOpargs(TLAParser.OpargsContext ctx) {

    }

    @Override
    public void enterInstOrSubexprPrefix(TLAParser.InstOrSubexprPrefixContext ctx) {

    }

    @Override
    public void exitInstOrSubexprPrefix(TLAParser.InstOrSubexprPrefixContext ctx) {

    }

    @Override
    public void enterGeneralIdentifier(TLAParser.GeneralIdentifierContext ctx) {

    }

    @Override
    public void exitGeneralIdentifier(TLAParser.GeneralIdentifierContext ctx) {

    }

    @Override
    public void enterModuleDefinition(TLAParser.ModuleDefinitionContext ctx) {

    }

    @Override
    public void exitModuleDefinition(TLAParser.ModuleDefinitionContext ctx) {

    }

    @Override
    public void enterAssumption(TLAParser.AssumptionContext ctx) {

    }

    @Override
    public void exitAssumption(TLAParser.AssumptionContext ctx) {

    }

    @Override
    public void enterTheorem(TLAParser.TheoremContext ctx) {

    }

    @Override
    public void exitTheorem(TLAParser.TheoremContext ctx) {

    }

    @Override
    public void enterAssumeProve(TLAParser.AssumeProveContext ctx) {

    }

    @Override
    public void exitAssumeProve(TLAParser.AssumeProveContext ctx) {

    }

    @Override
    public void enterInnerAssumeProve(TLAParser.InnerAssumeProveContext ctx) {

    }

    @Override
    public void exitInnerAssumeProve(TLAParser.InnerAssumeProveContext ctx) {

    }

    @Override
    public void enterNewG(TLAParser.NewGContext ctx) {

    }

    @Override
    public void exitNewG(TLAParser.NewGContext ctx) {

    }

    @Override
    public void enterProof(TLAParser.ProofContext ctx) {

    }

    @Override
    public void exitProof(TLAParser.ProofContext ctx) {

    }

    @Override
    public void enterTerminalProof(TLAParser.TerminalProofContext ctx) {

    }

    @Override
    public void exitTerminalProof(TLAParser.TerminalProofContext ctx) {

    }

    @Override
    public void enterNonTerminalProof(TLAParser.NonTerminalProofContext ctx) {

    }

    @Override
    public void exitNonTerminalProof(TLAParser.NonTerminalProofContext ctx) {

    }

    @Override
    public void enterStep(TLAParser.StepContext ctx) {

    }

    @Override
    public void exitStep(TLAParser.StepContext ctx) {

    }

    @Override
    public void enterQedStep(TLAParser.QedStepContext ctx) {

    }

    @Override
    public void exitQedStep(TLAParser.QedStepContext ctx) {

    }

    @Override
    public void enterUseOrHide(TLAParser.UseOrHideContext ctx) {

    }

    @Override
    public void exitUseOrHide(TLAParser.UseOrHideContext ctx) {

    }

    @Override
    public void enterUseBody(TLAParser.UseBodyContext ctx) {

    }

    @Override
    public void exitUseBody(TLAParser.UseBodyContext ctx) {

    }

    @Override
    public void enterAtExp(TLAParser.AtExpContext ctx) {

    }

    @Override
    public void exitAtExp(TLAParser.AtExpContext ctx) {

    }

    @Override
    public void enterIn(TLAParser.InContext ctx) {

    }

    @Override
    public void exitIn(TLAParser.InContext ctx) {

    }

    @Override
    public void enterInfix(TLAParser.InfixContext ctx) {

    }

    @Override
    public void exitInfix(TLAParser.InfixContext ctx) {

    }

    @Override
    public void enterPrefix(TLAParser.PrefixContext ctx) {

    }

    @Override
    public void exitPrefix(TLAParser.PrefixContext ctx) {

    }

    @Override
    public void enterRightTupleUnder(TLAParser.RightTupleUnderContext ctx) {

    }

    @Override
    public void exitRightTupleUnder(TLAParser.RightTupleUnderContext ctx) {

    }

    @Override
    public void enterIdOpargs(TLAParser.IdOpargsContext ctx) {
        String name = ctx.generalIdentifier().IDENTIFIER().getText();
        // 如果是方法，判断名字是否是方法名
        if (ctx.opargs() != null) {
            if (!SymbolTable.getInstance().existVar(name)) {
                reportError(UNDEFINED_FUNC, ctx.generalIdentifier().IDENTIFIER().getSymbol().getLine(),
                        "Undefined function \"" + name + "\".");
            }
            else {
                if (!(SymbolTable.getInstance().getSymbolByName(name) instanceof Function)) {
                    reportError(NOT_FUNCTION, ctx.generalIdentifier().IDENTIFIER().getSymbol().getLine(),
                            "\"" + name + "\" is not a function.");
                }
                else {
                    int curCnt = ctx.opargs().argument().size();
                    int actualCnt = ((Function) SymbolTable.getInstance().getSymbolByName(name)).getParamTypes().size();
                    if (curCnt != actualCnt) {
                        reportError(WRONG_PARAM, ctx.generalIdentifier().IDENTIFIER().getSymbol().getLine(),
                                "Wrong parament.");
                    }
                }
            }
        }
        else {
            char c = name.charAt(0);
            // 小写字母开头说明是变量
            if (c >= 'a' && c <= 'z' && !SymbolTable.getInstance().existVar(name)) {
                reportError(UNDEFINED_VAR, ctx.generalIdentifier().IDENTIFIER().getSymbol().getLine(),
                        "Undefined variable \"" + name + "\".");
            }
            // 大写字母开头说明是状态
            else if (c >= 'A' && c <= 'Z' && !SymbolTable.getInstance().existVar(name)) {
                reportError(UNDEFINED_STATE, ctx.generalIdentifier().IDENTIFIER().getSymbol().getLine(),
                        "Undefined state \"" + name + "\".");
            }
        }
    }

    @Override
    public void exitIdOpargs(TLAParser.IdOpargsContext ctx) {

    }

    @Override
    public void enterBacket(TLAParser.BacketContext ctx) {

    }

    @Override
    public void exitBacket(TLAParser.BacketContext ctx) {

    }

    @Override
    public void enterLogic(TLAParser.LogicContext ctx) {

    }

    @Override
    public void exitLogic(TLAParser.LogicContext ctx) {

    }

    @Override
    public void enterWF_SF(TLAParser.WF_SFContext ctx) {

    }

    @Override
    public void exitWF_SF(TLAParser.WF_SFContext ctx) {

    }

    @Override
    public void enterRsqbracketUnder(TLAParser.RsqbracketUnderContext ctx) {

    }

    @Override
    public void exitRsqbracketUnder(TLAParser.RsqbracketUnderContext ctx) {

    }

    @Override
    public void enterNumExp(TLAParser.NumExpContext ctx) {

    }

    @Override
    public void exitNumExp(TLAParser.NumExpContext ctx) {

    }

    @Override
    public void enterSqbracket(TLAParser.SqbracketContext ctx) {

    }

    @Override
    public void exitSqbracket(TLAParser.SqbracketContext ctx) {

    }

    @Override
    public void enterPostfix(TLAParser.PostfixContext ctx) {

    }

    @Override
    public void exitPostfix(TLAParser.PostfixContext ctx) {

    }

    @Override
    public void enterExp2(TLAParser.Exp2Context ctx) {

    }

    @Override
    public void exitExp2(TLAParser.Exp2Context ctx) {

    }

    @Override
    public void enterExp1(TLAParser.Exp1Context ctx) {

    }

    @Override
    public void exitExp1(TLAParser.Exp1Context ctx) {

    }

    @Override
    public void enterChoose(TLAParser.ChooseContext ctx) {

    }

    @Override
    public void exitChoose(TLAParser.ChooseContext ctx) {

    }

    @Override
    public void enterStrExp(TLAParser.StrExpContext ctx) {

    }

    @Override
    public void exitStrExp(TLAParser.StrExpContext ctx) {

    }

    @Override
    public void enterTimes(TLAParser.TimesContext ctx) {

    }

    @Override
    public void exitTimes(TLAParser.TimesContext ctx) {

    }

    @Override
    public void enterQuantifier(TLAParser.QuantifierContext ctx) {

    }

    @Override
    public void exitQuantifier(TLAParser.QuantifierContext ctx) {

    }

    @Override
    public void enterLet(TLAParser.LetContext ctx) {

    }

    @Override
    public void exitLet(TLAParser.LetContext ctx) {

    }

    @Override
    public void enterAssign(TLAParser.AssignContext ctx) {
        List<TLAParser.ExpressionContext> nodes = ctx.expression();
        TLAParser.ExpressionContext leftNode = nodes.get(0);
        TLAParser.ExpressionContext rightNode = nodes.get(1);

        if (leftNode instanceof TLAParser.NumExpContext) {
            reportError(WRONG_LEFT_VAL, leftNode.getStart().getLine(),
                    "The left-hand side of an assignment must be a variable.");
        }
        else if (leftNode instanceof TLAParser.IdOpargsContext && rightNode instanceof TLAParser.IdOpargsContext) {
            if (!(SymbolTable.getInstance().getSymbolByName(leftNode.getText()) instanceof Variable)) {
                reportError(WRONG_LEFT_VAL, leftNode.getStart().getLine(),
                        "The left-hand side of an assignment must be a variable.");
            }
            else {
                String leftType = ((Variable) SymbolTable.getInstance().getSymbolByName(leftNode.getText())).getType();
                String rightType = ((Variable) SymbolTable.getInstance().getSymbolByName(rightNode.getText())).getType();
                if (!leftType.equals(rightType)) {
                    reportError(MISMATCHED_ASSIGN, leftNode.getStart().getLine(),
                            "Type mismatched for assignment.");
                }
            }
        }
    }

    @Override
    public void exitAssign(TLAParser.AssignContext ctx) {

    }

    @Override
    public void enterBinary(TLAParser.BinaryContext ctx) {
        TLAParser.ExpressionContext leftNode = ctx.expression(0);
        TLAParser.ExpressionContext rightNode = ctx.expression(1);
        String left = leftNode.getText();
        String right = rightNode.getText();
        if (leftNode instanceof TLAParser.IdOpargsContext && rightNode instanceof TLAParser.IdOpargsContext) {
            String leftType = ((Variable) SymbolTable.getInstance().getSymbolByName(left)).getType();
            String rightType = ((Variable) SymbolTable.getInstance().getSymbolByName(right)).getType();
            if (!leftType.equals(rightType)) {
                reportError(MISMATCHED_OP, leftNode.getStart().getLine(),
                        "Type mismatched for operands.");
            }
        }
        else if (leftNode instanceof TLAParser.IdOpargsContext && rightNode instanceof TLAParser.NumExpContext) {
            String leftType = ((Variable) SymbolTable.getInstance().getSymbolByName(left)).getType();
            String rightType = "INT";
            boolean isFloat = isFloat(right);
            if (isFloat) {
                rightType = "FLOAT";
            }
            if (!leftType.equals(rightType)) {
                reportError(MISMATCHED_OP, leftNode.getStart().getLine(),
                        "Type mismatched for operands.");
            }
        }
        else if (leftNode instanceof TLAParser.NumExpContext && rightNode instanceof TLAParser.IdOpargsContext) {
            String leftType = "INT";
            String rightType = ((Variable) SymbolTable.getInstance().getSymbolByName(right)).getType();
            boolean isFloat = isFloat(left);
            if (isFloat) {
                leftType = "FLOAT";
            }
            if (!leftType.equals(rightType)) {
                reportError(MISMATCHED_OP, leftNode.getStart().getLine(),
                        "Type mismatched for operands.");
            }
        }
        else if (leftNode instanceof TLAParser.NumExpContext && rightNode instanceof TLAParser.NumExpContext) {
            // 假设只有整数和浮点数
            boolean isLeftFloat = isFloat(left);
            boolean isRightFloat = isFloat(right);
            if ((isLeftFloat && !isRightFloat)) {
                reportError(MISMATCHED_OP, leftNode.getStart().getLine(),
                        "Type mismatched for operands.");
            }
            else if (!isLeftFloat && isRightFloat) {
                reportError(MISMATCHED_OP, leftNode.getStart().getLine(),
                        "Type mismatched for operands.");
            }
        }
    }

    private boolean isFloat(String str) {
        for (char c : str.toCharArray()) {
            if (c == '.') {
                return true;
            }
        }
        return false;
    }

    @Override
    public void exitBinary(TLAParser.BinaryContext ctx) {

    }

    @Override
    public void enterInstOpargs(TLAParser.InstOpargsContext ctx) {

    }

    @Override
    public void exitInstOpargs(TLAParser.InstOpargsContext ctx) {

    }

    @Override
    public void enterIf(TLAParser.IfContext ctx) {

    }

    @Override
    public void exitIf(TLAParser.IfContext ctx) {

    }

    @Override
    public void enterTuple(TLAParser.TupleContext ctx) {

    }

    @Override
    public void exitTuple(TLAParser.TupleContext ctx) {

    }

    @Override
    public void enterParen(TLAParser.ParenContext ctx) {

    }

    @Override
    public void exitParen(TLAParser.ParenContext ctx) {

    }

    @Override
    public void visitTerminal(TerminalNode node) {

    }

    @Override
    public void visitErrorNode(ErrorNode node) {

    }

    @Override
    public void enterEveryRule(ParserRuleContext ctx) {

    }

    @Override
    public void exitEveryRule(ParserRuleContext ctx) {

    }
}
