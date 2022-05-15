import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;

/**
 * @author zzy
 */
public class TLAMain {

    public static void main(String[] args) throws IOException {
        InputStream is = System.in;

        String file;
        if (args.length > 0) {
            file = args[0];
            is = new FileInputStream(file);
        }

        // 获取输入流
        CharStream input = CharStreams.fromStream(is);
        // 放入词法分析器
        TLALexer lexer = new TLALexer(input) {
            @Override
            public void notifyListeners(LexerNoViableAltException e) {
                Flag.lexerError = true;
                String text = _input.getText(Interval.of(_tokenStartCharIndex, _input.index()));
                System.err.println("Lexer error at Line " + _tokenStartLine + ": Mysterious token \"" + text + "\".");
            }
        };
        // 产生词法单元流
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        // 放入语法分析器
        TLAParser parser = new TLAParser(tokens);

        parser.removeErrorListeners();
        parser.addErrorListener(new TLAErrorListener());

        ParseTree tree = parser.module();

        if (!Flag.lexerError && !Flag.parserError) {
            ParseTreeWalker walker = new ParseTreeWalker();
            walker.walk(new TLASemantics(), tree);
        }

        SymbolTable.getInstance().empty();

        if (!Flag.lexerError && !Flag.parserError && !Flag.semanticError) {
            System.out.println("进入");
            // 新建一个通用的，能够触发回调函数的语法分析树遍历器
            ParseTreeWalker walker = new ParseTreeWalker();
            walker.walk(new TLATranslator(), tree);
        }


    }

    public static void printTokens(List<? extends Token> tokens, Vocabulary vocabulary) {
        System.out.println("开始打印");
        for (Token token : tokens) {
            String textToPrint = token.getText();
            System.out.println(vocabulary.getSymbolicName(token.getType()) + " " + textToPrint
                    + " (" + token.getLine() + ")");
        }
    }
}
