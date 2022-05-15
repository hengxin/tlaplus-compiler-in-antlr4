import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;

public class TLAErrorListener extends BaseErrorListener {
    @Override
    public void syntaxError(Recognizer<?, ?> recognizer,
                            Object offendingSymbol,
                            int line,
                            int charPositionInLine,
                            String msg,
                            RecognitionException e) {

        if (Flag.lastErroredLine != line) {
            // 每行只报一个错误
            Flag.parserError = true;
            System.err.println("Syntax error at Line " + line + ": " + msg);
            Flag.lastErroredLine = line;
        }
    }
}
