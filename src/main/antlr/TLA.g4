grammar TLA;

// 语法
module : SEPARATOR ReservedWord_MODULE IDENTIFIER SEPARATOR
         (ReservedWord_EXTENDS (IDENTIFIER (COMMA IDENTIFIER)*))? (unit)* MODULE_END ;
unit
    : variableDeclaration
    | constantDeclaration
    | recursive
    | useOrHide
    | ReservedWord_LOCAL? operatorDefinition
    | ReservedWord_LOCAL? functionDefinition
    | ReservedWord_LOCAL? instance
    | ReservedWord_LOCAL? moduleDefinition
    | assumption
    | theorem (proof)?
    | module
    | SEPARATOR
    ;
variableDeclaration : (ReservedWord_VARIABLE | ReservedWord_VARIABLES) (IDENTIFIER (COMMA IDENTIFIER)*);
constantDeclaration : (ReservedWord_CONSTANT | ReservedWord_CONSTANTS) (opDecl (COMMA opDecl)*) ;
recursive : ReservedWord_RECURSIVE (opDecl (COMMA opDecl)*) ;
opDecl
    : IDENTIFIER
    | IDENTIFIER LPAREN (UNDER (COMMA UNDER)*) RPAREN
    | PREFIXOP UNDER
    | UNDER INFIXOP UNDER
    | UNDER POSTFIXOP
    ;
operatorDefinition : (nonFixLhs
                        | (POSTFIXOP IDENTIFIER)
                        | (IDENTIFIER INFIXOP IDENTIFIER)
                        | (IDENTIFIER POSTFIXOP))
                     DEFINE expression ;
nonFixLhs : IDENTIFIER (LPAREN ((IDENTIFIER | opDecl) (COMMA (IDENTIFIER | opDecl))*) RPAREN)? ;
functionDefinition : IDENTIFIER LSQBRACKET (quantifierBound (COMMA quantifierBound)*) RSQBRACKET DEFINE expression ;
quantifierBound : ((IDENTIFIER | (LTUPLE (IDENTIFIER (COMMA IDENTIFIER)*) RTUPLE)) | (IDENTIFIER (COMMA IDENTIFIER)*)) OP_IN expression ;
instance : ReservedWord_INSTANCE IDENTIFIER (ReservedWord_WITH (substitution (COMMA substitution)*))? ;
substitution : (IDENTIFIER | PREFIXOP | INFIXOP | POSTFIXOP) OP_LTDASH argument ;
argument : expression | opname | lambda ;
lambda : ReservedWord_LAMBDA (IDENTIFIER (COMMA IDENTIFIER)*) COLON expression ;
opname : (IDENTIFIER | PREFIXOP | INFIXOP | POSTFIXOP | PROOFSTEPID) (BANG (IDENTIFIER | PREFIXOP | INFIXOP | POSTFIXOP | (LTUPLE | RTUPLE | AT | NUMERAL+)))* ;
opargs : LPAREN (argument (COMMA argument)*) RPAREN ;
instOrSubexprPrefix : ( (PROOFSTEPID BANG)?
                        (( IDENTIFIER (opargs)?
                            | (LTUPLE | RTUPLE | AT | NUMERAL+)
                            | opargs
                            | (PREFIXOP | POSTFIXOP) LPAREN expression RPAREN
                            | INFIXOP LPAREN expression COMMA expression RPAREN)
                            BANG)*
                      ) ; // TODO： 这里要去除null的情况
generalIdentifier : ((instOrSubexprPrefix)? IDENTIFIER) | PROOFSTEPID ;
moduleDefinition : nonFixLhs DEFINE instance ;
assumption : (ReservedWord_ASSUME | ReservedWord_ASSUMPTION | ReservedWord_AXIOM) (IDENTIFIER DEFINE)? expression ;
theorem : (ReservedWord_THEOREM | ReservedWord_PROPOSITION | ReservedWord_LEMMA | ReservedWord_COROLLARY)
          (IDENTIFIER DEFINE)? (expression | assumeProve) ;
assumeProve : ReservedWord_ASSUME
              ((expression | newG | innerAssumeProve) (COMMA (expression | newG | innerAssumeProve))*)
              ReservedWord_PROVE
              expression ;
innerAssumeProve : (IDENTIFIER COLONCOLON)? assumeProve ;
newG : ((ReservedWord_NEW)?
            (ReservedWord_CONSTANT
                | ReservedWord_VARIABLE
                | ReservedWord_STATE
                | ReservedWord_ACTION
                | ReservedWord_TEMPORAL)?)  // TODO： 这里要去除null的情况
       ((IDENTIFIER OP_IN expression) | opDecl) ;
proof : terminalProof | nonTerminalProof ;
terminalProof : (ReservedWord_PROOF)?
                    (ReservedWord_BY (ReservedWord_ONLY)? useBody
                        | ReservedWord_OBVIOUS
                        | ReservedWord_OMITTED) ;
nonTerminalProof : (ReservedWord_PROOF)? step* qedStep ;
step : BEGINSTEPTOKEN ((useOrHide
                       | ReservedWord_DEFINE? (operatorDefinition | functionDefinition | moduleDefinition)+
                       | instance
                       | ReservedWord_HAVE expression
                       | ReservedWord_WITNESS (expression (COMMA expression)*)
                       | ReservedWord_TAKE ((quantifierBound (COMMA quantifierBound)*) | (IDENTIFIER (COMMA IDENTIFIER)*)))
                      | ((((ReservedWord_SUFFICES)? (expression | assumeProve))
                          | ReservedWord_CASE expression
                          | (ReservedWord_PICK ((quantifierBound (COMMA quantifierBound)*) | (IDENTIFIER (COMMA IDENTIFIER)*)) COLON expression)) proof?))
                     ;

qedStep : BEGINSTEPTOKEN ReservedWord_QED (proof)? ;
useOrHide : (( ReservedWord_USE (ReservedWord_ONLY)?) | ReservedWord_HIDE) useBody ;
useBody : ((((expression | ReservedWord_MODULE) (COMMA (expression | ReservedWord_MODULE))*) IDENTIFIER)?)
          (ReservedWord_DEF | ReservedWord_DEFS)?
          ((opname | (ReservedWord_MODULE IDENTIFIER)) (COMMA (opname | (ReservedWord_MODULE IDENTIFIER)))*) ; // TODO： 这里要去除null的情况
expression :
      IDENTIFIER (LPAREN (IDENTIFIER (COMMA IDENTIFIER)*) RPAREN)? COLONCOLON expression    # Exp1
    | instOrSubexprPrefix ((LTUPLE | RTUPLE | COLON | (NUMERAL)+) | opargs)                 # InstOpargs
    | generalIdentifier (opargs)?                                                           # IdOpargs
    // 运算符优先级问题
    | expression (OP_TIMES expression)+                                                     # Times
    | expression (OP_ASTER | OP_DIV | OP_PERCENT) expression                                             # Binary
    | expression ('+' | '-') expression                                                     # Binary
    | <assoc=right> expression '=' expression                                               # Assign
    | PREFIXOP expression                                                                   # Prefix
    | expression OP_IN expression                                                           # In
    | expression INFIXOP expression                                                         # Infix
    | expression POSTFIXOP                                                                  # Postfix
    | LPAREN expression RPAREN                                                              # Paren
    | (QUANTIFIER_A | QUANTIFIER_E) (quantifierBound (COMMA quantifierBound)*) COLON expression # Quantifier
    | (QUANTIFIER_A | QUANTIFIER_AA | QUANTIFIER_E | QUANTIFIER_EE) (IDENTIFIER (COMMA IDENTIFIER)*) COLON expression # Quantifier
    | ReservedWord_CHOOSE (IDENTIFIER | LTUPLE (IDENTIFIER (COMMA IDENTIFIER)*) RTUPLE) (OP_IN expression)? COLON expression # Choose
    | LBRACKET ((expression (COMMA expression)*))? RBRACKET # Backet  // 大括号
    | LBRACKET (IDENTIFIER | LTUPLE (IDENTIFIER (COMMA IDENTIFIER)*) RTUPLE) OP_IN expression COLON expression RBRACKET # Backet
    | LBRACKET expression COLON (quantifierBound (COMMA quantifierBound)*) RBRACKET # Backet
    | expression LSQBRACKET (expression (COMMA expression)*) RSQBRACKET # Sqbracket // 中括号
    | LSQBRACKET (quantifierBound (COMMA quantifierBound)*) OP_VBARDASHGT expression RSQBRACKET # Sqbracket
    | LSQBRACKET expression OP_DASHGT expression RSQBRACKET # Sqbracket
    | LSQBRACKET ((IDENTIFIER OP_VBARDASHGT expression) (COMMA (IDENTIFIER OP_VBARDASHGT expression))*) RSQBRACKET # Sqbracket
    | LSQBRACKET ((IDENTIFIER COLON expression) (COMMA (IDENTIFIER COLON expression))*) RSQBRACKET # Sqbracket
    | LSQBRACKET expression ReservedWord_EXCEPT
                 ((BANG (DOT IDENTIFIER | LSQBRACKET (expression (COMMA expression)*) RSQBRACKET)+ OP_EQ expression)
                  (COMMA (BANG
                    (DOT IDENTIFIER | LSQBRACKET (expression (COMMA expression)*) RSQBRACKET)+
                        OP_EQ expression))*) RSQBRACKET # Sqbracket
    | expression DOT IDENTIFIER # Exp2
    | LTUPLE ((expression (COMMA expression)*))? RTUPLE # Tuple
    | LSQBRACKET expression RSQBRACKETUNDER expression  # RsqbracketUnder
    | LTUPLE expression RTUPLEUNDER expression # RightTupleUnder
    | (ReservedWord_WF_ | ReservedWord_SF_) expression LPAREN expression RPAREN # WF_SF
    | ReservedWord_IF expression ReservedWord_THEN expression ReservedWord_ELSE expression # If
    // TODO | ReservedWord_CASE
    | ReservedWord_LET (operatorDefinition | functionDefinition | moduleDefinition)+ ReservedWord_IN expression # Let
    | (OP_LAND expression)+  # Logic
    | (OP_LAND2 expression)+ # Logic
    | (OP_LOR expression)+   # Logic
    | (OP_LOR2 expression)+  # Logic
    | expression OP_LAND expression # Logic
    | expression OP_LAND2 expression # Logic
    | expression OP_LOR expression # Logic
    | expression OP_LOR2 expression # Logic
    | NUMBER # NumExp
    | STRING # StrExp
    | AT # AtExp
    ;

//infixOp : OP_IN | OP_PLUS | OP_DASH |OP_DIV | OP_EQ | OP_LAND | OP_LAND2 | OP_LOR | OP_LOR2 | INFIXOP ;

/* 词法 */
// 关键字
ReservedWord_ASSUME : 'ASSUME' ;
ReservedWord_ELSE : 'ELSE' ;
ReservedWord_LOCAL : 'LOCAL' ;
ReservedWord_ASSUMPTION : 'ASSUMPTION' ;
ReservedWord_MODULE : 'MODULE' ;
ReservedWord_VARIABLE : 'VARIABLE' ;
ReservedWord_AXIOM : 'AXIOM' ;
ReservedWord_EXCEPT : 'EXCEPT' ;
ReservedWord_OTHER : 'OTHER' ;
ReservedWord_VARIABLES : 'VARIABLES' ;
ReservedWord_CASE : 'CASE' ;
ReservedWord_EXTENDS : 'EXTENDS' ;
ReservedWord_SF_ : 'SF_' ;
ReservedWord_WF_ : 'WF_' ;
ReservedWord_CHOOSE : 'CHOOSE' ;
ReservedWord_IF : 'IF' ;
ReservedWord_WITH : 'WITH' ;
ReservedWord_CONSTANT : 'CONSTANT' ;
ReservedWord_IN : 'IN' ;
ReservedWord_THEN : 'THEN' ;
ReservedWord_CONSTANTS : 'CONSTANTS' ;
ReservedWord_INSTANCE : 'INSTANCE' ;
ReservedWord_THEOREM : 'THEOREM' ;
ReservedWord_COROLLARY : 'COROLLARY' ;
ReservedWord_LET : 'LET' ;
ReservedWord_BY : 'BY';
ReservedWord_HAVE : 'HAVE' ;
ReservedWord_QED : 'QED' ;
ReservedWord_TAKE : 'TAKE' ;
ReservedWord_DEF : 'DEF' ;
ReservedWord_HIDE : 'HIDE' ;
ReservedWord_RECURSIVE : 'RECURSIVE' ;
ReservedWord_USE : 'USE' ;
ReservedWord_DEFINE : 'DEFINE' ;
ReservedWord_PROOF : 'PROOF' ;
ReservedWord_WITNESS : 'WITNESS' ;
ReservedWord_PICK : 'PICK' ;
ReservedWord_DEFS : 'DEFS' ;
ReservedWord_PROVE : 'PROVE' ;
ReservedWord_SUFFICES : 'SUFFICES' ;
ReservedWord_NEW : 'NEW' ;
ReservedWord_LAMBDA : 'LAMBDA' ;
ReservedWord_STATE : 'STATE' ;
ReservedWord_ACTION : 'ACTION' ;
ReservedWord_TEMPORAL : 'TEMPORAL' ;
ReservedWord_OBVIOUS : 'OBVIOUS' ;
ReservedWord_OMITTED : 'OMITTED' ;
ReservedWord_LEMMA : 'LEMMA' ;
ReservedWord_PROPOSITION : 'PROPOSITION' ;
ReservedWord_ONLY : 'ONLY' ;

OP_LAND : '\\land' ;
OP_LAND2 : '/\\' ; //{setText("bla");}
OP_LOR : '\\lor' ;
OP_LOR2 : '\\/' ;   // or
OP_IN : '\\in' ;  // 属于
OP_DASH : '-' ;
OP_PLUS : '+' ;
OP_ASTER : '*' ; // 乘
OP_DIV : '\\div' ;
OP_PERCENT : '%'; // 取模
OP_EQ : '=' ;

PREFIXOP
    : OP_DASH
    | OP_NEG
    | OP_SQUARE
    | OP_DIAMOND
    | OP_DOMAIN
    | OP_ENABLED
    | OP_POWERSET
    | OP_UNCHANGED
    | OP_UNION
    ;

INFIXOP
    : OP_BANGBANG
    | OP_SHARP
    | OP_SHARPSHARP
    | OP_DOLLAR
    | OP_DOLLARDOLLAR
    | OP_PERCENT
    | OP_PERCENTPERCENT
    | OP_AMP
    | OP_AMPAMP
    | OP_OPLUS
    | OP_OMINUS
    | OP_ODOT
    | OP_OSLASH
    | OP_OTIMES
    | OP_ASTER
    | OP_ASTERASTER
    | OP_PLUS
    | OP_PLUSPLUS
    | OP_DASH
    | OP_DASHPLUSDASHGT
    | OP_DASHDASH
    | OP_DASHVBAR
    | OP_DOTDOT
    | OP_DOTDOTDOT
    | OP_SLASH
    | OP_SLASHSLASH
    | OP_NOTEQ
    | OP_COLONCOLONEQ
    | OP_COLONEQ
    | OP_COLONGT
    | OP_LT
    | OP_LTCOLON
    | OP_EQ
    | OP_EQLT
    | OP_IMPLY
    | OP_EQVBAR
    | OP_GT
    | OP_GTEQ
    | OP_QUERY
    | OP_ATAT
    | OP_SUBTRACT
    | OP_CARET
    | OP_CARETCARET
    | OP_VBAR
    | OP_VBARDASH
    | OP_VBAREQ
    | OP_VBARVBAR
    | OP_TILDEGT
    | DOT
    | OP_LTEQ
    | OP_APPROX
    | OP_GTEQ
    | OP_SQSUPSETEQ
    | OP_ASYMP
    | OP_GTGT
    | OP_STAR
    | OP_BIGCIRC
    | OP_IN
    | OP_PREC
    | OP_SUBSET
    | OP_BULLET
    | OP_PRECEQ
    | OP_SUBSETEQ
    | OP_CAP
    | OP_LAND
    | OP_LAND2
    | OP_PROPTO
    | OP_SUCC
    | OP_CDOT
    | OP_LTEQ
    | OP_SIM
    | OP_SUCCEQ
    | OP_CIRC
    | OP_LTLT
    | OP_SIMEQ
    | OP_SUPSET
    | OP_CONG
    | OP_LOR
    | OP_LOR2
    | OP_SQCAP
    | OP_CUP
    | OP_SQCUP
    | OP_UNION
    | OP_DIV
    | OP_SQSUBSET
    | OP_UPLUS
    | OP_DOTEQ
    | OP_SQSUBSETEQ
    | OP_WR
    | OP_EQUIV
    | OP_SQSUPSET
    | OP_NOTIN
    ;

POSTFIXOP
    : OP_CARETPLUS
    | OP_CARETASTER
    | OP_CARETSHARP
    | '\''
    ;

// 操作符
OP_ENABLED : 'ENABLED' ;
OP_UNCHANGED : 'UNCHANGED' ;
OP_POWERSET : 'SUBSET' ;
OP_DOMAIN : 'DOMAIN' ;
OP_UNION : 'UNION' ;
//OP_DASH : '-' ;
OP_NEG : '~' ;    // \lnot or \neg
OP_SQUARE : '[]' ; // 正方形 称作box []F表示F总是正确的
OP_DIAMOND : '<>' ;

OP_BANGBANG : '!!' ;
OP_SHARPSHARP : '##' ;
OP_SHARP : '#' ;    // 不等于
OP_DOLLARDOLLAR : '$$' ;
OP_DOLLAR : '$' ;
OP_PERCENTPERCENT : '%%' ;
//OP_PERCENT : '%' ;
OP_AMPAMP : '&&' ;
OP_AMP : '&' ;
OP_OPLUS : '(+)' ;
OP_OMINUS : '(-)' ;
OP_ODOT : '(.)' ;
OP_OTIMES : '(\\X)' ;
OP_OSLASH : '(/)' ;
OP_ASTERASTER : '**' ;
//OP_ASTER : '*' ;
OP_PLUSPLUS : '++' ;
//OP_PLUS : '+' ;
// DASH '-'
OP_DASHPLUSDASHGT : '-+->' ;
OP_VBARDASHGT : '|->' ;
OP_DASHDASH : '--';
OP_DASHVBAR : '-|' ;
OP_DOTDOTDOT : '...' ;
OP_DOTDOT : '..' ;
OP_SLASHSLASH : '//' ;
OP_SLASH : '/' ;
OP_NOTEQ : '/=' ;   // 不等于 或#
//OP_LAND : '\\land' ;
//OP_LAND2 : '/\\' ;   // and
OP_COLONCOLONEQ : '::=' ;
OP_COLONEQ : ':=' ;
OP_COLONGT : ':>' ;
OP_LTCOLON : '<:' ;
OP_EQUIV : '<=>' ; // 恒等于
OP_LTEQ : '<=' ;
OP_LT : '<' ;

OP_EQLT : '=<' ; // =< 和 <= 是都是小于等于的意思
OP_IMPLY : '=>' ; // 推导 如F=>G
OP_EQVBAR : '=|' ;
//OP_EQ : '=' ;

OP_GTEQ : '>=' ;
OP_GT : '>' ;
OP_QUERY : '??' ;
OP_ATAT : '@@' ;
//OP_LOR : '\\lor' ;
//OP_LOR2 : '\\/' ;   // or
OP_SUBTRACT : '\\' ;

OP_CARETCARET : '^^' ;
OP_CARET : '^' ;
OP_VBARDASH : '|-' ;
OP_VBAREQ : '|=' ;
OP_VBARVBAR : '||' ;
OP_VBAR : '|' ;
OP_TILDEGT : '~>' ;
// .
//OP_IN : '\\in' ;
OP_NOTIN : '\\notin' ;
OP_LTLT : '\\ll' ; // 远小于
OP_GTGT : '\\gg' ; // 远大于

OP_PREC : '\\prec' ;
OP_PRECEQ : '\\preceq' ;
OP_SUBSETEQ : '\\subseteq' ;
OP_SUBSET : '\\subset' ;
OP_SQSUBSET : '\\sqsubset' ;
OP_SQSUBSETEQ : '\\sqsubseteq' ;

OP_SUCC : '\\succ' ;
OP_SUCCEQ : '\\succeq' ;
OP_SUPSETEQ : '\\supseteq' ;
OP_SUPSET : '\\supset' ;
OP_SQSUPSET : '\\sqsupset' ;
OP_SQSUPSETEQ : '\\sqsupseteq' ;

//OP_DIV : '\\div' ;
OP_CDOT : '\\cdot' ;
OP_CIRC : '\\circ' ;
OP_BULLET : '\\bullet' ;
OP_STAR : '\\star' ;
OP_BIGCIRC : '\\bigcirc' ;
OP_SIM : '\\sim' ;
OP_SIMEQ : '\\simeq' ;
OP_ASYMP : '\\asymp' ;
OP_APPROX : '\\approx' ; // 约等于
OP_CONG : '\\cong' ;
OP_DOTEQ : '\\doteq' ;
OP_DASHGT : '->' ; // 右箭头
OP_LTDASH : '<-' ; // 左箭头
OP_CAP : '\\cap' ; // 交集
OP_SQCAP : '\\sqcap' ;
OP_CUP : '\\cup' ; // 并集
OP_SQCUP : '\\sqcup' ;
OP_UPLUS : '\\uplus' ;
OP_TIMES : '\\times' ;
OP_WR : '\\wr' ;
OP_PROPTO : '\\propto' ;
OP_CARETPLUS : '^+' ;
OP_CARETASTER : '^*' ;
OP_CARETSHARP : '^#' ;
OP_DASHDOT : '-.' ;  // only used when define '-' prefix operator
QUANTIFIER_EE : '\\EE' ;
QUANTIFIER_E : '\\E' ;
QUANTIFIER_AA : '\\AA' ;
QUANTIFIER_A : '\\A' ;

// 符号
LTUPLE : '<<' ;  // 尖括号
RTUPLE : '>>' ;
RTUPLEUNDER : '>>_' ;
LPAREN : '(' ;
RPAREN : ')' ;
LBRACKET : '{' ;
RBRACKET : '}' ;
LSQBRACKET : '[' ;
RSQBRACKET : ']' ;
RSQBRACKETUNDER : ']_' ;
UNDER  : '_' ;
COMMA  : ',' ;
BANG : '!' ;
AT : '@' ;
DOT : '.' ;
COLONCOLON : '::' ; // 啥意思？
COLON : ':' ;
SEMICOLON : ';' ;

SEPARATOR : '---' ('-')+ ;
MODULE_END : '===' ('=')+ ;
DEFINE : '==' ;

NUMBER : NUMBERLEXEME ;
NUMBERLEXEME
    : NUMERAL+
    | NUMERAL* '.' NUMERAL+
    | ('\\b' | '\\B') ('0' | '1')+
    | ('\\o' | '\\O') [0-7]+
    | ('\\h' | '\\H') [0-9abcdefABCDEF]+
    ;
NUMERAL : [0-9] ;
WS : [ \t\r\n]+ -> skip ; // 丢弃空白符
COMMENT : '(*' .*? '*)' -> skip ; // 丢弃注释
LINE_COMMENT : '\\*' .*? '\n' -> skip ; // 丢弃行内注释

// 歧义如何解决？直接将语法分析器中的NAME改成IDENTIFIER？
IDENTIFIER : NAME ;
NAME : (NAMECHAR* LETTER NAMECHAR*) ;  //[^(ReservedWord_WF_ | ReservedWord_SF_) NAMECHAR+] ;
//IDENTIFIERORTUPLE : (IDENTIFIER | LTUPLE (IDENTIFIER (COMMA IDENTIFIER)*) RTUPLE) ;
PROOFSTEPID : OP_LT (NUMERAL+ | OP_ASTER) OP_GT (LETTER | NUMERAL | UNDER)+ ;
BEGINSTEPTOKEN : OP_LT (NUMERAL+ | OP_ASTER | OP_PLUS) OP_GT (LETTER | NUMERAL)* DOT*;
// .*?非贪婪匹配 获取一些字符 直到发现匹配后续子规则的字符为止 P117
STRING : '"' .*? '"' ; // 字符串匹配 '"' ('""'|~'"')* '"'

fragment
ESC : '\\"' | '\\\\' ;
fragment
LETTER : [a-zA-Z] ;
fragment
NAMECHAR : LETTER | NUMERAL | UNDER ;
