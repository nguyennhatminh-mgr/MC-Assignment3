//Student ID: 1712179

grammar MC;

@lexer::header {
from lexererr import *
}

@lexer::members {
def emit(self):
    tk = self.type
    if tk == self.UNCLOSE_STRING:       
        result = super().emit();
        raise UncloseString(result.text[1:]);
    elif tk == self.ILLEGAL_ESCAPE:
        result = super().emit();
        raise IllegalEscape(result.text[1:]);
    elif tk == self.ERROR_CHAR:
        result = super().emit();
        raise ErrorToken(result.text); 
    else:
        return super().emit();
}

options{
	language=Python3;
}

program: manydeclarations EOF;  

manydeclarations: declaration+;
// manydeclarations: manydeclarations declaration | declaration; 

declaration: var_declaration | func_declaration;

//variable declaration
var_declaration: primitive_type var_list SEMI;

primitive_type: INTTYPE | BOOLTYPE | STRINGTYPE | FLOATTYPE;

var_one: ID | array_id_var;

array_id_var: ID LSB INTLIT RSB;

var_list: var_one (COMMA var_one)*;

//function declaration
func_declaration: func_type LB func_list_para? RB block_statement;

func_type: (primitive_type (ID | array_id_func)) | (VOIDTYPE ID);

array_id_func: LSB RSB ID;

func_list_para: func_list_para_one (COMMA func_list_para_one)*;

func_list_para_one: primitive_type (ID | ID LSB RSB) ; 

// block_statement:  LP(var_declaration* statement* | statement* var_declaration*) RP;
block_statement:  LP(list_in_block)* RP;
// block_statement:  LP(var_declaration | statement)* RP;

list_in_block:var_declaration | statement;
//function call
funcall: ID LB list_expression? RB;
list_expression: expression (COMMA expression)*;
//literals
literals: INTLIT | FLOAT_LITERAL | STRING_LIT | BOOLEAN_LIT;

//operand definition
operand: literals
        | ID
        | funcall
        ;
//expression
expression: expression1 ASSIGN expression
        |   expression1
        ;
expression1: expression1 OR expression2
        |   expression2
        ;
expression2: expression2 AND expression3
        |   expression3
        ;
expression3: expression4 EQUAL expression4
        |   expression4 NOT_EQUAL expression4
        |   expression4
        ;
expression4: expression5 LESS_THAN expression5
        |   expression5 LESS_THAN_OR_EQUAL expression5
        |   expression5 GREATER_THAN expression5
        |   expression5 GREATER_THAN_OR_EQUAL expression5
        |   expression5
        ;
expression5: expression5 ADD expression6
        |   expression5 SUB expression6
        |   expression6
        ;
expression6: expression6 DIVISION expression7
        |   expression6 MULTIPLICATION expression7
        |   expression6 MODULUS expression7
        |   expression7
        ;
expression7: SUB expression7
        |   NOT expression7
        |   expression8
        ;
expression8: expression9 LSB expression RSB
        |   expression9
        ;
expression9: LB expression RB
        | operand
        ;

//statement
statement: callstatement
        | ifstatement
        | dowhile_statement
        | forstatement
        | breakstatement
        | continuestatement
        | returnstatement
        | block_statement
        | expressionstatement;

callstatement: funcall SEMI;

ifstatement: IF LB expression RB statement (ELSE statement)?;

dowhile_statement: DO statement+ WHILE expression SEMI;

forstatement: FOR LB expression SEMI expression SEMI expression RB statement;

breakstatement: BREAK SEMI;

continuestatement: CONTINUE SEMI;

returnstatement: RETURN expression? SEMI;

expressionstatement: expression SEMI;
// program  : mctype 'main' LB RB LP body? RP EOF ;

// mctype: INTTYPE | VOIDTYPE ;

// body: funcall SEMI;

// exp: funcall | INTLIT ;

// funcall: ID LB exp? RB ;

//key words

INTTYPE: 'int' ;

VOIDTYPE: 'void' ;

BOOLTYPE: 'boolean';

BREAK: 'break';

CONTINUE: 'continue';

ELSE: 'else';

FOR: 'for';

FLOATTYPE: 'float';

IF: 'if';

RETURN: 'return';

DO: 'do';

WHILE: 'while';

//TRUE: 'true';

//FALSE: 'false';

STRINGTYPE: 'string';

//operators

ADD: '+';

MULTIPLICATION: '*';

NOT: '!';

OR: '||';

NOT_EQUAL: '!=';

LESS_THAN: '<';

LESS_THAN_OR_EQUAL: '<=';

ASSIGN: '=';

SUB: '-';

DIVISION: '/';

MODULUS: '%';

AND: '&&';

EQUAL: '==';

GREATER_THAN: '>';

GREATER_THAN_OR_EQUAL: '>=';

// literals


INTLIT: [0-9]+;

// FLOATLIT: FRACPART EXPOPART?  | [0-9]+ EXPOPART;

// fragment FRACPART: INTLIT? '.' INTLIT | INTLIT '.';

// fragment EXPOPART: [Ee] SIGN? INTLIT;

// fragment SIGN: '-';

// FLOAT_LITERAL: (INTLIT? '.' INTLIT | INTLIT '.') ([Ee] '-'? INTLIT)? | INTLIT [Ee] '-'? INTLIT;

FLOAT_LITERAL: INTLIT [Ee] '-'? INTLIT | (INTLIT? '.' INTLIT | INTLIT '.') ([Ee] '-'? INTLIT)?;

BOOLEAN_LIT: 'true' | 'false';

//seperators

LB: '(' ;

RB: ')' ;

LP: '{';

RP: '}';

SEMI: ';' ;

COMMA: ',';

LSB: '[';

RSB: ']';

WS : [ \t\r\n]+ -> skip ; // skip spaces, tabs, newlines

//comments

BLOCK_COMMENT: '/*' .*? '*/' -> skip;

LINE_COMMENT: '//' ~[\r\n]* -> skip;

fragment LEGAL_ESCAPE: '\\b' | '\\f' | '\\r' | '\\n' | '\\t' | '\\"' | '\\''\\';

UNCLOSE_STRING:
    '"' (~[\n\r\b\f\t\\"] | LEGAL_ESCAPE)* ;// {raise UncloseString(self.text[1:])};

ILLEGAL_ESCAPE:
    UNCLOSE_STRING '\\' ~[nrbft"\\] ;// { raise IllegalEscape(self.text[1:])};

STRING_LIT:
    UNCLOSE_STRING  '"' {self.text = self.text[1:-1]};

ID : [a-zA-Z_][a-zA-Z0-9_]* ;

ERROR_CHAR:. ;//{raise ErrorToken(self.text)};
// ERROR_CHAR: .;
// UNCLOSE_STRING: .;
// ILLEGAL_ESCAPE: .;