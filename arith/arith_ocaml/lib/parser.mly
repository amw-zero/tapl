%{
open Core.Arith
%}

// Values
%token TRUE
%token FALSE
%token ZERO

%token SUCC
%token PRED

%token IF
%token THEN
%token ELSE

%token ISZERO

%token LPAREN
%token RPAREN
%token EOF

%token <string> ID
%token ARROW

%start prog
%type <arith option> prog 

%%

prog: 
  | e = expression EOF { Some e }
  | EOF                { None };

non_app:
  | TRUE                                  { ATrue }
  | FALSE                                 { AFalse}
  | ZERO                                  { AZero }
  | s = SUCC e = expression               { ASucc(e) }
  | s = PRED e = expression               { APred(e) }
  | SUCC e = expression                   { ASucc(e) }
  | PRED e = expression                   { APred(e) }
  | ISZERO e = expression                 { AIsZero(e) }
  | IF e1 = expression THEN e2 = expression ELSE e3 = expression 
                                          { AIfElse(e1, e2, e3) }
expression:
  | na = non_app                          { na }
//  | LPAREN f = expression x = non_app RPAREN { AApplyFunc(f, x) }
  | f = expression x = non_app            { AApplyFunc(f, x) }
  | f = expression LPAREN x = expression RPAREN            { AApplyFunc(f, x) }
  | LPAREN e = expression RPAREN          { e }
  | LPAREN arg = ID RPAREN ARROW body = expression { AArrowFunc(arg, body) } 
