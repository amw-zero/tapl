%token SUCC
%token PRED
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token LPAREN
%token RPAREN
%token EOF

%start prog
%type <Core.Arith.arith option> prog 

%%

prog: 
  | e = expression EOF { Some e }
  | EOF                { None };


expression:
  | TRUE                          { Core.Arith.ATrue }
  | FALSE                         { Core.Arith.AFalse}
  | s = SUCC e = expression       { Core.Arith.ASucc(e) }
  | s = PRED e = expression       { Core.Arith.APred(e) }
  | IF e1 = expression THEN e2 = expression ELSE e3 = expression 
                                  { Core.Arith.AIfElse(e1, e2, e3) }
  | LPAREN e = expression RPAREN  { e }
