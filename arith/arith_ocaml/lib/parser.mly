%token SUCC
%token PRED
%token TRUE
%token FALSE
%token LPAREN
%token RPAREN
%token EOF

%start toplevel
%type <Core.Arith.arith> toplevel 

%%

toplevel: e = expression EOF { e };


expression:
  | TRUE                          { Core.Arith.ATrue }
  | FALSE                         { Core.Arith.AFalse}
  | s = SUCC e = expression       { Core.Arith.ASucc(e) }
  | s = PRED e = expression       { Core.Arith.APred(e) }
  | LPAREN e = expression RPAREN  { e }
