%token SUCC
%token PRED
%token TRUE
%token FALSE
%token LPAREN
%token RPAREN
%token EOF

%start toplevel

%%

toplevel: e = expression EOF { e };

expression:
  | TRUE                  {Core.Arith.TTrue}
  | s = SUCC expression   {Core.Arith.succ}

