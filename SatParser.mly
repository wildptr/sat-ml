%{
open Term
%}

%token EOF
%token <string> IDENT
%token TRUE
%token FALSE
%token NOT
%token EQUIV
%token AND
%token OR
%token IMP
%token LPAREN
%token RPAREN

%left EQUIV
%right IMP
%left OR
%left AND
%nonassoc NOT

%start <Term.term> top

%%

top: term EOF {$1}

term:
  TRUE { Const true }
| FALSE { Const false }
| IDENT { Var $1 }
| NOT term { Not $2 }
| term EQUIV term { Equiv ($1, $3) }
| term IMP term { Imp ($1, $3) }
| term OR term { Or ($1, $3) }
| term AND term { And ($1, $3) }
| LPAREN term RPAREN {$2}
