%{
  open Term
%}
%token <string> IDENT
%token EOF
%token LPAREN RPAREN
%token ARROW EQUIV AND OR NOT BOT TOP
%token STRAY
%nonassoc EQUIV
%right ARROW
%right OR
%right AND
%nonassoc NOT
%start main
%type <Term.pnterm> main
%type <Term.pnterm> expression

%%

main:
  | expression EOF { $1 }
expression:
  | IDENT { PNVarName $1 }
  | LPAREN expression RPAREN { $2 }
  | expression EQUIV expression {
      let t1 = $1 in
      let t2 = $3 in
      PNAnd (PNArrow (t1,t2),PNArrow (t2,t1))
  }
  | expression ARROW expression { PNArrow ($1,$3) }
  | expression OR expression { PNOr ($1,$3) }
  | expression AND expression { PNAnd ($1,$3) }
  | NOT expression { PNArrow ($2,PNBot) }
  | TOP { PNTop }
  | BOT { PNBot }
;
