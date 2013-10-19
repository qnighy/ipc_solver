{
  open Parser
  let keyword_table = Hashtbl.create 1010
  let latex_table = Hashtbl.create 10101
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
    [ "IMPLIES", ARROW;
      "Implies", ARROW;
      "implies", ARROW;
      "IFF", EQUIV;
      "Iff", EQUIV;
      "iff", EQUIV;
      "AND", AND;
      "And", AND;
      "and", AND;
      "OR", OR;
      "Or", OR;
      "or", OR;
      "NOT", NOT;
      "Not", NOT;
      "not", NOT;
      "FALSE", BOT;
      "False", BOT;
      "false", BOT;
      "TRUE", TOP;
      "True", TOP;
      "true", TOP;
    ]
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add latex_table kwd tok)
    [ "to", ARROW;
      "Rightarrow", ARROW;
      "supset", ARROW;
      "implies", ARROW;
      "Leftrightarrow", EQUIV;
      "equiv", EQUIV;
      "leftrightarrow", EQUIV;
      "iff", EQUIV;
      "wedge", AND;
      "land", AND;
      "vee", OR;
      "lor", OR;
      "lnot", NOT;
      "neg", NOT;
      "sim", NOT;
      "bot", BOT;
      "top", TOP;
    ]
}
rule token =
  parse [' ' '\t' '\n'] { token lexbuf }
      | "(*" { in_comment lexbuf; token lexbuf }
      | "T" { TOP }
      | (['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*) as id {
          try
            Hashtbl.find keyword_table id
          with Not_found ->
            IDENT id }
      | "\\" (['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9']*) as id {
          Hashtbl.find latex_table id }
      | "=>" { ARROW }
      | "->" { ARROW }
      | "→" { ARROW }
      | "⇒" { ARROW }
      | "<=>" { EQUIV }
      | "<->" { EQUIV }
      | "=" { EQUIV }
      | "⇔" { EQUIV }
      | "&&" { AND }
      | "&" { AND }
      | "＆" { AND }
      | "*" { AND }
      | "/\\" { AND }
      | "∧" { AND }
      | "||" { OR }
      | "|" { OR }
      | "｜" { OR }
      | "+" { OR }
      | "\\/" { OR }
      | "∨" { OR }
      | "~" { NOT }
      | "!" { NOT }
      | "-" { NOT }
      | "￢" { NOT }
      | "_|_" { BOT }
      | "⊥" { BOT }
      | "0" { BOT }
      | "1" { TOP }
      | "(" { LPAREN }
      | "（" { LPAREN }
      | ")" { RPAREN }
      | "）" { RPAREN }
      | eof { EOF }
and in_comment =
  parse "(*" { in_comment lexbuf; in_comment lexbuf }
      | "*)" { () }
      | _ { in_comment lexbuf }
