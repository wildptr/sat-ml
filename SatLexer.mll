{
open Lexing
open SatParser

exception Error of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with
      pos_bol = lexbuf.lex_curr_pos;
      pos_lnum = pos.pos_lnum + 1 }

}

let white = [' ' '\t']+
let newline = '\n'
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*

rule lex = parse
  | white       { lex lexbuf }
  | newline     { next_line lexbuf; lex lexbuf }
  | id          { IDENT (Lexing.lexeme lexbuf) }
  | "⊤"         { TRUE }
  | "⊥"         { FALSE }
  | "¬"         { NOT }
  | "↔"         { EQUIV }
  | "∧"         { AND }
  | "∨"         { OR }
  | "→"         { IMP }
  | '('         { LPAREN }
  | ')'         { RPAREN }
  | eof         { EOF }
  | _ { raise (Error ("Unexpected character: " ^ Lexing.lexeme lexbuf)) }
