
{
open Parser
open Lexing

module StringMap = Map.Make(String)

let keyword_list =
  [ "as", AS;
    "end", END;
    "fun", FUN;
    "in", IN;
    "let", LET;
    "match", MATCH;
    "with", WITH; ]

let keywords =
  List.fold_left
    (fun acc (keyword, token) ->
      StringMap.add keyword token acc)
    StringMap.empty
    keyword_list

let newline lexbuf =
  let pos = lexbuf.lex_curr_p in
  let pos_lnum = pos.pos_lnum + 1 in
  let pos_bol = pos.pos_cnum in
  let pos' = { pos with pos_lnum; pos_bol } in
  lexbuf.lex_curr_p <- pos'

type error =
  | Illegal_character of char

exception Error of error * Lexing.position

}

let newline = ('\013'* '\010')
let blank = [' ' '\009' '\012']

let lowercase = ['a'-'z']
let uppercase = ['A'-'Z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9']

rule token = parse
  | newline { newline lexbuf; token lexbuf }
  | blank + { token lexbuf }
  | "->" { ARROW }
  | '|' { BAR }
  | '=' { EQUALS }
  | '#' { HASH }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | ";;" { SEMISEMI }
  | "_" { UNDERSCORE }
  | lowercase identchar *
      { let s = Lexing.lexeme lexbuf in
        match StringMap.find s keywords with
        | token -> token
        | exception Not_found -> LIDENT s }
  | uppercase identchar *
      { let s = Lexing.lexeme lexbuf in
        match StringMap.find s keywords with
        | token -> token
        | exception Not_found -> UIDENT s }
  | _
      { let char = Lexing.lexeme_char lexbuf 0 in
        let pos = lexbuf.lex_start_p in
        raise (Error(Illegal_character char, pos))
      }
