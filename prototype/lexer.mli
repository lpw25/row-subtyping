
open Lexing
open Parser

type error =
  | Illegal_character of char

exception Error of error * Lexing.position

val token : lexbuf -> token
