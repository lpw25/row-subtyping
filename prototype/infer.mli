
open Ast
open Types

type error =
  | Typing of Type.t * Type.t * Error.t
  | Binding of var

exception Error of location * error

val infer : Env.t -> definition -> Env.t * Type.t
