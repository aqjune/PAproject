(*
 * SNU 4541.664A Program Analysis
 * Definition of original program
 *)

type var = string
module Var =
struct
  type t = string
  let compare = compare
end
  
type cmd = 
  | ASSIGN of var * exp
  | PTRASSIGN of var * exp
  | SEQ of cmd * cmd
  | IF of exp * cmd * cmd
  | REPEAT of cmd * exp
and exp =
  | NUM of int
  | ADD of exp * exp
  | NEG of exp
  | VAR of var
  | DEREF of var
  | LOC of var
  | READINT

type program = cmd

let rec exp_to_str = function
  | NUM i -> string_of_int i
  | ADD (e1, e2) -> "(" ^ exp_to_str e1 ^ " + " ^ (exp_to_str e2) ^ ")"
  | NEG e -> "-(" ^ exp_to_str e ^ ")"
  | VAR x -> x
  | DEREF x -> "*" ^ x
  | LOC x -> "&" ^ x
  | READINT -> "readInt()"

let rec cmd_to_str = function
  | ASSIGN (x, e) -> x ^ " := " ^ exp_to_str e
  | PTRASSIGN (x, e) -> "*" ^ x ^ " := "^ exp_to_str e
  | SEQ (c1, c2) -> cmd_to_str c1 ^ ";\n" ^ cmd_to_str c2
  | IF (e, c1, c2) -> 
    "if (" ^ exp_to_str e ^ ")" ^ cmd_to_str c1 ^ "\n" ^ cmd_to_str c2
  | REPEAT (c, e) -> 
    "repeat (" ^ cmd_to_str c ^ ") until (" ^ exp_to_str e ^ ")"
