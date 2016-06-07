(*
 * SNU 4541.664A Program Analysis
 * Skeleton code for davinci-code analyzer
 *)

open Program
open GraphPgm

(* Type definitions (Do not modify) *)

type result = 
  | YES 
  | NO 
  | DONT_KNOW

(* Stringfy functions *)
let result_to_str : result -> string = fun a -> match a with
  | YES -> "YES, this is davinci code"
  | NO  -> "NO, this is NOT davinci code"
  | DONT_KNOW -> "I don't know"

(* TODO: you have to implement from here *)
let daVinciAnalyzer : pgm_graph -> result = fun pgm_g ->
  failwith "not implemented"
