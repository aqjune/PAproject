(*
 * SNU 4541.664A Program Analysis
 * Skeleton for even-odd analyzer
 *)

open Program
open GraphPgm
open DomFunctor
open AbsDomain
open EvenOddDomain
open TraceSemantics

(* Type definitions (Do not modify) *)

module VarMap = Map.Make(Var)
module VarSet = Set.Make(Var)

type num_result =
  | NONE
  | ODD
  | EVEN
  | DONTKNOW

type loc_result = VarSet.t

type result = (num_result * loc_result) VarMap.t

(* Stringfy functions *)

let num_result_to_str = function
  | NONE -> "no number"
  | ODD -> "odd"
  | EVEN -> "even"
  | DONTKNOW -> "don't know"

let loc_result_to_str res =
  "{" ^ (String.concat ", " (VarSet.elements res)) ^ "}"

let result_to_str : result -> string = fun res ->
  VarMap.fold 
    (fun x (num_res, loc_res) accum_str ->
      let num_str = num_result_to_str num_res in
      let loc_str = loc_result_to_str loc_res in
      (Printf.sprintf "%s --> (%s, %s)" x num_str loc_str) ^ accum_str
    ) res ""



(* TODO: you have to implement from here *)

module EvenOddTraceAnalyzer = TraceAnalyzer(EvenOddSemantics)

let eoAnalyzer: pgm_graph -> result = fun pgm_g ->
  let ndend = NodeDomain.make (get_end_node pgm_g) in
	let (t:EvenOddTraceAnalyzer.TraceDomain.t) = EvenOddTraceAnalyzer.runIterativeAlgorithm pgm_g in
  let laststore = EvenOddTraceAnalyzer.TraceDomain.image t ndend in
	
	EvenOddTraceAnalyzer.StoreDomain.fold 
		(fun key aval (res:result) -> 
			let (az, aloc) = aval in
			let evb = match az with
				| EvenOddAZ.ZERO -> EVEN
				| EvenOddAZ.EVEN -> EVEN
				| EvenOddAZ.ODD -> ODD
				| EvenOddAZ.BOT -> NONE
				| EvenOddAZ.TOP -> DONTKNOW 
      in
			let locs = VarSet.of_list (LocDomain.to_list aloc) in
			VarMap.add key (evb, locs) res)
		laststore
		(VarMap.empty)
  (*
    If your analyzer concluded that 'x' is (even, {}) and 'y' is (nan,{p}), then
    you can make your result as follow.

    let res = VarMap.empty in
    let res = VarMap.add "x" (EVEN, VarSet.empty) res in
    let res = VarMap.add "y" (NONE, VarSet.add "p" VarSet.empty) res in
    res

  *)
