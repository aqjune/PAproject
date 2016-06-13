(*
 * SNU 4541.664A Program Analysis
 * Skeleton code for davinci-code analyzer
 *)

open Program
open GraphPgm
open DavinciDomain
open AbsDomain
open TraceSemantics

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

module DavinciAnalyzer = TraceAnalyzer(DavinciSemantics)

let daVinciCheck (v:DavinciSemantics.DavinciValue.t) : result =
  let (az, loc) = 
      (DavinciSemantics.DavinciValue.get_az v,
      DavinciSemantics.DavinciValue.get_locs v) in
  let (az_list, loc_list) = 
      (DavinciAZ.to_list az, LocDomain.to_list loc) in
  if (List.length az_list) = 1 && (List.hd az_list) = 415 && (List.length loc_list) = 0 then
    YES
  else if (not (List.exists (fun n -> n = 415) az_list)) then
    NO
  else
    DONT_KNOW

let rec daVinciCheckByList (rl : result list) : result = 
  match rl with
  | [] -> raise (Failure "cannot be nil")
  | h::[] -> h
  | h::t -> 
    let res1 = daVinciCheckByList t in
    let res2 = h in
    match (res1, res2) with
    | (NO, _) -> NO
    | (_, NO) -> NO
    | (YES, YES) -> YES
    | _ -> DONT_KNOW

let daVinciAnalyzer : pgm_graph -> result = fun pgm_g ->
	let (trace:DavinciAnalyzer.TraceDomain.t) = 
      DavinciAnalyzer.runIterativeAlgorithm pgm_g in
	
	let foldedstore = DavinciAnalyzer.TraceDomain.fold 
		(fun k v llacc -> 
		  let ll = DavinciAnalyzer.StoreDomain.to_list v in
      let ll' = List.map (fun (k1,k2) -> (k1, daVinciCheck k2)) ll in
      List.append ll' llacc) 
    trace
    []
  in
  
  let rec f l : result list = 
    match l with
    | [] -> []
    | (k,_)::_ ->
      let (p1, p2) = List.partition (fun (k',_)-> k' = k) l in
      let res2 = f p2 in
      (daVinciCheckByList (snd (List.split p1)))::res2
  in
  let result = f foldedstore in

  if List.exists (fun itm -> itm = YES) result then 
    YES
  else if List.exists (fun itm -> itm = DONT_KNOW) result then
    DONT_KNOW
  else
    NO
