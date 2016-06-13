(*
 * SNU 4541.664A Program Analysis
 * Skeleton for even-odd analyzer
 *)

open Program
open GraphPgm

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

let rec exp_to_str (e:exp) : string =
	Printf.sprintf "(%s)"
  	(match e with
    | NUM i -> Printf.sprintf "%d" i
    | ADD (e1, e2) -> (Printf.sprintf "%s + %s" (exp_to_str e1) (exp_to_str e2)) 
    | NEG e -> Printf.sprintf "- %s" (exp_to_str e)
    | VAR x -> Printf.sprintf "%s" x
    | DEREF x -> Printf.sprintf "*%s" x
    | LOC x -> Printf.sprintf "&%s" x
    | READINT -> Printf.sprintf "readInt")
	
let node_to_str (nd:node) : string = 
	let cmd = get_command nd in
	match cmd with
	| Assign (x, e) -> (Printf.sprintf "%s := %s" x (exp_to_str e))
	| PtrAssign (x, e) -> (Printf.sprintf "*%s := %s" x (exp_to_str e))
	| Assume e -> Printf.sprintf "Assume %s" (exp_to_str e)
	| AssumeNot e -> Printf.sprintf "AssumeNot %s" (exp_to_str e)
	| Skip -> "Skip"

type aZ = AZ_ZERO | AZ_EVEN | AZ_ODD | AZ_BOTTOM | AZ_TOP

type aLoc = VarSet.t

type aValue = aZ * aLoc

type aStore = aValue VarMap.t

type aState = node * aStore


let calc_aZ_join (az1:aZ) (az2:aZ) : aZ = 
	match (az1, az2) with
	| (AZ_BOTTOM, az2) -> az2
	| (az1, AZ_BOTTOM) -> az1
	| (AZ_TOP, az2) -> AZ_TOP
	| (az1, AZ_TOP) -> AZ_TOP
	| (AZ_ZERO, AZ_ZERO) -> AZ_ZERO
  | (AZ_ZERO, AZ_EVEN) -> AZ_EVEN
	| (AZ_ZERO, AZ_ODD) -> AZ_TOP
	| (AZ_EVEN, AZ_ZERO) -> AZ_EVEN
  | (AZ_EVEN, AZ_EVEN) -> AZ_EVEN
	| (AZ_EVEN, AZ_ODD) -> AZ_TOP
	| (AZ_ODD, AZ_ZERO) -> AZ_TOP
  | (AZ_ODD, AZ_ODD) -> AZ_ODD
	| (AZ_ODD, AZ_EVEN) -> AZ_TOP

let get_aZ_to_str (az:aZ) : string =
	match az with
	| AZ_BOTTOM -> "BOTTOM"
	| AZ_TOP -> "TOP"
	| AZ_ZERO -> "0"
	| AZ_ODD -> "ODD"
	| AZ_EVEN -> "EVEN"

let aLoc_fold f locs initval : (var -> 'a -> 'a) -> aLoc -> 'a -> 'a = 
	VarSet.fold f locs initval

let get_aLoc_tolist (aloc:aLoc) : var list =
	VarSet.elements aloc

let get_aLoc_toVarSet (aloc:aLoc) : VarSet.t =
	aloc

let calc_aLoc_join (aloc1:aLoc) (aloc2:aLoc) : aLoc =
	VarSet.union aloc1 aloc2

let get_aLoc_to_str (aloc:aLoc) : string =
	Printf.sprintf "(%s)"
		(VarSet.fold (fun l str -> Printf.sprintf "%s,%s" l str) aloc "")

let new_aValue_num (n:int) : aValue = 
	((if n = 0 then AZ_ZERO else (if n mod 2 = 0 then AZ_EVEN else AZ_ODD)), VarSet.empty)

let new_aValue_loc (l:var) : aValue = 
	(AZ_BOTTOM, VarSet.singleton l)

let get_aValue_locs (av:aValue) : aLoc = 
	snd av

let get_aValue_to_str (av:aValue) : string =
	let (az, aloc) = av in
	Printf.sprintf "<%s,%s>" (get_aZ_to_str az) (get_aLoc_to_str aloc)

let calc_aValue_join (av1:aValue) (av2:aValue) : aValue =
	let (az1, aloc1) = av1 in
	let (az2, aloc2) = av2 in
	(calc_aZ_join az1 az2, calc_aLoc_join aloc1 aloc2)

let calc_aValue_equal (av1:aValue) (av2:aValue) : bool = 
	let (az1, aloc1) = av1 in
	let (az2, aloc2) = av2 in
	az1 = az2 && (VarSet.equal aloc1 aloc2)

let get_aStore_empty = VarMap.empty

let calc_aStore_join (as1:aStore) (as2:aStore) : aStore = 
	VarMap.merge 
		(fun k v1opt v2opt ->
			match (v1opt, v2opt) with
			| None, None -> None
			| None, Some v2 -> Some v2
			| Some v1, None -> Some v1
			| Some v1, Some v2 -> Some (calc_aValue_join v1 v2))
		as1 as2
	
let calc_aStore_equal (as1:aStore) (as2:aStore) : bool = 
	VarMap.equal (fun av1 av2 -> calc_aValue_equal av1 av2) as1 as2
	
let calc_aStore_update (x:var) (v:aValue) (st:aStore) : aStore =
	let st' = VarMap.remove x st in
	VarMap.add x v st

let get_aStore_to_str (ast:aStore) : string =
	let astlist = VarMap.bindings ast in
	List.fold_right
		(fun (key,aval) str -> Printf.sprintf "%s = %s\n%s" key (get_aValue_to_str aval) str)
		astlist
		""

let get_aState_node (ast:aState) : node = 
	fst ast
	
let get_aState_aStore (ast:aState) : aStore = 
	snd ast

let get_aState_to_str (ast:aState) : string =
	let (nd, st) = ast in
	Printf.sprintf "%d : %s" (get_nodeid nd) (get_aStore_to_str st)

let get_aStateList_to_str (asts:aState list) : string =
  String.concat "\n" (List.map get_aState_to_str asts)

let calc_aState_equal (as1:aState) (as2:aState) : bool = 
	let (as1n, as1st) = as1 in
	let (as2n, as2st) = as2 in
	(as1n = as2n) && (calc_aStore_equal as1st as2st)

let calc_aState_empty nd : aState = 
  (nd, VarMap.empty)

let calc_aState_join (as1:aState) (as2:aState) : aState = 
	let (nd1, ast1) = as1 in
  let (nd2, ast2) = as2 in
  if nd1 = nd2 then (nd1, calc_aStore_join ast1 ast2)
  else let _ = raise (Failure "nd1 and nd2 must be equal") in as1

let calc_aplus ((x1, x2):(aValue * aValue)) : aValue = 
	let aZvalue = match (fst x1, fst x2) with
	| (AZ_ZERO, x2) -> x2
	| (x1, AZ_ZERO) -> x1
	| (AZ_TOP, x2) -> AZ_TOP
	| (x1, AZ_TOP) -> AZ_TOP
	| (AZ_BOTTOM, x2) -> AZ_BOTTOM
	| (x1, AZ_BOTTOM) -> AZ_BOTTOM
	| (AZ_EVEN, AZ_EVEN) -> AZ_EVEN
	| (AZ_ODD, AZ_ODD) -> AZ_EVEN
	| (AZ_EVEN, AZ_ODD) -> AZ_ODD
	| (AZ_ODD, AZ_EVEN) -> AZ_ODD
	in (aZvalue, VarSet.empty)

let calc_aminus (x:aValue) : aValue = 
	let (aZval, aLocval) = x in (aZval, VarSet.empty)

let calc_aderef (x:var) (aM:aStore) : aValue = 
	let (aZval, aLocval) = VarMap.find x aM in
	VarSet.fold 
    (fun x' (azacc, alacc) -> 
      let (az, al) = VarMap.find x' aM in
      (calc_aZ_join az azacc, VarSet.union al alacc)) 
		aLocval (AZ_BOTTOM, VarSet.empty)

let calc_areadint = (AZ_TOP, VarSet.empty)

let rec calc_aE (e:exp) (aM:aStore) : aValue = 
	match e with
	| NUM n -> new_aValue_num n
	| ADD (e1, e2) -> 
		let av1 = calc_aE e1 aM in
		let av2 = calc_aE e2 aM in
		calc_aplus (av1,av2)
	| NEG e -> 
		let av = calc_aE e aM in
		calc_aminus av
	| VAR x -> (VarMap.find x aM)
	| DEREF x -> calc_aderef x aM
	| LOC x -> new_aValue_loc x
	| READINT -> calc_areadint
  
let make_m' node (m:aStore) : aStore = 
  let nodecmd = get_command node in
  match nodecmd with
  | Assign (x, e) -> calc_aStore_update x (calc_aE e m) m
  | PtrAssign (x, e) -> 
    (let v' = VarMap.find x m in
    let locs = get_aValue_locs v' in
    let ev = calc_aE e m in
    let stores : (aStore option) list = List.map (fun x' -> Some (calc_aStore_update x' ev m)) (get_aLoc_tolist locs) in
    let joinedst = List.fold_right 
      (fun st1 st2 -> 
        match (st1, st2) with
        | (None, None) -> None
        | (None, Some st2) -> Some st2
        | (Some st1, None) -> Some st1
        | (Some st1, Some st2) -> Some (calc_aStore_join st1 st2)) stores None
    in 
    match joinedst with
    | None -> raise (Failure "Cannot be none")
    | Some m' -> m')
  | Assume e -> m
  | AssumeNot e -> m
  | Skip -> m

let calc_anext (pgm:pgm_graph) (ast:aState) : aState list =
	let (node, m) = ast in
  let nextlist = next_nodes pgm node in
	List.map (fun nextnode -> (nextnode, make_m' nextnode m)) nextlist

let rec calc_api (pgm:pgm_graph) (astlist:aState list) : (aState list) list =
	let allnodes = all_nodes pgm in
	List.fold_right
		(fun nd ls -> 
			let (ndlist, _) = List.partition (fun (nd', st') -> nd = nd') astlist in
      if ndlist = [] then ls else ndlist::ls)
		allnodes
		[]



module StateMap = Map.Make(Node)

type statemap = aState StateMap.t

let statemap_to_str (sm:statemap) : string =
	StateMap.fold 
		(fun (key:Node.t) (v:aState) (str:string) ->
			Printf.sprintf "[%s] : [%s]\n%s" (node_to_str key) (get_aState_to_str v) str)
		sm
		""

let doNext (pgm:pgm_graph) (t0:statemap) (t:statemap) : statemap =
  let _ = print_endline "Before doNext() : " in
  let _ = print_endline (statemap_to_str t) in
	
  let (_, astlist) = List.split (StateMap.bindings t) in
	
  let astlist_next:aState list list = List.map (fun ast -> calc_anext pgm ast) astlist in
	let astlist_next = List.flatten astlist_next in
  let _ = print_endline "after applying calc_anext() : " in
  let _ = print_endline (get_aStateList_to_str astlist_next) in
  
  let astlist_next_p = calc_api pgm astlist_next in
  let _ = print_endline "after applying calc_api() : " in
  let _ = print_endline (List.fold_right 
    (fun asts str -> Printf.sprintf "--\n%s%s" (get_aStateList_to_str asts) str) 
    astlist_next_p "") in
	
  let tnext = List.fold_right 
		(fun (astl:aState list) (* a list of abstract states with same node *)
					(prev:statemap) -> 
			let nd = 
				match astl with
				| [] -> raise (Failure "doNext() : Cannot be nil")
				| h::t -> get_aState_node h
			in 
			let newastore = List.fold_right
				(fun astate ast' -> calc_aStore_join (get_aState_aStore astate) ast')
        astl
				get_aStore_empty
			in
			StateMap.add nd (nd,newastore) prev
		)
		astlist_next_p
		(StateMap.empty)
  in
  StateMap.merge 
    (fun (key:node) (aopt:aState option) bopt ->
      match (aopt, bopt) with
      | None,None -> None
      | (Some ast1), None -> Some ast1
      | None, (Some ast2) -> Some ast2
      | (Some ast1), (Some ast2) -> Some (calc_aState_join ast1 ast2)
    )
    t0
    tnext

let rec runIterativeAlgorithm (pgm:pgm_graph) (t0:statemap) : statemap =
	let rec _run (pgm:pgm_graph) (t:statemap) (tnext:statemap) (ith:int) : (statemap * int) =
		let _ = print_endline (Printf.sprintf "---- itr %d ----\n%s" ith (statemap_to_str t)) in
		
		if StateMap.equal (fun st1 st2 -> calc_aState_equal st1 st2) t tnext then
			(tnext, ith)
		else
			_run pgm tnext (doNext pgm t0 tnext) (ith + 1)
	in
	let (finalState, itrcnt) = (_run pgm t0 (doNext pgm t0 t0) 0) in
	finalState

let eoAnalyzer: pgm_graph -> result = fun pgm_g ->
  let nd0 = get_start_node pgm_g in
  let ndend = get_end_node pgm_g in
	let t0 = StateMap.add nd0 (nd0, (make_m' nd0 get_aStore_empty)) (StateMap.empty) in
	let t : statemap = runIterativeAlgorithm pgm_g t0 in
  let (nd, (laststore:aStore)) = StateMap.find ndend t in
	
	let res = VarMap.empty in
	VarMap.fold 
		(fun key aval (res:result) -> 
			let (az, aloc) = aval in
			let evb = match az with
				| AZ_ZERO -> EVEN
				| AZ_EVEN -> EVEN
				| AZ_ODD -> ODD
				| AZ_BOTTOM -> NONE
				| AZ_TOP -> DONTKNOW in
			let locs = get_aLoc_toVarSet aloc in
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
