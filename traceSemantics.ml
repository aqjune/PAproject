open Program
open GraphPgm
open DomFunctor
open AbsDomain
open AbsSemantics

module TraceAnalyzer (Semantics:SEMANTICS) = 
struct
  module StoreDomain = Semantics.StoreDomain
  module StateDomain = 
  struct
    include ProductDomain(NodeDomain)(StoreDomain)
    let node (ast:t) : NodeDomain.t = 
      fst ast
      
    let store (ast:t) : StoreDomain.t = 
      snd ast

    let to_str (ast:t) : string =
      let (nd, st) = ast in
      Printf.sprintf "%s" (StoreDomain.to_str st)

    let list_to_str (asts:t list) : string =
      String.concat "\n" (List.map to_str asts)

    let empty nd : t = 
      make nd (StoreDomain.bot)
  end

  type aState = StateDomain.t

  let calc_anext (pgm:pgm_graph) (ast:aState) : aState list =
    let (node, m) = ast in
    let (nextlist:NodeDomain.t list) = NodeDomain.next_nodes pgm node in
    List.map 
        (fun (nextnode:NodeDomain.t) -> 
          StateDomain.make nextnode (Semantics.make_m' nextnode m)) 
        nextlist

  let rec calc_api (pgm:pgm_graph) (astlist:aState list) : (aState list) list =
    let (allnodes:GraphPgm.node list) = all_nodes pgm in
    List.fold_right
      (fun (nd:GraphPgm.node) ls -> 
        let (ndlist, _) = List.partition (fun (nd', st') -> (NodeDomain.ELT nd) = nd') astlist in
        if ndlist = [] then ls else ndlist::ls)
      allnodes
      []


  module TraceDomain = 
  struct
    include FunDomain(NodeDomain)(Semantics.StoreDomain)
    let initial (nd0:NodeDomain.t) = 
      make [(nd0, (Semantics.make_m' nd0 StoreDomain.bot))] 
  end

  type trace = TraceDomain.t

  let trace_to_str (sm:trace) : string =
    TraceDomain.fold 
      (fun (key:NodeDomain.t) (v:StoreDomain.t) (str:string) ->
        Printf.sprintf "[%s] : [%s]\n%s" (NodeDomain.to_str key) (StoreDomain.to_str v) str)
      sm
      ""

  let doNext (pgm:pgm_graph) (t0:trace) (t:trace) : trace =
    let _ = print_endline "Before doNext() : " in
    let _ = print_endline (trace_to_str t) in
    
    let (astlist:aState list) = TraceDomain.to_list t in
    
    let astlist_next:aState list list = List.map (fun (ast:aState) -> calc_anext pgm ast) astlist in
    let astlist_next = List.flatten astlist_next in
    let _ = print_endline "after applying calc_anext() : " in
    let _ = print_endline (StateDomain.list_to_str astlist_next) in
    
    let astlist_next_p = calc_api pgm astlist_next in
    let _ = print_endline "after applying calc_api() : " in
    let _ = print_endline (List.fold_right 
      (fun asts str -> Printf.sprintf "--\n%s%s" (StateDomain.list_to_str asts) str) 
      astlist_next_p "") in
    
    let tnext = List.fold_right 
      (fun (astl:aState list) (* a list of abstract states with same node *)
            (prev:trace) -> 
        let nd = 
          match astl with
          | [] -> raise (Failure "doNext() : Cannot be nil")
          | h::t -> StateDomain.node h
        in 
        let newastore = List.fold_right
          (fun astate ast' -> StoreDomain.join (StateDomain.store astate) ast')
          astl
          StoreDomain.bot
        in
        TraceDomain.update prev nd newastore
      )
      astlist_next_p
      (TraceDomain.bot)
    in
    TraceDomain.join t0 tnext

  let rec runIterativeAlgorithm (pgm:pgm_graph) : trace =
    let nd0 = NodeDomain.make (get_start_node pgm) in
	  let t0 = TraceDomain.initial nd0 in
    let rec _run (pgm:pgm_graph) (t:trace) (tnext:trace) (ith:int) : (trace * int) =
      let _ = print_endline (Printf.sprintf "---- itr %d ----\n%s" ith (trace_to_str t)) in
      
      if TraceDomain.eq t tnext then
        (tnext, ith)
      else
        _run pgm tnext (doNext pgm t0 tnext) (ith + 1)
    in
    let (finalState, itrcnt) = (_run pgm t0 (doNext pgm t0 t0) 0) in
    finalState


end
