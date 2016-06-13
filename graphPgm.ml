(*
 * SNU 4541.664A Program Analysis
 * Definition of graph-style program
 *)

open Program

type command = 
  | Assign of var * exp     (*   x := E *)
  | PtrAssign of var * exp  (*  *x := E *)
  | Assume of exp     (* Continue execution if exp is true, stop otherwise *)
  | AssumeNot of exp  (* Continue execution if exp is false, stop otherwise *)
  | Skip              (* No operation *)

let command_to_str = function  
  | Assign (x, e) -> x ^ " := " ^ exp_to_str e
  | PtrAssign (x, e) -> "*" ^  x ^ " := " ^ exp_to_str e
  | Assume e -> "assume (" ^ exp_to_str e ^ ")"
  | AssumeNot e -> "assume !(" ^ exp_to_str e ^ ")"
  | Skip -> "skip"

module Node = 
struct
  type t = int * command (* Pair of (Node ID, command) *)

  let get_id : t -> int = fst
  let get_command : t -> command = snd
  let compare n1 n2 = Pervasives.compare (get_id n1) (get_id n2)
  let equal = (=)
  let hash = Hashtbl.hash
end

type node = Node.t

module G = struct
  include Graph.Persistent.Digraph.ConcreteBidirectional (Node)
  let merge : t -> t -> t = fun g1 g2 ->
    (* add_edge() includes an operation of adding src/dst vertex.
      As long as g1 and g2 don't have any isolated node, add_edge()
      is enough for merging the graph. *)
    fold_edges_e (fun e accum_g -> add_edge_e accum_g e) g2 g1
end

type pgm_graph = G.t * node * node (* (graph, start node, end node) *)

let get_nodeid (n:node) = 
  fst n
let get_command (n:node) = 
  snd n

let get_start_node pgm_g =
  let (g, start_node, end_node) = pgm_g in
  start_node

let get_end_node pgm_g =
  let (g, start_node, end_node) = pgm_g in
  end_node

let next_nodes pgm_g n = 
  let (g, start_node, end_node) = pgm_g in
  G.succ g n 
  
let pred_nodes pgm_g n = 
  let (g, start_node, end_node) = pgm_g in
  G.pred g n 

let all_nodes pgm_g = 
  let (g, start_node, end_node) = pgm_g in
  G.fold_vertex (fun v accum_list -> v :: accum_list) g []

let node_id = ref 0

let gen_id () = (node_id := !node_id + 1; !node_id)

let rec flatten_program : program -> pgm_graph = function
  | ASSIGN (x, e) -> 
    let node = (gen_id(), Assign (x, e)) in
    (G.add_vertex G.empty node, node, node)
  | PTRASSIGN (x, e) ->
    let node = (gen_id(), PtrAssign (x, e)) in
    (G.add_vertex G.empty node, node, node)
  | SEQ (c1, c2) -> 
    let (graph1, start1, end1) = flatten_program c1 in
    let (graph2, start2, end2) = flatten_program c2 in
    let graph = G.merge graph1 graph2 in
    let graph' = G.add_edge graph end1 start2 in
    (graph', start1, end2)
  | IF (e, c1, c2) ->
    let branch_node = (gen_id(), Skip) in
    let assume_node = (gen_id(), Assume e) in
    let assume_not_node = (gen_id(), AssumeNot e) in
    let (graph1, start1, end1) = flatten_program c1 in
    let (graph2, start2, end2) = flatten_program c2 in
    let join_node = (gen_id(), Skip) in
    let graph = G.merge graph1 graph2 in
    let graph = G.add_edge graph branch_node assume_node in
    let graph = G.add_edge graph branch_node assume_not_node in
    let graph = G.add_edge graph assume_node start1 in
    let graph = G.add_edge graph assume_not_node start2 in
    let graph = G.add_edge graph end1 join_node in
    let graph = G.add_edge graph end2 join_node in
    (graph, branch_node, join_node)
  | REPEAT (c, e) ->
    let (graph, c_start, c_end) = flatten_program c in
    let goback_node = (gen_id(), Assume e) in
    let exit_node = (gen_id(), AssumeNot e) in
    let graph = G.add_edge graph c_end goback_node in
    let graph = G.add_edge graph goback_node c_start in
    let graph = G.add_edge graph c_end exit_node in
    (graph, c_start, exit_node)

let graph_to_dot : pgm_graph -> string = fun (g, src, dst) ->

  let node_to_dot : G.V.t -> string = fun n ->
    let color_str = 
      if G.V.compare src n = 0 then
        "style=filled color=tomato" 
      else if G.V.compare dst n = 0 then
        "style=filled color=royalblue" 
      else ""
    in
    let cmd_str = command_to_str (Node.get_command n) in
    let id_str = string_of_int (Node.get_id n) in
    Printf.sprintf "%s [label=\"%s : %s\" %s];\n" id_str id_str cmd_str color_str
  in

  let edge_to_dot : G.E.t -> string = fun e ->
    let (src_n, dst_n) = (G.E.src e, G.E.dst e) in
    let src_id_str = string_of_int (Node.get_id src_n) in
    let dst_id_str = string_of_int (Node.get_id dst_n) in
    Printf.sprintf "%s -> %s;\n" src_id_str dst_id_str
  in

  let node_str =
    G.fold_vertex (fun n accum_str -> accum_str ^ node_to_dot n) g "" 
  in
  let edge_str = 
    G.fold_edges_e (fun e accum_str -> accum_str ^ edge_to_dot e) g ""
  in
  Printf.sprintf "digraph G {\nnode [shape=box];\n%s%s}" node_str edge_str
