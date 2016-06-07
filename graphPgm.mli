open Program

type command = 
  | Assign of var * exp     (*   x := E *)
  | PtrAssign of var * exp  (*  *x := E *)
  | Assume of exp     (* Continue execution if exp is true, stop otherwise *)
  | AssumeNot of exp  (* Continue execution if exp is false, stop otherwise *)
  | Skip              (* No operation *)

type node

type pgm_graph

val get_start_node : pgm_graph -> node
val get_end_node : pgm_graph -> node
val next_nodes : pgm_graph -> node -> node list
val pred_nodes : pgm_graph -> node -> node list
val all_nodes : pgm_graph -> node list

(* From here, you don't have to care *)
val graph_to_dot : pgm_graph -> string
val flatten_program : program -> pgm_graph
