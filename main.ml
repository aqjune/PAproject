(*
 * SNU 4541.664A Program Analysis
 * Main program driver
 *)

open Program
open GraphPgm

let src = ref ""
let opt_print = ref false
let opt_eo = ref false
let opt_davinci = ref false

let main () = 
  Arg.parse
    [ ("-print", Arg.Unit (fun _ -> opt_print := true), "print flattend pgm");
      ("-eo", Arg.Unit (fun _ -> opt_eo := true), "even/odd analysis");
      ("-davinci", Arg.Unit (fun _ -> opt_davinci := true), "davinci analysis")]
    (fun x -> src := x)
    ("Usage : " ^ (Filename.basename Sys.argv.(0)) ^ " [-option] [filename] ");
  let lexbuf = Lexing.from_channel (if !src = "" then stdin else open_in !src) in
  let pgm = (Parser.main Lexer.token lexbuf) in
  let pgm_graph = GraphPgm.flatten_program pgm in
  if !opt_print then (
	  print_endline "=== Printing Flattened Graph of Input Program ===";
    let chan = open_out "graph.dot" in
    let dot_content = graph_to_dot pgm_graph in
    output_string chan dot_content;
    let _ = close_out chan in
    let _ = Sys.command "dot ./graph.dot -o ./graph.png -T png" in
	  print_endline "(check graph.png file)"
  )
  else if !opt_eo then (
    let result = EvenOdd.eoAnalyzer pgm_graph in
    print_endline (EvenOdd.result_to_str result)
  )
  else if !opt_davinci then (
    let result = Davinci.daVinciAnalyzer pgm_graph in
    print_endline (Davinci.result_to_str result)
  )
  else
    print_endline "Please provide one of options! (try './main.native --help')"
  

let _ = main ()
