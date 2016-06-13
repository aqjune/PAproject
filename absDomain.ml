open Program
open GraphPgm
open DomFunctor

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
	
module NodeDomain = 
struct
  include FlatDomain(Node)
  let next_nodes pgm (n:t) : t list =
    match n with
    | BOT -> [BOT]
    | TOP -> [TOP]
    | ELT n -> List.map (fun v -> ELT v) (next_nodes pgm n)
  let compare t1 t2 = 
    match (t1, t2) with
    | BOT, BOT -> 0
    | TOP, TOP -> 0
    | BOT, _ -> -1
    | _, TOP -> 1
    | TOP, _ -> 1
    | _, BOT -> -1
    | (ELT n1), (ELT n2) -> Node.compare n1 n2
  let to_str nd =
    match nd with
    | BOT -> raise (Failure "Cannot be bot")
    | TOP -> raise (Failure "Cannot be top")
    | ELT nd -> 
      let cmd = get_command nd in
      match cmd with
      | Assign (x, e) -> (Printf.sprintf "%s := %s" x (exp_to_str e))
      | PtrAssign (x, e) -> (Printf.sprintf "*%s := %s" x (exp_to_str e))
      | Assume e -> Printf.sprintf "Assume %s" (exp_to_str e)
      | AssumeNot e -> Printf.sprintf "AssumeNot %s" (exp_to_str e)
      | Skip -> "Skip"
end

module Loc = Var
module LocSet = PrimitiveSet(Loc)
module LocDomain = 
struct
  include PowerSetDomain(LocSet)
  let to_str (aloc:t) : string = 
    Printf.sprintf "(%s)"
      (fold (fun l str -> Printf.sprintf "%s,%s" l str) aloc "")
end


module type AZDOMAIN = 
sig
  type t
  val bot : t
  val top : t
  
  val join : t -> t -> t
  val leq : t -> t -> bool

  val to_str : t -> string
  val make : int -> t
end

module type VALUEDOMAIN = 
sig
  include DOMAIN
  type azty
  val num : int -> t
  val loc : var -> t
  val get_az : t -> azty
  val get_locs : t -> LocDomain.t 
  val to_str : t -> string
end

module Value (AZ:AZDOMAIN) = 
struct
  include ProductDomain(AZ)(LocDomain)
  type azty = AZ.t
  
  let num (n:int) : t = 
    make 
      (AZ.make n)
      LocDomain.bot
  let loc (l:var) : t = 
    make 
      AZ.bot
      (LocDomain.make [l])

  let get_az (av:t) : AZ.t = 
    l av
  let get_locs (av:t) : LocDomain.t = 
    r av
  
  let to_str (av:t) : string =
	  let (az, aloc) = av in
	  Printf.sprintf "<%s,%s>" (AZ.to_str az) (LocDomain.to_str aloc)
end

module type STOREDOMAIN = 
sig
  include DOMAIN
  type keyt
  type valuet
  val image : t -> keyt -> valuet
  val fold : (keyt -> valuet -> 'a -> 'a) -> t -> 'a -> 'a
  val to_str : t -> string
  val to_list : t -> (keyt * valuet) list
end

module StoreDomain (Value:VALUEDOMAIN) = 
struct
  include FunDomain(Loc)(Value)
  type keyt = Loc.t
  type valuet = Value.t
  let to_str (ast:t) : string =
    let astlist = to_list ast in
    List.fold_right
      (fun (key,aval) str -> Printf.sprintf "%s = %s\n%s" key (Value.to_str aval) str)
      astlist
      ""
end

