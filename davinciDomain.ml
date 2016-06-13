open Program
open GraphPgm
open DomFunctor
open AbsDomain

module DavinciAZElem = 
struct
  type t = int
  let compare (n:int) (m:int) = n - m
end

module DavinciAZElemSet = PrimitiveSet(DavinciAZElem)

module DavinciAZ = 
struct
  include PowerSetDomain(DavinciAZElemSet)

  let to_str (az:t) : string =
    if sz az > 100 then
      Printf.sprintf "(Too large to print)"
    else
      fold 
        (fun elem str -> Printf.sprintf "%d %s" elem str)
        az
        ""
  
  let top' : t = 
    make
      (let rec f i = 
        if i < 1867 then i::(f (i + 1)) else []
      in f 0)

  let make (n:int) : t = 
    make [n mod 1867]
end

module DavinciSemantics
=
struct

  type aZ = DavinciAZ.t
  type aLoc = LocDomain.t
  module DavinciValue = Value(DavinciAZ)
  module StoreDomain = StoreDomain(DavinciValue)
  type aValue = DavinciValue.t
  type aStore = StoreDomain.t

  let calc_aplus ((x1, x2):(aValue * aValue)) : aValue = 
    let aZvalue = 
      let (az1, az2) = (DavinciValue.get_az x1, DavinciValue.get_az x2) in
      DavinciAZ.fold
        (fun az1elem az2union ->
          let az2' = DavinciAZ.map (fun az2elem -> (az2elem + az1elem) mod 1867) az2 in
          DavinciAZ.join az2union az2')
        az1
        (DavinciAZ.bot)
    in (aZvalue, LocDomain.bot)

  let calc_aminus (x:aValue) : aValue = 
    let (aZval, aLocval) = x 
    in 
    (DavinciAZ.map (fun azelem -> (0 - azelem + 1867) mod 1867) aZval, 
      LocDomain.bot)

  let calc_aderef (x:var) (aM:aStore) : aValue = 
    let (aZval, aLocval) = StoreDomain.image aM x in
    LocDomain.fold 
      (fun x' (azacc, alacc) -> 
        let (az, al) = StoreDomain.image aM x' in
        (DavinciAZ.join az azacc, LocDomain.join al alacc)) 
      aLocval (DavinciAZ.bot, LocDomain.bot)

  let calc_areadint = (DavinciAZ.top', LocDomain.bot)

  let rec calc_aE (e:exp) (aM:aStore) : aValue = 
    match e with
    | NUM n -> DavinciValue.num n
    | ADD (e1, e2) -> 
      let av1 = calc_aE e1 aM in
      let av2 = calc_aE e2 aM in
      calc_aplus (av1,av2)
    | NEG e -> 
      let av = calc_aE e aM in
      calc_aminus av
    | VAR x -> StoreDomain.image aM x
    | DEREF x -> calc_aderef x aM
    | LOC x -> DavinciValue.loc x
    | READINT -> calc_areadint
    
  let make_m' (node:NodeDomain.t) (m:aStore) : (bool * aStore) = 
    match node with
    | NodeDomain.TOP -> raise (Failure "Cannot be top")
    | NodeDomain.BOT -> raise (Failure "Cannot be bot")
    | NodeDomain.ELT node ->
      let nodecmd = get_command node in
      match nodecmd with
      | Assign (x, e) -> (true, StoreDomain.update m x (calc_aE e m))
      | PtrAssign (x, e) -> 
        (let v' = StoreDomain.image m x in
        let locs = DavinciValue.get_locs v' in
        let ev = calc_aE e m in
        let stores : (aStore option) list = 
            List.map 
              (fun x' -> Some (StoreDomain.update m x' ev)) 
              (LocDomain.to_list locs) in
        let joinedst = List.fold_right 
          (fun st1 st2 -> 
            match (st1, st2) with
            | (None, None) -> None
            | (None, Some st2) -> Some st2
            | (Some st1, None) -> Some st1
            | (Some st1, Some st2) -> Some (StoreDomain.join st1 st2)) stores None
        in 
        match joinedst with
        | None -> raise (Failure "Cannot be none")
        | Some m' -> (true, m'))
      | Assume e -> (true, m)
      | AssumeNot e -> 
        let v' = calc_aE e m in
        let az = DavinciValue.get_az v' in
        let az_list = DavinciAZ.to_list az in
        if List.exists (fun n -> n == 0) az_list then (true, m)
        else (false, m)
      | Skip -> (true, m)
end
