open Program
open GraphPgm
open DomFunctor
open AbsDomain

module EvenOddAZ  = 
struct
  type t = ZERO | EVEN | ODD | BOT | TOP
  let bot = BOT
  let top = TOP
  
  let join (az1:t) (az2:t) : t = 
    match (az1, az2) with
    | (BOT, az2) -> az2
    | (az1, BOT) -> az1
    | (TOP, az2) -> TOP
    | (az1, TOP) -> TOP
    | (ZERO, ZERO) -> ZERO
    | (ZERO, EVEN) -> EVEN
    | (ZERO, ODD) -> TOP
    | (EVEN, ZERO) -> EVEN
    | (EVEN, EVEN) -> EVEN
    | (EVEN, ODD) -> TOP
    | (ODD, ZERO) -> TOP
    | (ODD, ODD) -> ODD
    | (ODD, EVEN) -> TOP

  let leq (az1:t) (az2:t) : bool = 
    match (az1, az2) with
    | (BOT, _) -> true
    | (_, TOP) -> true
    | (TOP, _) -> false
    | (_, BOT) -> false
    | (ZERO, EVEN) -> true
    | (x, y) -> x = y

  let to_str (az:t) : string =
    match az with
    | TOP -> "TOP"
    | BOT -> "BOTTOM"
    | ZERO -> "0"
    | ODD -> "ODD"
    | EVEN -> "EVEN"

  let make (n:int) : t = 
    if n = 0 then ZERO else 
      (if n mod 2 = 0 then EVEN else ODD)
end

module EvenOddSemantics
=
struct

  type aZ = EvenOddAZ.t
  type aLoc = LocDomain.t
  module EvenOddValue = Value(EvenOddAZ)
  module StoreDomain = StoreDomain(EvenOddValue)
  type aValue = EvenOddValue.t
  type aStore = StoreDomain.t

  let calc_aplus ((x1, x2):(aValue * aValue)) : aValue = 
    let aZvalue = match (EvenOddValue.get_az x1, EvenOddValue.get_az x2) with
    | (EvenOddAZ.ZERO, x2) -> x2
    | (x1, EvenOddAZ.ZERO) -> x1
    | (EvenOddAZ.TOP, x2) -> EvenOddAZ.TOP
    | (x1, EvenOddAZ.TOP) -> EvenOddAZ.TOP
    | (EvenOddAZ.BOT, x2) -> EvenOddAZ.BOT
    | (x1, EvenOddAZ.BOT) -> EvenOddAZ.BOT
    | (EvenOddAZ.EVEN, EvenOddAZ.EVEN) -> EvenOddAZ.EVEN
    | (EvenOddAZ.ODD, EvenOddAZ.ODD) -> EvenOddAZ.EVEN
    | (EvenOddAZ.EVEN, EvenOddAZ.ODD) -> EvenOddAZ.ODD
    | (EvenOddAZ.ODD, EvenOddAZ.EVEN) -> EvenOddAZ.ODD
    in (aZvalue, LocDomain.bot)

  let calc_aminus (x:aValue) : aValue = 
    let (aZval, aLocval) = x in (aZval, LocDomain.bot)

  let calc_aderef (x:var) (aM:aStore) : aValue = 
    let (aZval, aLocval) = StoreDomain.image aM x in
    LocDomain.fold 
      (fun x' (azacc, alacc) -> 
        let (az, al) = StoreDomain.image aM x' in
        (EvenOddAZ.join az azacc, LocDomain.join al alacc)) 
      aLocval (EvenOddAZ.bot, LocDomain.bot)

  let calc_areadint = (EvenOddAZ.top, LocDomain.bot)

  let rec calc_aE (e:exp) (aM:aStore) : aValue = 
    match e with
    | NUM n -> EvenOddValue.num n
    | ADD (e1, e2) -> 
      let av1 = calc_aE e1 aM in
      let av2 = calc_aE e2 aM in
      calc_aplus (av1,av2)
    | NEG e -> 
      let av = calc_aE e aM in
      calc_aminus av
    | VAR x -> StoreDomain.image aM x
    | DEREF x -> calc_aderef x aM
    | LOC x -> EvenOddValue.loc x
    | READINT -> calc_areadint

  let calc_aB (e:exp) (m:aStore) : aStore = m
  
  let calc_aNB (e:exp) (m:aStore) : aStore = 
    match e with
    | VAR x -> StoreDomain.update m x (EvenOddValue.num 0)
    | ADD ((VAR x), e') | ADD (e', (VAR x)) -> 
      let v' = calc_aE e' m in
      StoreDomain.update m x v'
    | _ -> m


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
        let locs = EvenOddValue.get_locs v' in
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
      | Assume e -> (true, (calc_aB e m))
      | AssumeNot e -> 
        let v' = calc_aE e m in
        let az = EvenOddValue.get_az v' in
        if az == EvenOddAZ.ZERO || az == EvenOddAZ.EVEN || az == EvenOddAZ.TOP then 
          (true, (calc_aNB e m))
        else (false, m)
      | Skip -> (true, m)

end
