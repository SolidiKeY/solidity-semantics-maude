module Memory


type idI a b = a & list b
type idIB a v i = idI a (either v i)

type memory (a : Type) (b : Type) (c : Type) : Type =
  | MtMem : memory a b c
  | Write : mem : memory a b c -> id:idI a b -> f:b -> vall:c -> memory a b c
  | Add   : mem : memory a b c -> id:a -> memory a b c

let rec read (#a : eqtype) (#b : eqtype)  (mem : memory a b nat) (idr : idI a b) (fr : b)
  : nat
  = match mem, idr with
    | MtMem, _ -> 0
    | Write m idw fw v, _ -> if idw = idr && fw = fr
      then v
      else read m idr fr
    | Add m ida, (id, _) -> if ida = ida then 0 else read m idr fr

type memoryI a v i c = memory a (either v i) c
