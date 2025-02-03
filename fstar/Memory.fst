module Memory

type memory a b c =
  | MtMem : memory a b c
  | Write : mem : memory a b c -> id:a -> f:b -> v:c -> memory a b c

let rec read (#a : eqtype) (#b : eqtype) (mem : memory a b nat) (idr : a) (fr : b)
  : nat
  = match mem with
    | MtMem -> 0
    | Write m idw fw v -> if idw = idr && fw = fr
      then v
      else read m idr fr

type memoryI a v i c = memory (a & list (either v i)) (either v i) c

type idI a v i = a & list (either v i)
