module StorageToMemory

open Memory
open Storage

let rec copyStAux #v #i #a #c (mem : memoryI a v i c)
  (id : idI a v i) (st : structB c v i) : Tot (memoryI a v i c) (decreases %[st; id])
  = match st, id with
  | Mtst, _ -> mem
  | Store st' (Inl pf) (Var v), _ -> Write mem id (Inl pf) v
  | Store st' (Inr x) v, (idd, xs) ->
  let copyInt = copyStAux mem id st' in
  copyStAux copyInt (idd, (Inr x) :: xs) v
