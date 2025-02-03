module StorageToMemory

open Memory
open Storage

let rec copyStAux #v #i #a #c (mem : memory a (either v i) c) (id : a)
  (st : structB c v i) : memory a (either v i) c
  = match st with
  | Mtst -> mem
  | Store st (Inl pf) v -> Write mem id (Inl pf) v
  | Store st (Inr _) v -> admit()
