module Storage

type value a =
  | Mtst : value a
  | Var : (v : a) -> value a
  | Store : (st : value a) -> (k : nat) -> (v : value a) -> value a

let rec save #a (st : value a) (flds : list nat)  (v : value a) : value a
  = match st, flds with
    | Mtst, [] -> admit()
    | _, _ -> admit()
