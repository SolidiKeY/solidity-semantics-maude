module Storage

type value a b c =
  | Mtst : value a b c
  | Var : (v : a) -> value a b c
  | Store : (st : value a b c) -> (k : either b c) -> (v : value a b c) -> value a b c

let rec save #a (#b : eqtype) (#c : eqtype)  (st : value a b c) (flds : list (either b c))  (v : value a b c)
  : Tot (value a b c) (decreases st)
  = match st, flds with
    | Mtst, [] -> v
    | Mtst, k :: xs -> Store Mtst k (save Mtst xs v)
    | Var _, _ -> v
    | Store st x v', [] -> Store st x v'
    | Store st k v', k' :: ys -> if k = k' then Store st k (save v ys v') else Store (save st (k' :: ys) v') k v
