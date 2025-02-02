module Storage

type value a =
  | Mtst : value a
  | Var : (v : a) -> value a
  | Store : (st : value a) -> (k : nat) -> (v : value a) -> value a

let rec save #a (st : value a) (flds : list nat)  (v : value a)
  : Tot (value a) (decreases %[flds;st])
  = match st, flds with
    | Mtst, [] -> v
    | Mtst, k :: xs -> Store Mtst k (save Mtst xs v)
    | Var _, _ -> v
    | Store st x _, [] -> Store st x v
    | Store st k v', k' :: ys -> if k = k' then Store st k (save v' ys v) else Store (save st (k' :: ys) v) k v'

let rec select #a (st : value a) (n : nat) : value a
  = match st with
  | Mtst -> Mtst
  | Var st -> Mtst
  | Store st k v -> if k = n then v else select st n

let rec isStruct #a (st : value a) : bool
  = match st with
  | Mtst -> true
  | Var _ -> false
  | Store st _ Mtst -> isStruct st
  | Store st _ (Var _) -> isStruct st
  | Store st _ (Store v x v2) -> isStruct st && isStruct (Store v x v2)

let rec select_save #a (st : value a) (k : nat) (path : list nat) (v : value a) (k' : nat)
  : Lemma (requires isStruct st)
    (ensures select (save st (k :: path) v) k' == (if k = k' then save (select st k') path v else select st k'))
  = match st with
    | Mtst -> _
    | Var _ -> _
    | Store st' k''' v' -> select_save st' k path v k'
