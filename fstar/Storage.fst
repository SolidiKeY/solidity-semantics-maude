module Storage

type value a b =
  | Mtst : value a b
  | Var : (v : a) -> value a b
  | Store : (st : value a b) -> (k : b) -> (v : value a b) -> value a b

let rec save #a (#b : eqtype) (st : value a b) (flds : list b)  (v : value a b)
  : Tot (value a b) (decreases %[flds;st])
  = match st, flds with
    | Mtst, [] -> v
    | Mtst, k :: xs -> Store Mtst k (save Mtst xs v)
    | Var _, _ -> v
    | Store st x v', [] -> Store st x v'
    | Store st k v', k' :: ys -> if k = k' then Store st k (save v ys v') else Store (save st (k' :: ys) v') k v

let rec select #a (#b : eqtype) (st : value a b) (n : b) : value a b
  = match st with
  | Mtst -> Mtst
  | Var st -> Mtst
  | Store st k v -> if k = n then v else select st k

let rec isStruct #a #b (st : value a b) : bool
  = match st with
  | Mtst -> true
  | Var _ -> false
  | Store st _ Mtst -> isStruct st
  | Store st _ (Var _) -> isStruct st
  | Store st _ (Store v x v2) -> isStruct st && isStruct (Store v x v2)

// let rec isStructInside #a #b (st : value a b) (k : b) (v : value a b) :
//   Lemma (requires isStruct (Store st k v))
//     (ensures isStruct st)
//   = match st with
//   | Mtst -> _
//   | Var _ -> _
//   | Store _ _ _ -> _


let rec select_save #a (#b : eqtype) (st : value a b) (k : b) (path : list b) (v : value a b) (k' : b)
  : Lemma (requires isStruct st)
    (ensures select (save st (k :: path) v) k' == (if k = k' then save (select st k') path v else select st k'))
  = match st with
    | Mtst -> _
    | Var _ -> _
    | Store st' k''' v' ->
      // isStructInside st' k''' v';
      select_save st' k path v k;
      select_save st' k path v k';
      assume k''' == k;
      assume k == k';
      assert ((if k = k' then save (select st k') path v else select st k') == save (select st k') path v);
      _
