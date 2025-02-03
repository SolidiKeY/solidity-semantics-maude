module StorageToMemory

open FStar.List
open Memory
open Storage

let rec copyStAux #v #i #a #c (mem : memoryI a v i c)
  (id : idIB a v i) (st : structB c v i) : Tot (memoryI a v i c) (decreases %[st; id])
  = match st, id with
  | Mtst, _ -> mem
  | Store st' (Inl pf) (Var v), _ -> Write mem id (Inl pf) v
  | Store st' (Inr x) v, (idd, xs) ->
  let copyInt = copyStAux mem id st' in
  copyStAux copyInt (idd, (Inr x) :: xs) v

let copySt #v #i #a #c (mem : memoryI a v i c) (id : a) (st : structB c v i) : memoryI a v i c =
    copyStAux (Add mem id) (id, []) st

let rec is_same (#a : eqtype) (l1 l2 : list a) : bool
  = match l1, l2 with
  | [], [] -> true
  | x :: xs, y :: ys -> x = y && xs `is_same` ys
  | _ -> false

let rec is_same_same (#a : eqtype) (l1 l2 : list a) :
  Lemma (requires is_same l1 l2) (ensures l1 == l2)
  = match l1, l2 with
  | [], [] -> _
  | x :: xs, y :: ys -> is_same_same xs ys

let rec is_same_rev (#a : eqtype) (l : list a) :
  Lemma (is_same l l)
  = match l with
  | [] -> _
  | _ :: xs -> is_same_rev xs

let rec is_suffix_of (#a : eqtype) (l1 l2 : list a) : bool
  = l1 `is_same` l2 || (match l2 with
    | []  -> false
    | _ :: q -> l1 `is_suffix_of` q
    )

let suffix_equal (#a : eqtype) (x : a) (l : list a) :
  Lemma (ensures l `is_suffix_of` (x :: l))
  = match l with
  | [] -> _
  | _ :: xs -> is_same_rev xs

let rec readSkip (#v : eqtype) (#i :eqtype) (#a : eqtype) (mem : memoryI a v i nat) (pId : a)
  (pIdR : a) (st : structB nat v i) (fxsL : list (either v i)) (fxsR : list (either v i)) (fld : either v i) :
  Lemma (requires pId <> pIdR || pId = pIdR && not (fxsL `is_suffix_of` (fld :: fxsR)))
    (ensures read (copyStAux mem (pId, fxsL) st) (pIdR , fxsR) fld == read mem (pIdR , fxsR) fld) =
    match st with
    | Mtst -> _
    | Store st' (Inl f) (Var _) ->
      readSkip mem pId pIdR st' fxsL fxsR fld;
      suffix_equal fld fxsL
    | Store _ (Inr _) _ -> admit()
