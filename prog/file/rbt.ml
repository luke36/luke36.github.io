type tree =
  | R of tree * int * int * tree
  | B of tree * int * int * tree
  | BB of tree * int * int * tree
  | LL
  | L

let empty = L

let size t =
  match t with
  | L -> 0
  | LL -> 0
  | R (_, _, n, _)
  | B (_, _, n, _)
  | BB (_, _, n, _) -> n

let sized t =
  match t with
  | L -> L
  | LL -> LL
  | R (l, v, _, r) ->
     R (l, v, size l + size r + 1, r)
  | B (l, v, _, r) ->
     B (l, v, size l + size r + 1, r)
  | BB (l, v, _, r) ->
     BB (l, v, size l + size r + 1, r)

let blacken t =
  match t with
  | R (l, v, n, r)
  | B (l, v, n, r)
  | BB (l, v, n, r) ->
     B (l, v, n, r)
  | _ -> assert false

let balance t =
  match t with
  | B (R (R (a, x, n, b), y, _, c), z, p, d) ->
     R (B (a, x, n, b), y, p, B (c, z, p - n - 1, d))
  | B (R (a, x, _, R (b, y, _, c)), z, p, d) ->
     R (sized @@ B (a, x, -1, b), y, p, sized @@ B (c, z, -1, d))
  | B (a, x, n, R (R (b, y, _, c), z, _, d)) ->
     R (sized @@ B (a, x, -1, b), y, n, sized @@ B (c, z, -1, d))
  | B (a, x, n, R (b, y, _, R (c, z, p, d))) ->
     R (B (a, x, n - p - 1, b), y, n, B (c, z, p , d))
  | BB (R (a, x, _, R (b, y, _, c)), z, p, d) ->
     B (sized @@ B (a, x, -1, b), y, p, sized @@ B (c, z, -1, d))
  | BB (a, x, n, R (R (b, y, _, c), z, _, d)) ->
     B (sized @@ B (a, x, -1, b), y, n, sized @@ B (c, z, -1, d))
  | t -> t

let add v t =
  let rec ins t =
    match t with
    | L -> R (L, v, 1, L)
    | R (l, v', n, r) ->
       if (v <= v') then
         balance @@ R (ins l, v', n + 1, r)
       else
         balance @@ R (l, v', n + 1, ins r)
    | B (l, v', n, r) ->
       if (v <= v') then
         balance @@ B (ins l, v', n + 1, r)
       else
         balance @@ B (l, v', n + 1, ins r)
    | _ -> assert false
  in
  (blacken (ins t))

let isBB t =
  match t with
  | BB _
  | LL -> true
  | _ -> false

let whiten t =
  match t with
  | BB (l, x, n, r) -> B (l, x, n, r)
  | LL -> L
  | t -> t

let rotate t =
  match t with
  | R (axnb, y, m, B (c, z, _, d)) when isBB axnb ->
     balance @@ B (sized @@ R (whiten axnb, y, -1, c), z, m, d)
  | R (B (a, x, _, b), y, m, czpd) when isBB czpd ->
     balance @@ B (a, x, m, sized @@ R (b, y, -1, whiten czpd))
  | B (axnb, y, m, B (c, z, _, d)) when isBB axnb ->
     balance @@ BB (sized @@ R (whiten axnb, y, -1, c), z, m, d)
  | B (B (a, x, _, b), y, m, czpd) when isBB czpd ->
     balance @@ BB (a, x, m, sized @@ R (b, y, -1, whiten czpd))
  | B (awnb, x, m, R (B (c, y, _, d), z, _, e)) when isBB awnb ->
     B (balance @@ sized @@ B (sized @@ R (whiten awnb, x, -1, c), y, -1, d), z, m, e)
  | B (R (a, w, _, B (b, x, _, c)), y, p, dzqe) when isBB dzqe ->
     B (a, w, p, balance @@ sized @@ B (b, x, -1, sized @@ R(c, y, -1, whiten dzqe)))
  | t -> t

let rec remove_min t =
  match t with
  | R (L, x, _, L) -> (x, L)
  | B (L, x, _, L) -> (x, LL)
  | B (L, x, _, R (a, y, n, b)) -> (x, B (a, y, n, b))
  | R (a, x, n, b) ->
     let (v, a') = remove_min a in
     (v, rotate @@ R (a', x, n - 1, b))
  | B (a, x, n, b) ->
     let (v, a') = remove_min a in
     (v, rotate @@ B (a', x, n - 1, b))
  | _ -> assert false

and del v t =
  match t with
  | L -> L
  | R (L, v', _, L) when v = v' -> L
  | B (R (a, x, n, b), v', _, L) when v = v' -> B (a, x, n, b)
  | B (L, v', _, L) when v = v' -> LL
  | R (a, x, n, b) ->
     if v < x then
       rotate @@ sized @@ R (del v a, x, -1, b)
     else if v > x then
       rotate @@ sized @@ R (a, x, -1, del v b)
     else
       let (v', b') = remove_min b in
       rotate @@ R (a, v', n - 1, b')
  | B (a, x, n, b) ->
     if v < x then
       rotate @@ sized @@ B (del v a, x, -1, b)
     else if v > x then
       rotate @@ sized @@ B (a, x, -1, del v b)
     else
       let (v', b') = remove_min b in
       rotate @@ B (a, v', n - 1, b')
  | _ -> assert false

let remove v t = whiten @@ del v t

let rec min t =
  match t with
  | R (L, x, _, _)
  | B (L, x, _, _) ->
     x
  | R (a, _, _, _)
  | B (a, _, _, _) ->
     min a
  | _ -> assert false

let rec max t =
  match t with
  | R (_, x, _, L)
  | B (_, x, _, L) ->
     x
  | R (_, _, _, b)
  | B (_, _, _, b) ->
     max b
  | _ -> assert false

let rec succ v t =
  match t with
  | L -> None
  | R (a, x, _, b)
  | B (a, x, _, b) -> begin
      if v = x then
        match b with
        | L -> None
        | b -> Some (min b)
      else if v > x then
        succ v b
      else
        match succ v a with
        | None -> Some x
        | Some suc -> Some suc
    end
  | _ -> assert false

let rec pred v t =
  match t with
  | L -> None
  | R (a, x, _, b)
  | B (a, x, _, b) -> begin
      if v = x then
        match a with
        | L -> None
        | a -> Some (max a)
      else if v < x then
        pred v a
      else
        match pred v b with
        | None -> Some x
        | Some prd -> Some prd
    end
  | _ -> assert false

let rec nlt v t =
  match t with
  | L -> 0
  | R (a, x, _, b)
  | B (a, x, _, b) ->
     if x >= v then
       nlt v a
     else
       1 + size a + nlt v b
  | _ -> assert false

let rec ngt v t =
  match t with
  | L -> 0
  | R (a, x, _, b)
  | B (a, x, _, b) ->
     if x <= v then
       ngt v b
     else
       1 + size b + ngt v a
  | _ -> assert false

let nbetween a b t =
  size t - nlt a t - ngt b t

let member v t =
  let rec mem t =
    match t with
    | L -> false
    | R (a, x, _, b)
    | B (a, x, _, b) ->
       if v = x then true
       else if v < x then mem a
       else mem b
    | _ -> assert false
  in mem t

(***** Hyper *****)

let ndata = 5000000
let max_int = Int.max_int
let max_nbase = 25
let heavy_nbase = 1

(*****************)

module DBase = struct
  type t = tree

  let bases = Array.make max_nbase empty

  let sp = ref 1

  let last = ref (-1)
  let lasti = ref (-1)

  let init () =
    sp := 1;
    for i = 0 to max_nbase - 1 do
      bases.(i) <- empty
    done;
    last := -1

  let add i x =
    if not (member x bases.(i)) then begin
        bases.(i) <- add x bases.(i);
        last := x;
        lasti := i
      end

  let remove i x =
    bases.(i) <- remove x bases.(i);
    if i = !lasti && x = !last then
        last := -1

  let fork i =
    bases.(!sp) <- bases.(i);
    sp := !sp + 1

  let query i x =
    let mem = member x bases.(i) in
    if mem then begin
        lasti := i;
        last := x
    end;
    mem

  let range i low high =
    nbetween low high bases.(i)

  let pred () =
    if !last = (-1) then
      -1
    else
      let r = pred !last bases.(!lasti) in
      let r = match r with None -> -1 | Some x -> x in
      last := r;
      r

  let succ () =
    if !last = -1 then
      -1
    else
      let r = succ !last bases.(!lasti) in
      let r = match r with None -> -1 | Some x -> x in
      last := r;
      r
end

type operation =
  | Ins of int * int
  | Del of int * int
  | Fork of int
  | Ask of int * int
  | Ran of int * int * int
  | Pred
  | Succ

let rec trav t =
  match t with
  | R (a, _, _, b) | B (a, _, _, b) -> trav a; trav b
  | _ -> ()

let doop op =
  let open DBase in
  match op with
  | Ins (i, x) -> add i x
  | Del (i, x) -> remove i x
  | Fork i -> fork i
  | Ask (i, x) -> ignore @@ query i x
  | Ran (i, a, b) -> for _ = a to b do ignore @@ range i a b done
  | Pred -> ignore @@ pred ()
  | Succ -> ignore @@ succ ()

let dotest f g =
  let rec checksz t =
    match t with
    | L -> ()
    | R (a, _, n, b)
    | B (a, _, n, b) ->
       checksz a;
       checksz b;
       if n <> size a + size b + 1 then
         failwith "wrong tree"
    | _ -> assert false
  in
  let rec checkbi t =
    match t with
    | L -> ()
    | R (a, v, _, b)
    | B (a, v, _, b) ->
       checkbi a;
       checkbi b;
       if a != L && max a >= v || b != L && min b <= v then
         failwith "wrong tree"
    | _ -> assert false
  in
  let open DBase in
  checksz DBase.bases.(0);
  checkbi DBase.bases.(0);
  Scanf.bscanf f "%d" (fun o ->
  match o with
  | 0 -> Scanf.bscanf f " %d %d\n" (fun i a -> add i a)
  | 1 -> Scanf.bscanf f " %d %d\n" (fun i a -> remove i a)
  | 2 -> Scanf.bscanf f " %d\n" (fun i -> fork i)
  | 3 -> Scanf.bscanf f " %d %d\n" (fun i a -> Printf.fprintf g "%b\n" (query i a))
  | 4 -> Scanf.bscanf f " %d %d %d\n" (fun i a b -> Printf.fprintf g "%d\n" (range i a b))
  | 5 -> Scanf.bscanf f "\n" Printf.fprintf g "%d\n" (pred ())
  | 6 -> Scanf.bscanf f "\n" Printf.fprintf g "%d\n" (succ ())
  | _ -> assert false)

let serialize f op =
  let write x =
    for i = 8 - 1 downto 0 do
      Printf.fprintf f "%c" @@ char_of_int @@ 0b11111111 land (x asr (i * 8))
    done
  in
  match op with
  | Ins (i, x) ->
     Printf.fprintf f "%c" @@ char_of_int @@ 0b000 + i lsl 3;
     write x
  | Del (i, x) ->
     Printf.fprintf f "%c" @@ char_of_int @@ 0b001 + i lsl 3;
     write x
  | Ask (i, x) ->
     Printf.fprintf f "%c" @@ char_of_int @@ 0b010 + i lsl 3;
     write x
  | Fork i ->
     Printf.fprintf f "%c" @@ char_of_int @@ 0b011 + i lsl 3
  | Ran (i, a, b) ->
     Printf.fprintf f "%c" @@ char_of_int @@ 0b100 + i lsl 3;
     write a;
     write b
  | Pred ->
     Printf.fprintf f "%c" @@ char_of_int @@ 0b101
  | Succ ->
     Printf.fprintf f "%c" @@ char_of_int @@ 0b110

let answer f op =
  let open DBase in
  let write x =
    for i = 8 - 1 downto 0 do
      Printf.fprintf f "%c" @@ char_of_int @@ 0b11111111 land (x asr (i * 8))
    done
  in
  match op with
  | Ins (i, x) -> add i x
  | Del (i, x) -> remove i x
  | Fork i -> fork i
  | Ask (i, x) -> write @@ if query i x then 1 else 0
  | Ran (i, a, b) -> write @@ range i a b
  | Pred -> write @@ pred ()
  | Succ -> write @@ succ ()

let gentest ques ans op =
  let open DBase in
  match op with
  | Ins (i, x) ->
     Printf.fprintf ques "0 %d %d\n" i x;
     add i x
  | Del (i, x) ->
     Printf.fprintf ques "1 %d %d\n" i x;
     remove i x
  | Fork i ->
     Printf.fprintf ques "2 %d\n" i;
     fork i
  | Ask (i, x) ->
     Printf.fprintf ques "3 %d %d\n" i x;
     Printf.fprintf ans "%b\n" @@ query i x
  | Ran (i, a, b) ->
     Printf.fprintf ques "4 %d %d %d\n" i a b;
     Printf.fprintf ans "%d\n" @@ range i a b
  | Pred ->
     Printf.fprintf ques "5\n";
     Printf.fprintf ans "%d\n" @@ pred ()
  | Succ ->
     Printf.fprintf ques "6\n";
     Printf.fprintf ans "%d\n" @@ succ ()


let _ = Random.self_init ()

let pick_random _ = Random.full_int max_int

let pick_up round =
  round * (max_int / ndata)

let pick_down round =
  (ndata - round) * (max_int / ndata)

let rec which x arr sum i =
  let sum' = sum + arr.(i) in
  if sum' > x then i
  else which x arr sum' (i + 1)

let random_op rem =
  let sum = Array.fold_left (+) 0 rem in
  let ch = which (Random.int sum) rem 0 0 in
  ch

let order = [0; 2; 4; 5; 6; 3; 1]
let heavy_load rem =
  let rec f l =
    match l with
    | [] -> assert false
    | a :: d -> if rem.(a) > 0 then a else f d
  in
  f order

let rec gen1 used nused round rem nmap f op ch =
  if round > 0 then
    let c = ch rem in
    rem.(c) <- rem.(c) - 1;
    match c with
    | 0 -> let i = Random.int (Int.min nmap heavy_nbase) in
      let x = f round in
      op @@ Ins (i, x);
      used.(i).(nused.(i)) <- x;
      nused.(i) <- nused.(i) + 1;
      gen1 used nused (round - 1) rem nmap f op ch
    | 1 -> let i = Random.int (Int.min nmap heavy_nbase) in
      let x = used.(i).(Random.int nused.(i)) in
      op @@ Del (i, x);
      gen1 used nused (round - 1) rem nmap f op ch
    | 2 -> let i = Random.int (Int.min nmap heavy_nbase) in
      let x = used.(i).(Random.int nused.(i)) in
      op @@ Ask (i, x);
      gen1 used nused (round - 1) rem nmap f op ch
    | 3 -> let i = Random.int (Int.min nmap heavy_nbase) in
      used.(nmap) <- Array.copy used.(i);
      nused.(nmap) <- nused.(i);
      op @@ Fork i;
      gen1 used nused (round - 1) rem (nmap + 1) f op ch
    | 4 -> let i = Random.int (Int.min nmap heavy_nbase) in
      let x = used.(i).(Random.int nused.(i))  in
      op @@ Ran (i, x, Int.min Int.max_int (x + Random.int 1000));
      gen1 used nused (round - 1) rem nmap f op ch
    | 5 -> op Pred;
      gen1 used nused (round - 1) rem nmap f op ch
    | 6 -> op Succ;
      gen1 used nused (round - 1) rem nmap f op ch
    | _ -> assert false

let gen f op ch =
  let used = Array.make max_nbase [||] in
  let nused = Array.make max_nbase 0 in
  used.(0) <- Array.make ndata 0;
  gen1 used nused ndata
    [| ndata/2 + (ndata-ndata/2-ndata/6-ndata/9-max_nbase+1-ndata/18-ndata/12-ndata/12);
       ndata/6;
       ndata/9;
       max_nbase-1;
       ndata/18;
       ndata/12;
       ndata/12|]
    1 f op ch

