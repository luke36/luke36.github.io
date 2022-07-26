# 拙劣的模仿

```ocaml
type o = OT
type 'a s = ST

type (_, _, _) plus =
  | O_N_N : (o, 'a, 'a) plus
  | S_O_S : ('a, 'b, 'c) plus -> ('a s, 'b, 'c s) plus

type _ vect = Nil : o vect | Cons : int * 'a vect -> 'a s vect

let hd : type a. a s vect -> int = fun v -> match v with Cons (n, _) -> n

let rec app : type a b c. (a, b, c) plus -> a vect -> b vect -> c vect =
 fun prf u v ->
  match prf with
  | O_N_N -> v
  | S_O_S prf' -> ( match u with Cons (n, u') -> Cons (n, app prf' u' v))
```

下次试试写证明？
