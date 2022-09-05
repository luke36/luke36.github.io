---
layout: post
title: "如果有人知道如何避免，请告诉我"
---

```ocaml
type _ op =
  | Add : (int ty_base * int ty_base -> int ty_base) op
  | Sub : (int ty_base * int ty_base -> int ty_base) op
  | Mul : (int ty_base * int ty_base -> int ty_base) op
  | Div : (int ty_base * int ty_base -> int ty_base) op
  | Rem : (int ty_base * int ty_base -> int ty_base) op
  | BitAnd : (int ty_base * int ty_base -> int ty_base) op
  | BitOr : (int ty_base * int ty_base -> int ty_base) op
  | BitXor : (int ty_base * int ty_base -> int ty_base) op
  | Neg : (int ty_base -> int ty_base) op
  | BitNot : (int ty_base -> int ty_base) op
  | Lt : (int ty_base * int ty_base -> bool ty_base) op
  | Le : (int ty_base * int ty_base -> bool ty_base) op
  | Gt : (int ty_base * int ty_base -> bool ty_base) op
  | Ge : (int ty_base * int ty_base -> bool ty_base) op
  | Neq : ('a * 'a -> bool ty_base) op
  | Eq : ('a * 'a -> bool ty_base) op
  | And : (bool ty_base * bool ty_base -> bool ty_base) op
  | Or : (bool ty_base * bool ty_base -> bool ty_base) op
  | Not : (bool ty_base -> bool ty_base) op

and _ expr =
  | Lit : 'a * 'a ty_base ty -> 'a ty_base expr
  | LVal : 'a lval -> 'a expr
  | Bin : 'a expr * ('a * 'b -> 'c) op * 'b expr -> 'c expr
  | Un : ('a -> 'b) op * 'a expr -> 'b expr

let refute (e : ('a * 'b) expr) : 'd =
  match e with
  | LVal lv -> (
      match lv with
      | Var (_, ty) -> .
      | ArrElm (_, TyArr (ty, _), _) -> .
      | _ -> .)
  | _ -> .

let type_of : type a. a expr -> a ty =
 fun e ->
  match e with
  (* omit valid cases *)
  | Un (Not, _) -> TyBool
  | Un (Sub, e) -> refute e
  | Un (Add, e) -> refute e
  | Un (Mul, e) -> refute e
  | Un (Div, e) -> refute e
  (* ... *)
  | Un (Le, e) -> refute e
  | Un (Ge, e) -> refute e
  | Un (Gt, e) -> refute e
  | Un (Eq, e) -> refute e
  | Un (Neq, e) -> refute e (* !!!disaster *)
```

感觉就好比 auto 的层数不够多.
