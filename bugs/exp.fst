module Expressions

type binop =
| Plus
| Minus
| Times

type id = nat

type aexp =
| AInt : int -> aexp
| AVar : id -> aexp 
| AOp  : binop -> aexp -> aexp -> aexp 

type bexp =
| BTrue  : bexp
| BFalse : bexp
| BEq    : aexp -> aexp -> bexp
| BLe    : aexp -> aexp -> bexp
| BNot   : bexp -> bexp
| BAnd   : bexp -> bexp -> bexp

type heap = id -> Tot int

val eval_aexp : heap -> aexp -> Tot int
let rec eval_aexp h e =
  match e with 
  | AInt i -> i
  | AVar x -> h x
  | AOp op op1 op2 ->
     let i1 = eval_aexp h op1 in
     let i2 = eval_aexp h op2 in
     (match op with
      | Plus  -> i1 + i2
      | Minus -> i1 - i2
      | Times -> i1 * i2)

val eval_bexp : heap -> bexp -> Tot bool
let rec eval_bexp h be =
  match be with 
  | BTrue -> true
  | BFalse -> false
  | BEq e1 e2 -> eval_aexp h e1  = eval_aexp h e2
  | BLe e1 e2 -> eval_aexp h e1 <= eval_aexp h e2
  | BNot be' -> not (eval_bexp h be')
  | BAnd be1 be2 -> eval_bexp h be1 && eval_bexp h be2
