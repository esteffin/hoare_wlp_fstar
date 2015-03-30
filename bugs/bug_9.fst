module WeakestPrecondition

type heap = nat -> Tot int

assume type form

assume type deduce : form -> Type

type pred = heap -> Tot form

type com =
| Assign : var:nat -> term:int -> com

val update : heap -> nat -> int -> Tot heap
let update h x v = fun y -> if y = x then v else h y

assume type reval : com -> heap -> heap -> Type

type hoare (p:pred) (c:com) (q:pred) : Type =
  (#h:heap -> #h':heap -> reval c h h' -> deduce (p h) -> Tot (deduce (q h')))

val pred_sub : nat -> int -> pred -> Tot pred
let pred_sub x e p = fun h -> p (update h x e)

(* Error changes if I remove this *)
opaque val hoare_assign : q:pred -> x:nat -> e:int ->
                          Tot (hoare (pred_sub x e q) (Assign x e) q)
let hoare_assign q x e = fun h h' pr vh -> vh
