module Bug5

type form =
| FForall : (heap -> Tot form) -> form

type deduce : form -> Type =
  | DForallElim :
             f:(heap->Tot form) ->
             deduce (FForall f) ->
             x:heap ->
             deduce (f x)

type pred = heap -> Tot form

val hoist : pred -> heap -> Tot form
let hoist p = fun h -> p h

val hoare_consequence : p:pred -> deduce (FForall (hoist p)) -> h:heap -> Tot unit
let hoare_consequence p vpp' h0 = 
  ignore(DForallElim (hoist p) vpp' h0)
