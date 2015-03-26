module Deduce2

(* Formulas *)
type form =
| FFalse  : form
| FImpl   : form -> form -> form
| FAnd    : form -> form -> form
| FForall : #a:Type -> (a -> form) -> form
| FEq     : #a:Type -> a -> a -> form

val fnot : form -> Tot form
let fnot f = FImpl f FFalse

val ftrue : form
let ftrue = FEq () ()

(* Why not do the forall trick from deduce1 also for implication? ...
   get rid of the context! *)
type deduce : form -> Type =
  | DFalseElim :
             f:form ->
             deduce FFalse ->
             deduce f
  | DImplIntro :
             f1:form ->
             f2:form ->
             (deduce f1 -> deduce f2) -> (* <-- meta level implication *)
             deduce (FImpl f1 f2)
  | DImplElim :
             f1:form ->
             f2:form ->
             (deduce (FImpl f1 f2)) ->
             deduce f1 ->
             deduce f2
  | DAndIntro :
             f1:form ->
             f2:form ->
             deduce f1 ->
             deduce f2 ->
             deduce (FAnd f1 f2)
  | DAndElim1 :
             f1:form ->
             f2:form ->
             deduce (FAnd f1 f2) ->
             deduce f1
  | DAndElim2 :
             f1:form ->
             f2:form ->
             deduce (FAnd f1 f2) ->
             deduce f2
  | DForallIntro : 
             #a:Type ->
             #f:(a->Tot form) ->
             (x:a -> deduce (f x)) -> (* <-- meta level quantification *)
             deduce (FForall f)
  | DForallElim :
             #a:Type ->
             #f:(a->Tot form) ->
             deduce (FForall f) ->
             x:a ->
             deduce (f x)
  | DEqRefl : #a:Type ->
              e:a ->
              deduce (FEq e e)
  | DEqSymm : #a:Type ->
              e1:a ->
              e2:a ->
              deduce (FEq e1 e2) ->
              deduce (FEq e2 e1)
  | DEqTran : #a:Type ->
              e1:a ->
              e2:a ->
              e3:a ->
              deduce (FEq e1 e2) ->
              deduce (FEq e2 e3) ->
              deduce (FEq e1 e3)
  | DEqSubst :
              #a:Type ->
              e1:a ->
              e2:a ->
              f:(a -> Tot form) ->
              deduce (FEq e1 e2) ->
              deduce (f e1) ->
              deduce (f e2)
