module Deduce1

(* Formulas *)
type form =
| FTrue   : form
| FNot    : form -> form
| FImpl   : form -> form -> form
| FAnd    : form -> form -> form
| FForall : #a:Type -> (a -> form) -> form
| FEq     : #a:Type -> a -> a -> form

(* Natural deduction *)
(* Lists for environments? Why not sets? *)
(* Cheating a quite a bit with the forall? *)
type deduce : list form -> form -> Type =
  | DAxiom : #fs : list form ->
             f : form{List.mem f fs} ->
             deduce fs f
  | DImplIntro :
             #fs:list form ->
             f1:form ->
             f2:form ->
             deduce (f1::fs) f2 ->
             deduce fs (FImpl f1 f2)
  | DImplElim :
             #fs:list form ->
             f1:form ->
             f2:form ->
             deduce fs (FImpl f1 f2) ->
             deduce fs f1 ->
             deduce fs f2
  | DForallIntro : 
             #fs : list form ->
             #a:Type ->
             #f:(a->Tot form) ->
             (x:a -> Tot (deduce fs (f x))) -> (* <-- meta level quantification *)
             deduce fs (FForall f)
  | DForallElim :
             #fs : list form ->
             #a:Type ->
             #f:(a->Tot form) ->
             deduce fs (FForall f) ->
             x:a ->
             deduce fs (f x)
