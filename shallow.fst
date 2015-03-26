module ShallowEmbedding
open Expressions

(* Formulas *)
type form =
| FTrue   : form
| FNot    : form -> form
| FImpl   : form -> form -> form
| FAnd    : form -> form -> form
| FForall : #a:Type -> (a -> form) -> form
| FEq     : #a:Type -> a -> a -> form

(* Could also have a variant of this targeting constructive connectives;
   How do we define validity for the constructive things though?
   Using axioms like in Classical? *)
type shallow : form -> Type -> Type =
  | ShTrue : shallow FTrue True
  | ShNot  : #f:form ->
            #t:Type ->
            shallow f t ->
            shallow (FNot f) (~t)
  | ShImpl  : #f1:form ->
             #f2:form ->
             #t1:Type ->
             #t2:Type ->
             shallow f1 t1 ->
             shallow f2 t2 ->
             shallow (FImpl f1 f2) (t1 ==> t2)
  | ShAnd :   #f1:form ->
             #f2:form ->
             #t1:Type ->
             #t2:Type ->
             shallow f1 t1 ->
             shallow f2 t2 ->
             shallow (FAnd f1 f2) (t1 /\ t2)
  | ShForall : #a:Type ->
               #f:(a->Tot form) ->
               #t:(a->Type) ->
               (x:a -> shallow (f x) (t x)) ->
(*               shallow (FForall f) (forall (x:a). t x) -- lots of warnings *)
(*               shallow (FForall f) (x:a -> t x) -- lots of warnings *)
               shallow (FForall f) True
  | ShEq     : #a:Type ->
               x1:a ->
               x2:a ->
               shallow (FEq x1 x2) (x1 = x2)

(* This exists and conjunction(?) could also be constructive *)
type valid_shallow (f:form) = (exists (t:Type). shallow f t /\ t)
(* Using this constructively would imply:
   - producing the witness t
   - applying ShX rules to produce the shallow embedding proof
   - realizing some of the proof of t
     (e.g. using things like forall_intro, exists_elim, etc.)
*)
