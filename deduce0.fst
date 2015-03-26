module Deduce0
open Expressions

type hval =
  | HvHeap : heap -> hval
  | HvVar  : nat  -> hval

type form =
| FFalse  : form
| FImpl   : form -> form -> form
| FAnd    : form -> form -> form
| FForall : form -> form         (* forall h : heap. form -- deBruijn *)
| FBexp   : bexp -> hval -> form (* boolean expression in heap h, rather weak *)

val fnot : form -> Tot form
let fnot f = FImpl f FFalse

(*
val feq : aexp -> aexp -> hval -> Tot form
let feq a1 a2 hv = FBexp (BEq a1 a2) hv
*)

assume val subst : nat -> heap -> form -> Tot form

assume val shift_up_env : list form -> Tot (list form)

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
  | DFalseElim :
             #fs:list form ->
             f:form ->
             deduce fs FFalse ->
             deduce fs f
  | DAndIntro :
             #fs:list form ->
             f1:form ->
             f2:form ->
             deduce fs f1 ->
             deduce fs f2 ->
             deduce fs (FAnd f1 f2)
  | DAndElim1 :
             #fs:list form ->
             f1:form ->
             f2:form ->
             deduce fs (FAnd f1 f2) ->
             deduce fs f1
  | DAndElim2 :
             #fs:list form ->
             f1:form ->
             f2:form ->
             deduce fs (FAnd f1 f2) ->
             deduce fs f2
  | DForallIntro :
             #fs:list form ->
             #f:form ->
             deduce (shift_up_env fs) f ->
             deduce fs (FForall f)
  | DForallElim :
             #fs:list form ->
             #a:Type ->
             #f:form ->
             deduce fs (FForall f) ->
             h:heap ->
             deduce fs (subst 0 h f)
  | DBexpIntro :
              fs:list form ->
              b:bexp ->
              h:heap{eval_bexp h b = true} ->
              deduce fs (FBexp b (HvHeap h))
(* no elimination for FBexp
  | DBexpElim :
              fs:list form ->
              b:bexp ->
              deduce fs (FBexp b (HvHeap h)) ->
              deduce ???
... in particular no replacing of equals by equals
  | DEqSubst :
              #fs:list form ->
              #a:Type ->
              e1:a ->
              e2:a ->
              f:(a -> Tot form) ->
              deduce fs (feq e1 e2) ->
              deduce fs (f e1) ->
              deduce fs (f e2)
*)
