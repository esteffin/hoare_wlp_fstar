module Deduce0
open Expressions

type hval =
  | HvHeap : heap -> hval
  | HvVar  : nat  -> hval

type form =
| FImpl   : form -> form -> form
| FAnd    : form -> form -> form
| FForall : form -> form    (* forall h : heap. form -- deBruijn *)
| FBexp   : bexp -> hval -> form (* boolean expression in heap h, rather weak *)

val ftrue : form
let ftrue = FBexp BTrue (HvVar 0)

val ffalse : form
let ffalse = FBexp BFalse (HvVar 0)

val fnot : form -> Tot form
let fnot f = FImpl f ffalse

(*
val feq : aexp -> aexp -> hval -> Tot form
let feq a1 a2 hv = FBexp (BEq a1 a2) hv
*)

assume val subst : nat -> heap -> form -> Tot form

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
             deduce fs ffalse ->
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
  | DSubst :
             #fs:list form ->
             #f:form ->
             h:heap ->
             deduce fs f ->
             deduce fs (subst 0 h f)
  | DForallIntro : 
             #fs:list form ->
             #f:form ->
             deduce fs f ->
             deduce fs (FForall f)
  | DForallElim :
             #fs:list form ->
             #a:Type ->
             #f:form ->
             deduce fs (FForall f) ->
             h:heap ->
             deduce fs (subst 0 h f)
  | DBexp :
              fs:list form ->
              b:bexp ->
              h:heap{eval_bexp h b = true} ->
              deduce fs (FBexp b (HvHeap h))
(*
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
