module WeakestPrecondition
open Expressions

(* Formulas *)
type form =
| FFalse  : form
| FImpl   : form -> form -> form
| FAnd    : form -> form -> form
| FForall : (heap -> Tot form) -> form
| FEq     : #a:Type -> a -> a -> form
(*| FBexp   : bexp -> heap -> form*)

val fnot : form -> Tot form
let fnot f = FImpl f FFalse

val ftrue : form
let ftrue = FEq () ()

val ffor : form -> form -> Tot form
(*
let ffor f1 f2 = fnot (FAnd (fnot f1) (fnot f2))
(f1 => false) /\ (f2 => false) ==> false
*)
let ffor f1 f2 = FImpl (fnot f1) f2
(* (f1 => false) => f2 *)

type deduce : form -> Type =
  | DFalseElim :
             f:form ->
             deduce FFalse ->
             deduce f
  | DImplIntro :
             #f1:form ->
             #f2:form ->
             (deduce f1 -> Tot (deduce f2)) -> (* <-- meta level implication *)
             deduce (FImpl f1 f2)
  | DImplElim :
	     #f1:form ->
             #f2:form ->
             deduce (FImpl f1 f2) ->
             deduce f1 ->
             deduce f2
  | DAndIntro :
             #f1:form ->
             #f2:form ->
             deduce f1 ->
             deduce f2 ->
             deduce (FAnd f1 f2)
  | DAndElim1 :
             #f1:form ->
             #f2:form ->
             deduce (FAnd f1 f2) ->
             deduce f1
  | DAndElim2 :
             #f1:form ->
             #f2:form ->
             deduce (FAnd f1 f2) ->
             deduce f2
  | DForallIntro : 
             f:(heap->Tot form) ->
             (x:heap -> Tot (deduce (f x))) -> (* <-- meta level quantification *)
             deduce (FForall f)
  | DForallElim :
             f:(heap->Tot form) ->
             deduce (FForall f) ->
             x:heap ->
             deduce (f x)
  | DEqRefl : 
              #a:Type ->
              e:a ->
              deduce (FEq e e)
  | DNotEq :
              #a:Type ->
              e1:a ->
              e2:a{e1 <> e2} ->
              deduce (fnot (FEq e1 e2))
  | DEqSubst :
              #a:Type ->
              #e1:a ->
              #e2:a ->
              #f:(a -> Tot form) ->
              deduce (FEq e1 e2) ->
              deduce (f e1) ->
              deduce (f e2)
  | DExMid :
              f:form ->
              deduce (ffor f (fnot f))

(* Derivable; see bpred below
  | DBexpIntro :
              b:bexp ->
              h:heap{eval_bexp h b = true} ->
              deduce (FBexp b h)
*)
(* Derivable rules
  | DEqSymm : 
              #a:Type ->
              e1:a ->
              e2:a ->
              deduce (FEq e1 e2) ->
              deduce (FEq e2 e1)
  | DEqTran : 
              #a:Type ->
              e1:a ->
              e2:a ->
              e3:a ->
              deduce (FEq e1 e2) ->
              deduce (FEq e2 e3) ->
              deduce (FEq e1 e3)
 *)

(* Predicates (aka. assertions) *)
type pred = heap -> Tot form


(* Commands (aka. statements) -- while has loop invariant *)
type com = 
| Skip   : com
| Assign : var:id -> term:aexp -> com
| Seq    : first:com -> second:com -> com
| If     : cond:bexp -> then_branch:com -> else_branch:com -> com
| While  : cond:bexp -> body:com -> inv:pred -> com

val update : heap -> id -> int -> Tot heap 
let update h x v = fun y -> if y = x then v else h y


(* Evaluation relation *)
type reval : com -> heap -> heap -> Type =
| ESkip      : h0:heap ->
               reval Skip h0 h0

| EAssign    : h0:heap -> x:id -> e:aexp ->
               reval (Assign x e) h0 (update h0 x (eval_aexp h0 e))

| ESeq       : #h0:heap -> #c1:com -> #c2:com -> #h1:heap -> #h2:heap -> 
               reval c1 h0 h1 ->
               reval c2 h1 h2 ->
               reval (Seq c1 c2) h0 h2

| EIfTrue    : #h0:heap -> be:bexp{eval_bexp h0 be = true} ->
               ct:com -> ce:com -> #h1:heap ->
               reval ct h0 h1 ->
               reval (If be ct ce) h0 h1

| EIfFalse   : #h0:heap -> be:bexp{eval_bexp h0 be = false} ->
               ct:com -> ce:com -> #h1:heap ->
               reval ce h0 h1 ->
               reval (If be ct ce) h0 h1

| EWhileEnd  : #h0:heap -> be:bexp{eval_bexp h0 be = false} ->
               cb:com -> i:pred ->
               reval (While be cb i) h0 h0

| EWhileLoop : #h0:heap -> be:bexp{eval_bexp h0 be = true} ->
               cb:com -> i:pred -> #h1:heap -> #h2:heap ->
               reval cb h0 h1 ->
               reval (While be cb i) h1 h2 ->
               reval (While be cb i) h0 h2


(* Defining a new eval that is correct with respect to reval
   (needs to be proved in intrinsic (+ constructive) style(s),
   because eval has side-effects) *)

val eval : c:com -> h0:heap -> Dv (|h1:heap * reval c h0 h1|)
let rec eval c h0 =
  match c with
  | Skip ->
     (|h0, ESkip h0|)
  | Assign x e ->
     (|update h0 x (eval_aexp h0 e), EAssign h0 x e|)
  | Seq c1 c2 ->
     let (|h1, p1|) = eval c1 h0 in
     let (|h2, p2|) = eval c2 h1 in
     (|h2, ESeq p1 p2|)
  | If be ct ce ->
     if eval_bexp h0 be then
       let (|h1, p1|) = eval ct h0 in
       (|h1, EIfTrue be ct ce p1|)
     else
       let (|h1, p1|) = eval ce h0 in
       (|h1, EIfFalse be ct ce p1|)
  | While be cb i ->
     if eval_bexp h0 be
     then let (|h1, p1|) = eval cb h0 in
          let (|h2, p2|) = eval c  h1 in
          (|h2, EWhileLoop be cb i p1 p2|)
     else (|h0, EWhileEnd be cb i|)



(* Hoare logic *)

(* Hoare triples - partial correctness (no termination) *)
type hoare (p:pred) (c:com) (q:pred) : Type =
  (forall h h'. reval c h h' ==> deduce (p h) ==> deduce (q h'))

(* hoare constructive *)
type hoare_c (p:pred) (c:com) (q:pred) : Type =
  (#h:heap -> #h':heap -> reval c h h' -> deduce (p h) -> deduce (q h'))

val pred_sub : id -> aexp -> pred -> Tot pred
let pred_sub x e p = fun h -> p (update h x (eval_aexp h e))

val hoare_assign : q:pred -> x:id -> e:aexp -> Tot (hoare_c (pred_sub x e q) (Assign x e) q)
let hoare_assign q x e = fun h h' pr (vh:deduce (pred_sub x e q h)) -> vh

val pand : pred -> pred -> Tot pred
let pand p1 p2 h = FAnd (p1 h) (p2 h)

val pimpl : pred -> pred -> Tot pred
let pimpl p1 p2 h = FImpl (p1 h) (p2 h)

val pnot : pred -> Tot pred
let pnot p h = fnot (p h)

val pif : pred -> pred -> pred -> Tot pred
let pif pg pt pe = pand (pimpl pg pt) (pimpl (pnot pg) pe)

val pred_impl : pred -> pred -> Tot form
let pred_impl p q = FForall (pimpl p q)


val hoare_consequence : p:pred -> p':pred -> q:pred -> q':pred -> c:com ->
                        hoare_c p' c q'        -> 
                        deduce (pred_impl p p') -> 
                        deduce (pred_impl q' q) -> 
                        Tot (hoare_c p c q)
let hoare_consequence p p' q q' c hpcq' vpp' vqq' = 
    fun h h' pr (vph:deduce (p h)) -> 
        let vpp'  = DForallElim (pimpl p p') vpp' h in // deduce ((pimpl p p') h)
        let vpph  = DImplElim (p h) (p' h) vpp' vph in
        let vqqh' = hpcq' pr vpph in
        let vqq'  = DForallElim (pimpl q' q) vqq' h' in // deduce ((pimpl q q') h')
        let vqqh' = DImplElim (q' h') (q h') vqq' vqqh' in //deduce (q h')
        vqqh'

val hoare_skip : p:pred -> Tot (hoare_c p Skip p)
let hoare_skip p = fun h h' pr vph -> vph 


val hoare_seq : p:pred -> c1:com -> q:pred -> c2:com -> r:pred -> 
        hpq : hoare_c p c1 q  -> 
        hqr:hoare_c q c2 r    ->
        Tot (hoare_c p (Seq c1 c2) r)
let hoare_seq p c1 q c2 r hpq hqr = 
    fun h1 h3 pr vph1 ->
        let ESeq r12 r23 = pr in 
        let vph2= hpq r12 vph1 in
        hqr r23 vph2

val bpred : bexp -> Tot pred
let bpred be h = FEq bool (eval_bexp h be) true


val hoare_if : p:pred -> q:pred -> be:bexp -> t:com -> e:com ->
                hoare_c (fun h -> FAnd (p h) (bpred be h))  t q ->
                hoare_c (fun h -> FAnd (p h) (fnot (bpred be h))) e q ->
                Tot (hoare_c p (If be t e) q)
let hoare_if p q be t e hthen helse = 
    fun h h' pr (ph:deduce (p h)) -> (*ph -> *)
        match pr with
          | EIfTrue be cthen celse rthen  -> hthen rthen (DAndIntro ph (DEqRefl true))
          | EIfFalse be cthen celse relse -> helse relse (DAndIntro ph (DNotEq false true))

(* this is weaker than usual and can only show the annotated invariant *)


val hoare_while : p:pred -> be:bexp -> c:com -> 
  hoare_c (fun h -> FAnd (p h) (bpred be h)) c p ->
  Tot (hoare_c p (While be c p) (fun h -> FAnd (p h) (fnot (bpred be h))))
let (*rec*) hoare_while p be c hbody = 
    fun h h' pr (ph:deduce (p h)) -> 
        match pr with
          | EWhileEnd  be cb i -> (DAndIntro ph (DNotEq false true))
          | EWhileLoop be cb i rbody rloop -> 
              let vph1 = hbody rbody (DAndIntro ph (DEqRefl true)) in
              //let _ = hoare_while p be c hbody rbody vph1 in
              magic()
          
(*
rbody = h cb h'
rloop = h' (While be cb i) h''
| EWhileLoop : #h0:heap -> be:bexp{eval_bexp h0 be = true} ->
               cb:com -> i:pred -> #h1:heap -> #h2:heap ->
               reval cb h0 h1 ->
               reval (While be cb i) h1 h2 ->
               reval (While be cb i) h0 h2

| EWhileEnd  : #h0:heap -> be:bexp{eval_bexp h0 be = false} ->
               cb:com -> i:pred ->
               reval (While be cb i) h0 h0

hoare_c (p h && be h) b (p h)
hoare_c (p h) (While be c p) (p h && not (be h))


| DNotEq :
        #a:Type ->
        e1:a ->
        e2:a{e1 <> e2} ->
        deduce (fnot (FEq e1 e2)) *)


(* Weakest Liberal Precondition (aka. predicate transformer semantics) *)

val wlp : com -> pred -> Tot pred
let rec wlp c q =
  match c with
  | Skip -> q
  | Assign x e -> pred_sub x e q
  | Seq c1 c2 -> wlp c1 (wlp c2 q)
  | If be ct ce -> pif (bpred be) (wlp ct q) (wlp ce q)
  | While be c' i -> pand i (pif (bpred be) (wlp c' i) q)

val proof_if_true : c : pred -> p1 : pred -> p2 : pred -> h : heap -> deduce( pred_impl (pand (pif c p1 p2) c) p1 h )
let proof_if_true c p1 p2 h = 
  let f lhs = 
  	let pc = DAndElim2 lhs in
  	let pcp1 = DAndElim1 (DAndElim1 lhs) in
  	DImplElim pcp1 pc 
  in DImplIntro f
val wlp_sound : c:com -> q:pred -> Tot (hoare_c (wlp c q) c q)
let rec wlp_sound c q =
  match c with
  | Skip -> hoare_skip q
  | Assign x e -> hoare_assign q x e
  | Seq c1 c2 -> 
      let wlp_c1 = wlp_sound c1 (wlp c2 q) in
      let wlp_c2 = wlp_sound c2 q in
      hoare_seq (wlp c1 (wlp c2 q)) c1 (wlp c2 q) c2 q wlp_c1 wlp_c2
  | If be ct ce -> 
      let wlp_t = wlp_sound ct q in
      let wlp_e = wlp_sound ce q in
      let vpp' = DForallIntro (pimpl (pand (pif (bpred be) (wlp ct q) (wlp ce q)) (bpred be)) (wlp ct q)) (proof_if_true (bpred be) (wlp ct q) (wlp ce q)) in 
      let p = (pimpl (pand (pif (bpred be) (wlp ct q) (wlp ce q)) (bpred be)) (wlp ct q)) in
      let p' = wlp ct q in
      let hthen = hoare_consequence p p' q q ct wlp_t vpp' (DForallIntro (pimpl q q) (fun h -> (DImplIntro (fun pq -> pq)))) in
      admit()
  | _ -> admit() (* need more definitions to prove the rest formally *)


(*

val hoare_consequence : p:pred -> p':pred -> q:pred -> q':pred -> c:com ->
                        hoare_c p' c q'        -> 
                        deduce (pred_impl p p') -> 
                        deduce (pred_impl q' q) -> 
                        Tot (hoare_c p c q)

pand (pimpl pg pt) (pimpl (pnot pg) pe)

((pg ==> pt) && (not pg ==> pe))

val hoare_if : p:pred -> q:pred -> be:bexp -> t:com -> e:com ->
                hoare_c (fun h -> FAnd (p h) (bpred be h))  t q ->
                hoare_c (fun h -> FAnd (p h) (fnot (bpred be h))) e q ->
                Tot (hoare_c p (If be t e) q)

  (#h:heap -> #h':heap -> reval c h h' -> deduce (p h) -> deduce (q h'))*)

(* Informal proofs:

Case: c = if be then st else se
-------------------------------

to show:
{ if be then wlp ct q else wlp ce q } if be then ct else ce { q }

by hoare_if, still to show:
1. {     be /\ if be then wlp ct q else wlp ce q } ct { q }
2. { not be /\ if be then wlp ct q else wlp ce q } ce { q }

by consequence (with logical equivalence in pre), still to show:
1. { wlp ct q } ct { q }
2. { wlp ce q } ce { q }

both of these are immediate from the induction hypothesis


Case: c = while be do c' inv i
------------------------------

                            -------------???????
                            { i /\ be } c' { i }
---------trivial     ---------------------------------------     -------???????
i /\ ... ==> i       { i } while be do c' inv i { i /\ ~be }     i /\ ~be ==> q
------------------------------------------------------------------------------- Conseq
    { i /\ if be then wlp c i else q } while be do c' inv i { q }


to show:
{ i /\ if be then wlp c i else q } while be do c' inv i { q }

*)

assume val wlp_weakest : c:com -> p:pred -> q:pred ->
            hpcq:hoare p c q -> 
            Tot (deduce (pred_impl p (wlp c q)))

  
