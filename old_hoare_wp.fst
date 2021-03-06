module WeakestPrecondition
open Expressions

(* Formulas *)
type form =
| FTrue   : form
| FNot    : form -> form
| FImpl   : form -> form -> form
| FAnd    : form -> form -> form
| FForall : #a:Type -> (a -> form) -> form
| FEq     : #a:Type -> a -> a -> form

type invalid : form -> Type = 
  | INot        : #f1:form    -> 
                  valid f1    -> 
                  invalid (FNot f1)
  | IImpl       : #f1:form    ->
                  #f2:form    ->
                  valid f1    ->
                  invalid f2  ->
                  invalid (FImpl f1 f2)
  | IAndL       : #f1:form    ->
                  f2:form     ->
                  invalid f1  ->
                  invalid (FAnd f1 f2)
  | IAndR       : f1:form    ->
                  #f2:form    ->
                  invalid f1  ->
                  invalid (FAnd f1 f2)
  | IForall     : #a:Type     ->
                  #f:(a -> Tot form) ->
                  #x:a        ->
                  invalid (f x)  ->
                  invalid (FForall f)
  | IEq         : #a:Type     ->
                  x1:a        ->
		  x2:a{x1 <> x2} ->
		  invalid (FEq x1 x2)


and valid : form -> Type =
  | VTrue       : valid FTrue
  | VNot        : #f1:form    -> 
                  invalid f1  -> 
                  valid (FNot f1)
  | VImpl       : #f1:form    -> 
                  #f2:form     ->
                  (f : valid f1 -> valid f2) -> 
                  valid (FImpl f1 f2)
  | VAnd        : #f1:form    -> 
                  #f2:form    -> 
                  valid f1    -> 
                  valid f2    -> 
                  valid (FAnd f1 f2)
  | VForall     : #a:Type     ->
                  #p:(a -> Tot form)->
                  f: (x:a-> Tot (valid (p x)))->
                  valid (FForall p)
  | VEq         : #a:Type     ->
                  x:a         ->
                  valid (FEq x x)


(*
val f: v:form -> Tot (r:bool{r = true <==> (exists (p:valid v). True)})
let rec f v = match v with
| FTrue -> true
| FNot v' -> not (f v')
| _ -> false
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
  (forall h h'. reval c h h' ==> valid (p h) ==> valid (q h'))

(* hoare constructive *)
type hoare_c (p:pred) (c:com) (q:pred) : Type =
  (#h:heap -> #h':heap -> reval c h h' -> valid (p h) -> valid (q h'))

val pred_sub : id -> aexp -> pred -> Tot pred
let pred_sub x e p = fun h -> p (update h x (eval_aexp h e))

val hoare_assign : q:pred -> x:id -> e:aexp -> Tot (hoare_c (pred_sub x e q) (Assign x e) q)
let hoare_assign q x e = fun h h' pr (vh:valid (pred_sub x e q h)) -> vh


val pred_impl : pred -> pred -> Tot form
let pred_impl p q = FForall (fun h -> FImpl (p h) (q h))


val hoare_consequence : p:pred -> p':pred -> q:pred -> q':pred -> c:com ->
                        hoare_c p' c q'        -> 
                        valid (pred_impl p p') -> 
                        valid (pred_impl q' q) -> 
                        Tot (hoare_c p c q)
let hoare_consequence p p' q q' c hpcq' vpp' vqq' = 
    fun h h' pr (vph:valid (p h)) -> 
        let VForall fpp' = vpp' in
        //assert (is_VImpl (fpp' h)); (*BUG: adding this assert makes the compilation explode*)
        let VImpl fpp' = fpp' h in
        let vpph = fpp' vph in
        let vqphp = hpcq' pr vpph in
        let VForall fqq' = vqq' in
        let VImpl fqq'   = fqq' vqphp in
        fqq' vqphp


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
                hoare_c (fun h -> FAnd (p h) (FNot (bpred be h))) e q ->
                Tot (hoare_c p (If be t e) q)
let hoare_if p q be t e hthen helse = 
    fun h h' pr (vh:valid (p h)) -> (*vh -> *)
        match pr with
          | EIfTrue be cthen celse rthen -> hthen rthen (VAnd vh (VEq true))
          | EIfFalse be cthen celse relse -> helse relse (VAnd vh (VNot (IEq false true)))

(*

(* this is weaker than usual and can only show the annotated invariant *)
assume val hoare_while : p:pred -> be:bexp -> c:com -> Lemma
  (requires (hoare (fun h -> FAnd (p h) (bpred be h)) c p))
  (ensures (hoare p (While be c p) (fun h -> FAnd (p h) (FNot (bpred be h)))))


(* Weakest Liberal Precondition (aka. predicate transformer semantics) *)

val pand : pred -> pred -> Tot pred
let pand p1 p2 h = FAnd (p1 h) (p2 h)

val pimpl : pred -> pred -> Tot pred
let pimpl p1 p2 h = FImpl (p1 h) (p2 h)

val pnot : pred -> Tot pred
let pnot p h = FNot (p h)

val pif : pred -> pred -> pred -> Tot pred
let pif pg pt pe = pand (pimpl pg pt) (pimpl (pnot pg) pe)

val wlp : com -> pred -> Tot pred
let rec wlp c q =
  match c with
  | Skip -> q
  | Assign x e -> pred_sub x e q
  | Seq c1 c2 -> wlp c1 (wlp c2 q)
  | If be ct ce -> pif (bpred be) (wlp ct q) (wlp ce q)
  | While be c' i -> pand i (pif (bpred be) (wlp c' i) q)

val wlp_sound : c:com -> q:pred -> Lemma (hoare (wlp c q) c q)
let rec wlp_sound c q =
  match c with
  | Skip -> hoare_skip q
  | Assign x e -> hoare_assign q x e
  | Seq c1 c2 ->
     (wlp_sound c2 q; wlp_sound c1 (wlp c2 q);
      hoare_seq (wlp c1 (wlp c2 q)) (wlp c2 q) q c1 c2)
  | _ -> admit() (* need more definitions to prove the rest formally *)

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
  Lemma (requires (hoare p c q)) (ensures (valid (pred_impl p (wlp c q))))
  *)
