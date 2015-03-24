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

assume type valid : form -> Type

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

(* TODO: remove all implicit arguments (#) from reval and redo the
         proofs within eval. Hint: do it one rule at a time. *)

(* TODO: add repeat-until to com and extend reval and eval accordingly *)


(* Hoare logic *)

(* Hoare triples - partial correctness (no termination) *)
type hoare (p:pred) (c:com) (q:pred) : Type =
  (forall h h'. reval c h h' ==> valid (p h) ==> valid (q h'))

val pred_sub : id -> aexp -> pred -> Tot pred
let pred_sub x e p = fun h -> p (update h x (eval_aexp h e))

assume val hoare_assign : q:pred -> x:id -> e:aexp ->
  Lemma (hoare (pred_sub x e q) (Assign x e) q)

val pred_impl : pred -> pred -> Tot form
let pred_impl p q = FForall (fun h -> FImpl (p h) (q h))

assume val hoare_consequence : p:pred -> p':pred -> q:pred -> q':pred -> c:com ->
  Lemma (requires (hoare p' c q'
                /\ valid (pred_impl p p') /\ valid (pred_impl q' q)))
        (ensures (hoare p c q))

assume val hoare_skip : p:pred -> Lemma (hoare p Skip p)

assume val hoare_seq : p:pred -> q:pred -> r:pred -> c1:com -> c2:com ->
  Lemma (requires (hoare p c1 q /\ hoare q c2 r))
        (ensures (hoare p (Seq c1 c2) r))

val bpred : bexp -> Tot pred
let bpred be h = FEq bool (eval_bexp h be) true

assume val hoare_if : p:pred -> q:pred -> be:bexp -> t:com -> e:com -> Lemma
        (requires (hoare (fun h -> FAnd (p h)       (bpred be h))  t q /\
                   hoare (fun h -> FAnd (p h) (FNot (bpred be h))) e q))
        (ensures (hoare p (If be t e) q))

(* this is weaker than usual and can only show the annotated invariant *)
assume val hoare_while : p:pred -> be:bexp -> c:com -> Lemma
  (requires (hoare (fun h -> FAnd (p h) (bpred be h)) c p))
  (ensures (hoare p (While be c p) (fun h -> FAnd (p h) (FNot (bpred be h)))))


(* Weakest Liberal Precondition (aka. predicate transformer semantics) *)

val fif : form -> form -> form -> Tot form
let fif fg ft fe = FAnd (FImpl       fg  ft)
                        (FImpl (FNot fg) fe)

val wlp : com -> pred -> Tot pred
let rec wlp c q =
  match c with
  | Skip -> q
  | Assign x e -> pred_sub x e q
  | Seq c1 c2 -> wlp c1 (wlp c2 q)

  | If be st se -> fun h -> fif (bpred be h) ((wlp st q) h) ((wlp se q) h)

  | While be c i -> fun h -> FAnd (i h) (fif (bpred be h) ((wlp c i) h) (q h))

val wlp_sound : c:com -> q:pred -> Lemma (hoare (wlp c q) c q)
let rec wlp_sound c q =
  match c with
  | Skip -> hoare_skip q
  | Assign x e -> hoare_assign q x e
  | Seq c1 c2 ->
     (wlp_sound c2 q; wlp_sound c1 (wlp c2 q);
      hoare_seq (wlp c1 (wlp c2 q)) (wlp c2 q) q c1 c2)
  | _ -> admit() (* need more definitions to prove the rest *)

assume val wlp_weakest : c:com -> p:pred -> q:pred ->
  Lemma (requires (hoare p c q)) (ensures (valid (pred_impl p (wlp c q))))
