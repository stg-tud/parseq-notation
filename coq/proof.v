From Equations Require Import Equations.
From Coq.ssr Require Import ssreflect.
Require Import Utf8 List.

Require Import Lia.
Require Import Setoid.
Require Import Coq.Program.Tactics.

Set Primitive Projections.
Set Equations Transparent.
Unset Equations With Funext.
Set Structural Injection.
Set Universe Polymorphism.

Definition compose {a b c} (g:b→c) (f:a→b) (x:a) := g (f x).
Notation "f '·' g" := (fun x => f (g x)) (at level 20).
Notation "A -.> B"  := (forall x, A x -> B x) (at level 21).
Notation "A =.= B"  := (forall x, A x  = B x) (at level 21).
Notation "A -..> B" := (forall x y, A x y -> B x y) (at level 21).
Notation "A =..= B" := (forall x y, A x y  = B x y) (at level 21).

Notation "(Σ) x" := (sigT x) (at level 100).
Notation "'Σ' x .. y , P" :=
  (sigT (fun x => .. (sigT (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' Σ  x  ..  y ']' ,  '/' P ']'") : type_scope.
Notation "( x , .. , y , z )" :=
  (existT _ x .. (existT _ y z) ..)
  (right associativity, at level 0,
  format "( x ,  .. ,  y ,  z )").
Notation "A × B" := (Σ (_:A), B) (at level 21, right associativity).
Notation " x .1 " := (projT1 x) (at level 3, format "x .1").
Notation " x .2 " := (projT2 x) (at level 3, format "x .2").

Equations eq_app {A B x y} {f g: A->B} (rf: f=g) (rx: x=y): f x = g y :=
| eq_refl, eq_refl := eq_refl.
Notation "∗ a" := (@eq_refl _ a) (at level 51).
Notation "a '…' b" := (eq_app a b) (at level 51).

Equations fold {t c}: c -> (t -> c -> c) -> (list t -> c) :=
| def,f,nil   => def
| def,f,x::xs => f x (fold def f xs).

Ltac iff' := match goal with [ |- context G [ match ?c with _ => _ end ] ] => 
  lazymatch c with context G [ match ?cc with _ => _ end ] => fail | _ => idtac end;
  let H := fresh in remember c as H; dependent elimination H end.
Ltac iff := iff'; cbn.


Definition Unit: Type := unit.

Module ParSeq.

  (* Listing Lawful Monad *)
  Class Monad F := {
    pure {A}  : A -> F A;
    bind {A B}: (A -> F B) -> F A -> F B;
    ap   {A B}: F (A -> B) -> F A -> F B;
    map  {A B}: (A  ->  B) -> F A -> F B;
  }.
  Class MonadLaw F := {
    monad :> Monad F;

    idl {A B} (f: A → F B)                {x}:  bind f (pure x)    =  f x;
    idr {A B} (f: A → B)                  {x}:  bind (pure · f) x  =  map f x;
    asc {A B C} (f: A → F B) (g: B → F C) {x}:  bind g (bind f x)  =  bind (bind g · f) x;

    apl  {A B} (f: A → B)                 {x}:  ap (pure f) x      =  map (λ x', f x') x;
    apr  {A B} (f: F (A → B))             {x}:  ap f (pure x)      =  map (λ f', f' x) f;
    aplr {A B} (f: A → B)                 {x}:  map f (pure x)     =  pure (f x);

    map_map {A B C} (g: A → B) (f: B → C) {x}:  map f (map g x)    =  map (λ x, f (g x)) x;
  }.

  (* two examples for lawful monad instances, not used later *)
  Section ExampleInstanceList.
    Definition pureL {A} (x: A): list A := cons x nil.
    Equations bindL {A B}: (A -> list B) -> list A -> list B :=
    | f, nil   => nil
    | f, x::xs => f x ++ bindL f xs.
    Definition apL {A B} (f:list (A → B)) e :=
      bindL (λ f', bindL (λ e', cons (f' e') nil) e) f.
    Equations mapL {A B}: (A -> B) -> list A -> list B :=
    | f, nil   => nil
    | f, x::xs => f x :: mapL f xs.
    Local Instance monadList : Monad list := {
      pure _ x         := pureL x;
      bind A B e f     := bindL e f;
      ap   A B f e     := apL f e;
      map A B f e      := mapL f e;
    }.

    Equations map_pureL {A B} (f: A → B) (x: A):
      map f (pureL x) = pureL (f x) := | _ => _.
    Equations? map_mapL {A B C} (f:A→B) (g:B→C) (xs: list A):
      map g (map f xs) = map (g · f) xs := | _ => _.
      Proof. induction xs. auto. cbn. rewrite IHxs. auto. Defined.
    Equations? bindL_app {A B aa bb} (g: A → list B):
      bindL g (aa ++ bb) = bindL g aa ++ bindL g bb := | _ => _.
      Proof. induction aa; auto. cbn. rewrite IHaa. apply app_assoc. Defined.
    Equations? idlL {A B} (f: A → list B) (x: A):
      bind f (pure x) = f x := | _ => _.
      Proof. apply (app_nil_r _). Defined.
    Equations? idrL {A B} (f: A → B) (xs: list A):
      bind (pure · f) xs = map f xs := | _ => _.
      Proof. induction xs. auto. cbv [bindL] in IHxs |- *. cbn. rewrite IHxs. auto. Defined.
    Equations? ascL {A B C} (f: A -> list B) (g: B -> list C):
      bind g · bind f =.= bind (bind g · f) := | _ => _.
      Proof. induction x. auto. cbn in *. rewrite -IHx. apply bindL_app. Defined.
    (* #[tactic=idtac] Equations? aplL {A B} (f: A -> B) (x: list A):
      apL (pureL f) x = bindL (λ x', pureL (f x')) x   by struct x :=
    | f,nil => _ | f,x::xs => _.
      reflexivity. cbn. rewrite -aplL. cbn.
      rewrite app_nil_r app_nil_r. auto. Defined. *)
    (* #[tactic=idtac] Equations? aprL {A B} (f: list (A -> B)) (x: A):
      apL f (pureL x) = bindL (λ f', pureL (f' x)) f   by struct f :=
    | nil,x => _ | f::fs,x => _.
      reflexivity. cbn. rewrite -aprL. auto. Defined. *)
    #[tactic=idtac] Equations? aplL' {A B} (f: A -> B) (x: list A):
      apL (pureL f) x = mapL (λ x', f x') x   by struct x :=
    | f,nil => _ | f,x::xs => _.
      Proof. reflexivity. cbn. rewrite -aplL'. cbn. rewrite app_nil_r. auto. Defined.
    #[tactic=idtac] Equations? aprL' {A B} (f: list (A -> B)) (x: A):
      apL f (pureL x) = mapL (λ f', f' x) f   by struct f :=
    | nil,x => _ | f::fs,x => _.
      Proof. reflexivity. cbn. rewrite -aprL'. auto. Defined.
    Local Instance monadListLaw : MonadLaw list := {
      monad             := monadList;
      idl  _ _      f   := idlL f;
      idr  _ _      f   := idrL f;
      asc  _ _ _    f g := ascL f g;
      apl  _ _      f   := aplL' f;
      apr  _ _      f   := aprL' f;
      aplr _ _      f   := map_pureL f;
      map_map _ _ _ f g := map_mapL f g;
    }.
  End ExampleInstanceList.

  Section ExampleInstanceCounter.
    Definition ctr n := nat × n.
    Definition pureC {A} (x:A): ctr A := (0, x).
    Definition bindC {A B} (f: A → ctr B) '(n,v) :=
      let '(m,w) := f v in (n+m, w).
    Definition apC {A B} (f: ctr (A → B)) (e: ctr A) : ctr B :=
      let '(n,v) := f in
      let '(m,w) := e in
      (max n m, v w).
    Definition mapC {A B} (f: A → B) '(n,v): ctr B :=
      (n, f v).
    Definition joinC {A} (e: ctr (ctr A)): ctr A :=
      bindC id e.
    Local Instance monadCtr : Monad ctr := {
      pure _ x         := pureC x;
      bind A B e f     := bindC e f;
      ap   A B f e     := apC f e;
      map A B f e     := mapC f e;
    }.

    Equations? idlC {A B} (f: A → ctr B) (x: A):
      bind f (pure x) = f x := | _ => _.
      Proof. iff. auto. Defined.
    Equations? idrC {A B} (f: A → B) (xs: ctr A):
      bind (pure·f) xs = map f xs := | _ => _.
      Proof. induction xs. cbn. f_equal. auto. Defined.
    Equations? ascC {A B C} (f: A -> ctr B) (g: B -> ctr C) (xs: ctr A) :
      bind g (bind f xs) = bind (bind g · f) xs := | _ => _.
      Proof. induction xs. cbn. iff. iff. f_equal. auto with arith. Defined.
    #[tactic=idtac] Equations? aplC {A B} (f: A -> B) (x: ctr A):
      apC (pureC f) x = mapC (λ x', f x') x   by struct x :=
    | f,x => _.
      Proof. cbn. iff. f_equal. Defined.
    #[tactic=idtac] Equations? aprC {A B} (f: ctr (A -> B)) (x: A):
      apC f (pureC x) = map (λ f', f' x) f   by struct f :=
    | (n,f),x => _.
      Proof. cbn. f_equal. transitivity n. auto with arith. reflexivity. Defined.
    Equations map_pureC {A B} (f: A → B) (x: A):
      mapC f (pureC x) = pureC (f x) := | _ => _.
    Equations? map_mapC {A B C} (f:A→B) (g:B→C) (xs: ctr A):
      mapC g (mapC f xs) = mapC (g · f) xs := | _ => _.
      Proof. induction xs. cbn. auto. Defined.
    Local Instance monadCtrLaw : MonadLaw ctr := {
      monad             := monadCtr;
      idl _ _       f   := idlC f;
      idr _ _       f   := idrC f;
      asc _ _ _     f g := ascC f g;
      apl _ _       f   := aplC f;
      apr _ _       f   := aprC f;
      aplr _ _      f   := map_pureC f;
      map_map _ _ _ f g := map_mapC f g;
    }.
  End ExampleInstanceCounter.


  (* Listing Syntax and Semantics *)
  (* a) types *)
  Inductive ty :=
  | unt
  | arr (s t: ty)
  | prd (s t: ty)
  | sum (s t: ty)
  | MON (s: ty)
  | NAT.
  Derive NoConfusion EqDec for ty.
  Notation "𝟙"      := (unt).
  Notation "a ⇒ b"  := (arr a b) (right associativity, at level 90).
  Notation "a ∧ b"  := (prd a b) (right associativity, at level 80).
  Notation "a ∨ b"  := (sum a b) (right associativity, at level 85).
  Notation "'𝕄' a" := (MON a)   (at level 75).

  (* b) type denotation *)
  Equations EVAL (m: Type → Type): ty → Type :=
  | m,   𝟙    => Unit
  | m, s ∨ t  => EVAL m s + EVAL m t
  | m, s ∧ t  => EVAL m s × EVAL m t
  | m, s ⇒ t  => EVAL m s → EVAL m t
  | m, MON t  => m (EVAL m t)
  | m, NAT    => nat.

  (* c) labels and denotation *)
  Inductive ef := src | tgt | com.
  Derive NoConfusion EqDec for ef.
  Equations EF (m: Type → Type): ef → Type → Type :=
  | m,src, t => m t
  | m,com, t => t
  | m,tgt, t => t.

  (* d) terms and their denotation *)
  (* First we define {Γ} implicit, so that its automatically implicit
     for all constructors of T, then we clear implicits for T
     making Γ an explicit argument for T, but keeping it an implict argument
     for all constructors of T. *)
  Inductive tm {Γ: ty → Type}: ef → ty → Type :=
  | Var {B t}:   Γ t              → tm B t
  | Unt {B}:     Unit             → tm B 𝟙
  | Prd {B s t}: tm B s × tm B t  → tm B (s ∧ t) 
  | Fst {B s t}: tm B (s ∧ t)     → tm B s
  | Snd {B s t}: tm B (s ∧ t)     → tm B t
  | App {B s t}: tm B (s ⇒ t)     → (tm B s → tm B t)
  | Lam {B s t}: (Γ s → tm com t) → tm B (s ⇒ t)

  | Each {t}:    tm src (𝕄 t)   → tm src t

  | Pure {t}:    tm com t            → tm tgt (𝕄 t)
  | Join {t}:    tm tgt (𝕄 (𝕄 t))   → tm tgt (𝕄 t)
  | Map  {s t}:  tm tgt (s ⇒ t)      → (tm tgt (𝕄 s) → tm tgt (𝕄 t))
  | Ap  {s t}:   tm tgt (𝕄 (s ⇒ t)) → (tm tgt (𝕄 s) → tm tgt (𝕄 t)).
  Arguments tm Γ B: clear implicits.
  Derive Signature for tm.

  Equations eval {t m} {M:Monad m} B (e: tm (EVAL m) B t): EF m B (EVAL m t) :=
  | com, Var i       => i
  | com, Lam k       => eval _ · k
  | com, Fst e       => (eval _ e).1
  | com, Snd e       => (eval _ e).2
  | com, App e f     => (eval _ e) (eval _ f)
  | com, Prd (e, f)  => (eval _ e, eval _ f)
  | com, Unt tt      => tt

  | tgt, Var i       => i
  | tgt, Lam k       => eval _ · k
  | tgt, Unt tt      => tt
  | tgt, Fst e       => (eval _ e).1
  | tgt, Snd e       => (eval _ e).2
  | tgt, App e f     => (eval _ e) (eval _ f)
  | tgt, Prd (e, f)  => (eval _ e, eval _ f)
  | tgt, Map f e     => M.(map)  (eval _ f) (eval _ e)
  | tgt, Ap f e      => M.(ap)   (eval _ f) (eval _ e)
  | tgt, Pure e      => M.(pure) (eval _ e)
  | tgt, Join e      => M.(bind) id (eval _ e)

  | src, Var i       => M.(pure) i
  | src, Lam k       => M.(pure) (λ x: EVAL _ _, eval _ (k x))
  | src, Unt tt      => M.(pure) tt
  | src, Fst e       => M.(map) (λ e': EVAL _ _ × EVAL _ _, e'.1) (eval _ e)
  | src, Snd e       => M.(map) (λ e': EVAL _ _ × EVAL _ _, e'.2) (eval _ e)
  | src, App e f     => M.(ap) (eval _ e) (eval _ f)
  | src, Prd (e, f)  => M.(ap) (M.(map) (λ a' b': EVAL _ _, (a', b')) (eval _ e)) (eval _ f)
  | src, Each e      => M.(bind) id (eval _ e)
  .

  (* function relabel is not shown in any figure, but explained in the text. *)
  Equations relabel {a Γ t}: tm Γ com t -> tm Γ a t :=
  | Var x       => Var x
  | Unt tt      => Unt tt
  | Prd (e,f)   => Prd (relabel e, relabel f)
  | Fst e       => Fst (relabel e)
  | Snd e       => Snd (relabel e)
  | App e f     => App (relabel e) (relabel f)
  | Lam f       => Lam f
  .

  Notation "'Λ' x .. y ',' b" :=
    (Lam (λ x, .. (Lam (λ y, b)) ..)) (x binder, at level 21).
  (* Notation "f ∙ e" := (App  f e) (at level 22, left associativity). *)
  (* Notation "f ⋄ e" := (Ap  f e) (at level 22, left associativity). *)

  (* Listing Translation: PURE, AP, JOIN *)
  Equations AP {Γ s t} (f: tm Γ tgt (MON (s ⇒ t))) (e: tm Γ tgt (MON s)): tm Γ tgt (MON t) :=
  | Pure f, Pure e => Pure (App f e)
  | Pure f,      e => Map (Lam (λ x, App f (Var x))) e
  |      f, Pure e => Map (Lam (λ x, App (Var x) e)) f
  |      f,      e => Ap f e.
  Notation "f `AP` e" := (AP f e) (at level 20).

  Equations JOIN {Γ t} (e: tm Γ tgt (MON (MON t))): tm Γ tgt (MON t) :=
  | Pure e => relabel e
  |      e => Join e.

  (* parallelism-preserving CPS translation
     applicative-first monadic translation *)
  Equations PURE {Γ x} (e: tm Γ src x): tm Γ tgt (MON x) :=
  | Var i       => Pure (Var i)
  | Unt tt      => Pure (Unt tt)
  | Lam j       => Pure (Lam j)
  | Fst e       => Pure (Λ e', Fst (Var e')) `AP` PURE e
  | Snd e       => Pure (Λ e', Snd (Var e')) `AP` PURE e
  | Prd (e, f)  => Pure (Λ e' f', Prd (Var e',  Var f')) `AP` PURE e `AP` PURE f
  | App e f     => PURE e `AP` PURE f
  | Each e      => JOIN (PURE e)
  .

  (* Listing Span and Work *)
  (* a) Span *)
  Equations span {B x} (e: tm (fun _ => nat) B x): nat :=
  | Var i  => 0 | Lam e  => 0
  | Unt tt => 0 | Pure e => 0
  | Fst  e     => span e
  | Snd  e     => span e
  | Prd  (e,f) => max (span e) (span f)
  | App  e f   => max (span e) (span f)
  | Ap   e f   => max (span e) (span f)
  | Map  e f   => max (span e) (span f)
  | Join e     => S (span e)
  | Each e     => S (span e)
  .

  (* b) Work *)
  Equations work {B x} (e: tm (fun _ => nat) B x): nat :=
  | Var i  => 0 | Lam e  => 0
  | Unt tt => 0 | Pure e => 0
  | Fst  e       => work e
  | Snd  e       => work e
  | Prd  (e,f)   => work e + work f
  | App  e f     => work e + work f
  | Ap  e f      => work e + work f
  | Map  e f     => work e + work f
  | Join e       => S (work e)
  | Each e       => S (work e)
  .

  (* We use that lower equal is reflexive and transitive;
     and that maximum and plus and sucessor are respected by lower equal, e.g.,

     max_resp: x1 <= x2 -> y1 <= y2 -> max x1 y1 <= max x2 y2
     add_resp: x1 <= x2 -> y1 <= y2 -> x1 + y1 <= x2 + y2
     S_resp:   x1 <= x2 -> S x1 <= S x2
   *)
  Add Relation _ le
    reflexivity  proved by PeanoNat.Nat.le_refl
    transitivity proved by PeanoNat.Nat.le_trans as le_rel.
  Add Parametric Morphism : max  with signature le ==> le ==> le as max_mor. Proof. lia. Qed.
  Add Parametric Morphism : plus with signature le ==> le ==> le as add_mor. Proof. lia. Qed.
  Add Parametric Morphism : S    with signature le ==> le as S_mor. Proof. lia. Qed.

  (* max and add form a monoid, in particular they have a neutral element *)
  Equations? max_zero x:
    max x 0 = x  := | _ => _.
  Proof. induction x. auto. auto. Defined.
  #[tactic=idtac] Equations? add_zero x:
    x + 0 = x  := | _ => _.
  Proof. induction x. auto. auto. Defined.




  (* In the following we find the proof including the lemmas and the theorem of the paper: *)





  Ltac congruent M := apply (f_equal (fun x => M.(monad).(bind) x _))
                   || apply (f_equal (fun x => M.(monad).(map) x _))
                   || apply (f_equal (fun x => M.(monad).(pure) x)).
  Ltac simple M := rewrite /compose /M.(monad).(bind) /M.(monad).(ap) /AP /JOIN.

  (* NOTE we define a tactic to perform all tactics mentioned previously, e.g., 
     mergeing all monad/applicative/monoid/functor laws we need together into a tactic. *)

  Local Hint Rewrite
    @idl @idr @asc @apl @apr @aplr @map_map
    @PeanoNat.Nat.max_0_l @max_zero
    @add_zero (* @app_nil_r *) : laws.
  Ltac laws := autorewrite with laws.

  (* Not all of these are necessary, but there all similar so why not do them all: *)
  Ltac doit M tac :=
    dependent elimination e; cbn; try iff; try rewrite tac; try rewrite tac; cbn; laws; try rewrite tac; auto.
  Fixpoint to_eval_src {m} {M: MonadLaw m} {t} (e: tm (EVAL m) com t): eval src (relabel e)      = eval tgt (Pure e). Proof. doit M to_eval_src. Defined.
  Fixpoint to_eval_tgt {m} {M: MonadLaw m} {t} (e: tm (EVAL m) com t): eval tgt (relabel e)      = eval com e.        Proof. doit M to_eval_tgt. Defined.
  Fixpoint to_span_src                     {t} (e: tm _ com t):        span (relabel (a:=src) e) <= span e.           Proof. doit M to_span_src. Defined.
  Fixpoint to_span_tgt                     {t} (e: tm _ com t):        span (relabel (a:=tgt) e) <= span e.           Proof. doit M to_span_tgt. Defined.
  Fixpoint to_work_src                     {t} (e: tm _ com t):        work (relabel (a:=src) e) <= work e.           Proof. doit M to_work_src. Defined.
  Fixpoint to_work_tgt                     {t} (e: tm _ com t):        work (relabel (a:=tgt) e) <= work e.           Proof. doit M to_work_tgt. Defined.

  Fixpoint span_com_zero {x} (e: tm (fun _ => nat) com x): span e = 0. Proof. doit M span_com_zero. Defined.
  Fixpoint work_com_zero {x} (e: tm (fun _ => nat) com x): work e = 0. Proof. doit M work_com_zero. Defined.

  (* AP and JOIN are part of PURE, therefore to proof that PURE preserves eval, span and work, 
     we need to show that AP and JOIN also respect eval, span and work.*)
  (* AP, JOIN preserve evaluatio, and respect span and work: *)
  #[tactic=idtac] Equations? AP_eval {m} {M: MonadLaw m} {s t} (f: tm (EVAL m) tgt (MON (s ⇒ t))) (e: tm (EVAL m) tgt (MON s)):
    eval _ (AP f e) = eval _ (Ap f e)  := | f,e => _.
  Proof. dependent elimination f; dependent elimination e; cbn; by laws. Defined.
  #[tactic=idtac] Equations? AP_span {s t} (f: tm _ tgt (MON (s ⇒ t))) (e: tm _ tgt (MON s)):
    span (AP f e) = span (Ap f e)  := | f,e => _.
  Proof. dependent elimination f; dependent elimination e; cbn; by laws. Defined.
  #[tactic=idtac] Equations? AP_work {s t} (f: tm _ tgt (MON (s ⇒ t))) (e: tm _ tgt (MON s)):
    work (AP f e) = work (Ap f e)  := | f,e => _.
  Proof. dependent elimination f; dependent elimination e; cbn; by laws. Defined.

  #[tactic=idtac] Equations? JOIN_eval {m} {M: MonadLaw m} {s} (e: tm (EVAL m) tgt (MON (MON s))):
    eval _ (JOIN e) = eval _ (Join e)  := | e => _.
  Proof. dependent elimination e; cbn; laws; auto. by rewrite to_eval_tgt. Defined.
  #[tactic=idtac] Equations? JOIN_span {s} (e: tm _ tgt (MON (MON s))):
    span (JOIN e) <= span (Join e)  := | e => _.
  Proof. dependent elimination e; cbn; auto. rewrite to_span_tgt span_com_zero. auto. Defined.
  #[tactic=idtac] Equations? JOIN_work {s} (e: tm _ tgt (MON (MON s))):
    work (JOIN e) <= work (Join e)  := | e => _.
  Proof. dependent elimination e; cbn; auto. rewrite to_work_tgt work_com_zero. auto. Defined.

  (* we add the new lemmas to autorewrite *)
  Local Hint Rewrite
    @AP_eval   @AP_span   @AP_work
    @JOIN_eval @JOIN_span @JOIN_work: laws.

  Ltac break a b := repeat (
    (progress laws(* ;      idtac "  RW" *))  ||
    (progress cbn(* ;       idtac "  cbn" *)) ||
    (reflexivity(* ;        idtac "refl" *))  ||
    (progress rewrite a(* ; idtac "a" *))     ||
    (progress rewrite b(* ; idtac "b" *))     ).

  Tactic Notation "adv" tactic(y) := progress (y; try clear_dup).

  Opaque AP JOIN.

  Ltac preprocess e this :=
    dependent elimination e; repeat match goal with
    | [ H:    Unit     |- _ ] => destruct H
    | [ H:   _ + _     |- _ ] => destruct H
    | [ H:   _ × _     |- _ ] => destruct H
    (* | [ H:   _ = _     |- _ ] => discriminate H *)
    | [ H: _ → tm _ _ _ |- _ ] => (* idtac H; *) adv epose (this _ _ _ · H)
    | [ H: _ → tm _ _ _ |- _ ] => (* idtac H; *) adv epose (this _     · H)
    | [ H:     tm _ _ _ |- _ ] => (* idtac H; *) adv epose (this _ _ _   H)
    | [ H:     tm _ _ _ |- _ ] => (* idtac H; *) adv epose (this _       H)
    end.

  (* NOTE Finally we have the three important theorems: *)

  (* Theorem PURE preserves semantics *)
  #[tactic=idtac] Equations? eval_pres {m} {M: MonadLaw m} {x} (e: tm (EVAL m) src x):
    eval tgt (PURE e) = eval src e  by struct e := | _ => _.
  Proof.
    preprocess e eval_pres.
    Time par: (break e0 e; idtac " done"). (* ca. 3 secs *)
    Time Defined.                          (* ca. 13 seks *)

  (* Theorem PURE preserves span and work *)
  #[tactic=idtac] Equations? span_pres {x} (t: tm (fun _ => nat) src x):
    span (PURE t) <= span t  by struct t := | _ => _.
  Proof.
    preprocess t span_pres.
    Time all: (break l0 l; idtac " done"). (* ca. 1 seks *)
    Time Defined.                          (* ca. 2 seks *)

  #[tactic=idtac] Equations? work_pres {x} (t: tm (fun _ => nat) src x):
    work (PURE t) ≤ work t by struct t := | _ => _.
  Proof.
    preprocess t work_pres.
    Time all: (break l0 l; idtac " done"). (* ca. 1 seks *)
    Time Defined.                          (* ca. 2 seks *)

  (* Lets check that we didn't cheat and use any bad axioms.
     We expect no axiom to show up: *)
  Succeed Print Assumptions eval_pres. (* -> Closed under the global context *)
  Succeed Print Assumptions span_pres. (* -> Closed under the global context *)
  Succeed Print Assumptions work_pres. (* -> Closed under the global context *)

End ParSeq.
