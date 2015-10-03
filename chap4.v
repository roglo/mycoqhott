(* experimentations on HoTT *)
(* requires coq 8.5 *)

Require Import Utf8 QArith NPeano.
Require Import chap1 chap2 chap3.

(* no default implicit without arguments *)
Arguments eq_refl [A] x.

Notation "⊥" := False.
Notation "⊤" := True.
Notation "'ℬ'" := (bool : Type).
Notation "A ⇔ B" := ((A → B) * (B → A))%type (at level 100).
Notation "( x , y ) '_{' P }" := (existT P x y)
  (at level 0, format "'[' ( x ,  y ) _{ P } ']'", only parsing).

Open Scope nat_scope.

(* "Chapter 4 - Equivalences" *)

(* "4.1 - Quasi-inverses" *)

(* "Lemma 4.1.1. If f : A → B is such that qinv(f) is inhabited, then
        qinv(f) ≃ (Π (x : A) (x = x). " *)

Definition hott_4_1_1 A B (f : A → B) (q : qinv f) :
  qinv f ≃ (Π (x : A), x = x).
Proof.
assert (e : isequiv f) by (apply qinv_isequiv, q).
set (fe := existT isequiv f e : A ≃ B); simpl in fe.
remember (ua fe) as p eqn:r.
set (s := (idtoeqv_ua fe)⁻¹ : fe = idtoeqv (ua fe)); simpl in s.
rewrite <- r in s.
destruct p; unfold idtoeqv in s; simpl in s.
subst fe; injection s; clear s; intros s t; subst f.

unfold qinv.
apply (@equiv_compose _ ({g : A → A & ((g = id) * (g = id))%type})).
bbb.

eapply equiv_compose.
Check @ex_2_10.
(* @ex_2_10
     : ∀ (A : Type) (B : A → Type) (C : {x : A & B x} → Type),
       {x : A & {y : B x & C (existT (λ x0 : A, B x0) x y)}}
       ≃ {p : {x : A & B x} & C p} *)

bbb.
Definition ex_2_10 {A B C} :
  (Σ (x : A), Σ (y : B x), C (existT _ x y)) ≃ (Σ (p : Σ (x : A), B x), C p).

exists (λ _ x, eq_refl x).
apply qinv_isequiv.
exists (λ _, existT _ id (@eq_refl A, @eq_refl A)).
unfold "◦", "~~", id; simpl.
split.
 intros g.
 apply Π_type.funext; intros x.
bbb.

