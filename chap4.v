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

Definition hott_4_1_1 A B (f : A → B) (p : qinv f) :
  qinv f ≃ (Π (x : A), x = x).
Proof.
assert (Π (x : A), x = x).
 intros x.
 destruct p as (g, (fg, gf)).
 assert ((g ◦ f) x = x) by apply gf.
bbb.

 pose proof gf x as q; unfold id in q.
 apply (ap f) in q.

 eapply compose; [ | apply (snd (Σ_pr₂ p)) ].
simpl.

 rewrite (λ x, snd (Σ_type.pr₂ p) x).
bbb.


Check (λ x, snd (Σ_type.pr₂ p) x).
exists (λ _ x, eq_refl x).
apply qinv_isequiv.
exists (λ _, p).
unfold "◦", "~~", id; simpl.
split.
 intros g.
 apply Π_type.funext; intros x.

bbb.

