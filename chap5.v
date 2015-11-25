(* experimentations on HoTT *)
(* requires coq 8.5 *)

Require Import Utf8 QArith NPeano.
Require Import chap1 chap2 chap3 chap4.
Set Universe Polymorphism.

(* no default implicit without arguments *)
Arguments eq_refl [A] x.

Notation "⊥" := False.
Notation "⊤" := True.
Notation "'ℬ'" := (bool : Type).
Notation "A ⇔ B" := ((A → B) * (B → A))%type (at level 100).
Notation "( x , y ) '_{' P }" := (existT P x y)
  (at level 0, format "'[' ( x ,  y ) _{ P } ']'", only parsing).
Notation "f '~~' g" := (dt_homotopy f g) (at level 70).

Open Scope nat_scope.

(* "Chapter 5 - Induction" *)

(* "5.1 Introduction to inductive types" *)

(* "Theorem 5.1.1. Let f, g : Π (x:ℕ) E(x) be two functions
    which satisfy the recurrences
         e_z : E(0)     and     e_s : Π (n : ℕ) E(n) → E (succ(n))
    up to propositional equality, i.e., such that
         f(0) = e_z     and     g(0) = e z
    as well as
         Π (n : ℕ) f(succ(n)) = e_s(n, f(n)),
         Π (n : ℕ) g(succ(n)) = e_s(n, g(n)),
    Then f and g are equal." *)

Definition hott_5_1_1 E (f g : Π (x : ℕ), E x)
  (e_z : E 0) (e_s : Π (n : ℕ), E n → E (S n)) :
  f 0 = e_z → g 0 = e_z
  → (Π (n : ℕ), f (S n) = e_s n (f n))
  → (Π (n : ℕ), g (S n) = e_s n (g n))
  → f = g.
Proof.
intros fz gz fs gs.
apply Π_type.funext; intros n.
induction n; [ destruct fz, gz; apply eq_refl | ].
pose proof (fs n) as p.
pose proof (gs n) as q.
destruct IHn, p, q; apply eq_refl.
Defined.

(* "5.2 Uniqueness of inductive types" *)

Inductive ℕ' : Set := O' | S' : ℕ' → ℕ'.

Definition f : ℕ → ℕ' := nat_rec (λ n, ℕ') O' (λ n, S').
Definition g : ℕ' → ℕ := ℕ'_rec (λ n', ℕ) O (λ n', S).

Definition ℕ_gf : Π (n : ℕ), g (f n) = n.
Proof.
intros n.
change ((g ◦ f) n = id n); apply hap.
eapply hott_5_1_1; intros; try apply eq_refl.
Defined.

Definition ℕ'_fg : Π (n : ℕ'), f (g n) = n.
Proof.
intros n.
induction n; [ apply eq_refl | simpl; apply ap, IHn ].
Defined.
