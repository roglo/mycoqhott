Require Import Utf8.
Require Import chap1 chap2.

Definition fib {A B} (f : A → B) (y : B) := Σ (x : A), (f x = y).

(* a funib is a generalization of functions and fibers; given types A
   and B, it associates any value a : A to a subset in B; for a function,
   this subset has only one value (it is contractible); for a fiber, this
   subset is the fiber over a *)

Definition funib A B (R : A → B → Type) (x : A) := Σ (y : B), R x y.

Definition fun_is_funib A B (f : A → B) :
  Σ (R : A → B → Type), Π (a : A), Π (u : funib A B R a), Σ_pr₁ u = f a.
Proof.
exists (λ a b, b = f a).
intros a u; unfold funib in u.
destruct u as (b, p); apply p.
Defined.

Definition fib_is_funib A B (f : A → B) :
  Σ (R : B → A → Type), Π (u : ∀ b, fib f b), Π (b : B),
  Π (v : funib B A R b), (b = f (Σ_pr₁ v)) * R b (Σ_pr₁ (u b)).
Proof.
exists (λ b a, b = f a).
intros u b v; destruct v as (a, p); simpl.
split; [ apply p | ].
destruct (u b) as (x, q); simpl.
apply invert, q.
Defined.
