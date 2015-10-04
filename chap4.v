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

Definition Σ_equiv {A} {P Q : A → Type} :
  P = Q → (Σ (x : A), P x) ≃ (Σ (x : A), Q x).
Proof.
intros p.
exists
  (λ (q : Σ (x : A), P x),
   existT Q (Σ_pr₁ q)
     match p in (_ = f) return f (Σ_pr₁ q) with
     | eq_refl _ => Σ_pr₂ q
     end : Σ (x : A), Q x).
apply qinv_isequiv.
exists
  (λ (q : Σ (x : A), Q x),
   existT P (Σ_pr₁ q)
     (match p in (_ = f) return (f (Σ_pr₁ q) → P (Σ_pr₁ q)) with
      | eq_refl _ => id
      end (Σ_pr₂ q)) : Σ (x : A), P x).
unfold "◦", "~~", id; simpl.
split; intros (x, q); destruct p; apply eq_refl.
Defined.

Definition type_pair_eq {A B C D : Type} :
  A = C → B = D → (A * B)%type = (C * D)%type.
Proof. intros p q; destruct p, q; apply eq_refl. Defined.

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
 apply Σ_equiv, Π_type.funext; intros f.
 unfold "◦", "~~"; simpl.
 apply type_pair_eq.
  apply ua.
  exists (λ g, Π_type.funext g).
  apply qinv_isequiv.
  exists (λ g x, (Π_type.happly g x)).
  unfold "◦", "~~"; simpl.
  split; [ intros p; apply invert, Π_type.funext_prop_uniq_princ | ].
  intros p; apply Π_type.funext; intros x.
  apply (Π_type.funext_quasi_inverse_of_happly f id p x).

  apply ua.
  exists (λ g, Π_type.funext g).
  apply qinv_isequiv.
  exists (λ g x, (Π_type.happly g x)).
  unfold "◦", "~~"; simpl.
  split; [ intros p; apply invert, Π_type.funext_prop_uniq_princ | ].
  intros p; apply Π_type.funext; intros x.
  apply (Π_type.funext_quasi_inverse_of_happly f id p x).

(* @ex_2_10
     : ∀ (A : Type) (B : A → Type) (C : {x : A & B x} → Type),
       {x : A & {y : B x & C (existT (λ x0 : A, B x0) x y)}}
       ≃ {p : {x : A & B x} & C p} *)
 Check (@ex_2_10 (A → A) (λ g, g = id)).
(*
  ============================
   {g : A → A & ((g = id) * (g = id))%type} ≃ (∀ x : A, x = x)
*)
eapply ex_2_10.
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

