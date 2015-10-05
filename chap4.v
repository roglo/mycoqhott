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

Definition Σ_eq_inv A (x : A) : (Σ (y : A), x = y) → (Σ (y : A), y = x).
Proof.
intros (z, s).
exists z; apply invert, s.
Defined.

Definition Σ_Π_eq_inv A :
  (Σ (x : A), Π (y : A), y = x)
  → (Σ (x : A), Π (y : A), x = y).
Proof.
intros (x, p).
exists x; intros y.
apply invert, p.
Defined.

Definition isContr_Σ_inv A (x : A) :
  isProp (Σ (y : A), y = x)
  → isContr (Σ (y : A), x = y)
  → isContr (Σ (y : A), y = x).
Proof.
intros P.
unfold isContr; intros (p, q).
pose proof (Σ_eq_inv _ _ p) as y.
exists y; intros z.
apply P.
Defined.

Definition hott_4_1_1 A B (f : A → B) (q : qinv f) :
  qinv f ≃ (Π (x : A), x = x).
Proof.
set (r (_ : A) := eq_refl (A := A)); simpl in r.
assert (e : isequiv f) by (apply qinv_isequiv, q).
set (fe := existT isequiv f e : A ≃ B); simpl in fe.
remember (ua fe) as p eqn:s.
set (t := (idtoeqv_ua fe)⁻¹ : fe = idtoeqv (ua fe)); simpl in t.
rewrite <- s in t.
destruct p; unfold idtoeqv in t; simpl in t.
subst fe; injection t; clear t; intros t u; subst f.

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

 assert
   (H : {g : A → A & ((g = id) * (g = id))%type} ≃
    (Σ (h : Σ (g : A → A), g = @id A), Σ_pr₁ h = @id A)).
  eapply equiv_compose; [ | eapply ex_2_10 ].
  simpl.
  apply Σ_equiv, Π_type.funext; intros x; apply ua.
  exists (λ p, existT (λ _, x = id) (fst p) (snd p)).
  apply qinv_isequiv.
  exists (λ p : {_ : x = id & x = id}, (Σ_pr₁ p, Σ_pr₂ p)).
  unfold "◦", "~~", id; simpl.
  split; [ intros (p, u); apply eq_refl | ].
  intros p; apply invert, surjective_pairing.

  eapply equiv_compose; [ apply H | clear H ].
  assert (p : isContr (Σ (g : A → A), g = id)).
   apply isContr_Σ_inv; [ intros (f, x) (g, y); subst f g; apply eq_refl | ].
   apply hott_3_11_8.

   apply hott_3_11_9_i in p.
   exists (λ _ _, eq_refl _).
   apply qinv_isequiv.
   exists (λ u, existT _ p (Σ_pr₂ p)).
   unfold "◦", "~~", id; simpl.
   split.
    intros u.
    apply Π_type.funext; intros x.
bbb.
(* @hott_3_11_9_i
     : Π (A : Type),
       Π (P : Π (_ : A), Type),
       Π (_ : Π (x : A), isContr (P x)), Σ (x : A), P x ≃ A *)
(* @hott_3_11_9_ii
     : Π (A : Type),
       Π (P : Π (_ : A), Type),
       Π (p : isContr A), (let a := Σ_type.pr₁ p in Σ (x : A), P x ≃ P a) *)
bbb.
