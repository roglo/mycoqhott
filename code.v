(* proving nat and list are hset *)

Set Universe Polymorphism.
Require Import Utf8.

Definition isSet A := ∀ (x y : A) (p q : x = y), p = q.

Definition homotopy {A B} (f g : A → B) := ∀ x : A, f x = g x.
Definition composite {A B C} (f : A → B) (g : B → C) x := g (f x).

Definition isequiv {A B : Type} f :=
  ({ g : B → A & homotopy (composite g f) (@id _) } *
   { h : B → A & homotopy (composite f h) (@id _) })%type.

Definition equivalence (A B : Type) := { f : A → B & isequiv f }.

Definition transport {A} P {x y : A} (p : x = y) : P x → P y :=
  match p with
  | eq_refl _ => @id _
  end.

Definition ap {A B x y} (f : A → B) (p : x = y) : f x = f y :=
  match p with
  | eq_refl _ => eq_refl (f x)
  end.

Definition qinv {A B} (f : A → B) :=
  { g : B → A &
    (homotopy (composite g f) (@id _) *
     homotopy (composite f g) (@id _))%type }.

Definition qinv_isequiv {A B} (f : A → B) : qinv f → isequiv f.
Proof.
intros p.
destruct p as (g, (α, β)).
split; exists g; assumption.
Defined.

Lemma equiv_compose {A B C} :
  ∀ (f : equivalence A B) (g : equivalence B C), equivalence A C.
Proof.
intros eqf eqg.
destruct eqf as (f, ((f₁, eqf₁), (f₂, eqf₂))).
destruct eqg as (g, ((g₁, eqg₁), (g₂, eqg₂))).
unfold equivalence.
exists (composite f g).
split.
 exists (composite g₁ f₁).
 intros c; unfold composite; simpl.
 transitivity (g (g₁ c)); [ apply ap, eqf₁ | apply eqg₁ ].

 exists (composite g₂ f₂).
 intros a; unfold composite; simpl.
 transitivity (f₂ (f a)); [ apply ap, eqg₂ | apply eqf₂ ].
Defined.

Definition hott_2_3_10 {A B x y} :
    ∀ (f : A → B) (P : B → Type) (p : x = y) (u : P (f x)),
    transport (composite f P) p u = transport P (ap f p) u
 := λ f P p u,
    match p with
    | eq_refl _ => eq_refl (transport P (ap f (eq_refl x)) u)
    end.

(* proof nat is hset *)

Fixpoint N_code m n : Type :=
  match (m, n) with
  | (0, 0) => True
  | (S m, 0) => False
  | (0, S n) => False
  | (S m, S n) => N_code m n
  end.

Fixpoint N_r n : N_code n n :=
  match n with
  | 0 => I
  | S m => N_r m
  end.

Definition N_encode (m n : nat) : m = n → N_code m n :=
  λ p, transport (N_code m) p (N_r m).

Definition N_decode (m n : nat) : N_code m n → m = n.
Proof.
revert m n.
fix IHn 1.
intros m n p.
destruct m.
 destruct n; [ reflexivity | refine (match p with end) ].

 destruct n; [ refine (match p with end) | simpl in p ].
 apply ap, IHn, p.
Defined.

Theorem N_decode_encode {m n} : ∀ p, N_decode m n (N_encode m n p) = p.
Proof.
intros p.
destruct p; simpl; unfold id; simpl.
induction m; [ reflexivity | simpl ].
apply (ap (ap S)) in IHm; assumption.
Defined.

Theorem N_encode_decode {m n} : ∀ c, N_encode m n (N_decode m n c) = c.
Proof.
intros c.
revert n c; induction m; intros.
 simpl in c.
 destruct n, c; reflexivity.

 simpl in c.
 destruct n; [ refine (match c with end) | simpl ].
 unfold N_encode.
 rewrite <- (hott_2_3_10 S (N_code (S m)) (N_decode m n c)).
 apply IHm.
Defined.

Theorem N_hott_2_13_1 : ∀ m n, equivalence (m = n) (N_code m n).
Proof.
intros.
exists (N_encode m n); apply qinv_isequiv.
exists (N_decode m n).
unfold composite, homotopy, id; simpl.
split; intros p; [ apply N_encode_decode | apply N_decode_encode ].
Defined.

Require Import Arith.

Definition N_code_equiv_1_or_0 m n :
  (equivalence (N_code m n) True) + (equivalence (N_code m n) False).
Proof.
destruct (eq_nat_dec m n) as [H1| H1].
 left; subst m.
 exists (λ c, I); apply qinv_isequiv.
 exists (λ _, N_r n).
 unfold composite, homotopy, id; simpl.
 split; [ intros u; destruct u; reflexivity | intros c ].
 induction n; [ destruct c; reflexivity | apply IHn ].

 right.
 exists (λ c, H1 (N_decode m n c)); apply qinv_isequiv.
 exists (λ p : False, match p with end).
 unfold composite, homotopy, id.
 split; [ intros p; destruct p | ].
 intros c; destruct (H1 (N_decode m n c)).
Defined.

Definition isSet_nat : isSet nat.
Proof.
intros m n p q.
pose proof N_hott_2_13_1 m n as r.
pose proof N_code_equiv_1_or_0 m n as s.
destruct s as [s| s].
 eapply equiv_compose in s; [ | apply r ].
 destruct s as (f, ((g, Hg), (h, Hh))).
 unfold composite, homotopy, id in Hg, Hh.
 pose proof Hh p as Hp.
 pose proof Hh q as Hq.
 destruct (f p), (f q).
 subst p q; reflexivity.

 eapply equiv_compose in s; [ | apply r ].
 destruct s as (f, ((g, Hg), (h, Hh))).
 exfalso; apply f, p.
Defined.

(* proof list is hset *)

Require Import List.
Import List.ListNotations.

Fixpoint list_code a b : Type :=
  match (a, b) with
  | ([], []) => True
  | (_ :: _, []) => False
  | ([], _ :: _) => False
  | (a :: al, b :: bl) => (a = b * list_code al bl)%type
  end.

Check list_code.

Fixpoint list_r n : list_code n n :=
  match n with
  | [] => I
  | a :: l => list_r l
  end.

Definition N_encode (m n : nat) : m = n → N_code m n :=
  λ p, transport (N_code m) p (N_r m).
