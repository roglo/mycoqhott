(* proving nat and list are hset *)

Set Universe Polymorphism.
Set Nested Proofs Allowed.

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

Theorem equiv_compose {A B C} :
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

Fixpoint nat_code m n : Type :=
  match (m, n) with
  | (0, 0) => True
  | (S m, 0) => False
  | (0, S n) => False
  | (S m, S n) => nat_code m n
  end.

Fixpoint nat_r n : nat_code n n :=
  match n with
  | 0 => I
  | S m => nat_r m
  end.

Definition nat_encode (m n : nat) : m = n → nat_code m n :=
  λ p, transport (nat_code m) p (nat_r m).

Definition nat_decode (m n : nat) : nat_code m n → m = n.
Proof.
revert m n.
fix IHn 1.
intros m n p.
destruct m.
 destruct n; [ reflexivity | refine (match p with end) ].

 destruct n; [ refine (match p with end) | simpl in p ].
 apply ap, IHn, p.
Defined.

Theorem nat_decode_encode {m n} : ∀ p, nat_decode m n (nat_encode m n p) = p.
Proof.
intros p.
destruct p; simpl; unfold id; simpl.
induction m; [ reflexivity | simpl ].
apply (ap (ap S)) in IHm; assumption.
Defined.

Theorem nat_encode_decode {m n} : ∀ c, nat_encode m n (nat_decode m n c) = c.
Proof.
intros c.
revert n c; induction m; intros.
 simpl in c.
 destruct n, c; reflexivity.

 simpl in c.
 destruct n; [ refine (match c with end) | simpl ].
 unfold nat_encode.
 rewrite <- (hott_2_3_10 S (nat_code (S m)) (nat_decode m n c)).
 apply IHm.
Defined.

Theorem nat_hott_2_13_1 : ∀ m n, equivalence (m = n) (nat_code m n).
Proof.
intros.
exists (nat_encode m n); apply qinv_isequiv.
exists (nat_decode m n).
unfold composite, homotopy, id; simpl.
split; intros p; [ apply nat_encode_decode | apply nat_decode_encode ].
Defined.

Require Import Arith.

Definition nat_code_equiv_1_or_0 m n :
  (equivalence (nat_code m n) True) + (equivalence (nat_code m n) False).
Proof.
destruct (eq_nat_dec m n) as [H1| H1].
 left; subst m.
 exists (λ c, I); apply qinv_isequiv.
 exists (λ _, nat_r n).
 unfold composite, homotopy, id; simpl.
 split; [ intros u; destruct u; reflexivity | intros c ].
 induction n; [ destruct c; reflexivity | apply IHn ].

 right.
 exists (λ c, H1 (nat_decode m n c)); apply qinv_isequiv.
 exists (λ p : False, match p with end).
 unfold composite, homotopy, id.
 split; [ intros p; destruct p | ].
 intros c; destruct (H1 (nat_decode m n c)).
Defined.

Definition isSet_nat : isSet nat.
Proof.
intros m n p q.
pose proof nat_hott_2_13_1 m n as r.
pose proof nat_code_equiv_1_or_0 m n as s.
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

(* proof bool is hset *)

Definition isSet_bool : isSet bool.
Proof.
intros x y p q.
destruct x, y; try discriminate p.
 refine (match p with eq_refl _ => _ end).
 refine (match q with eq_refl _ => _ end).
 reflexivity.

 refine (match p with eq_refl _ => _ end).
 refine (match q with eq_refl _ => _ end).
 reflexivity.
Defined.

(* proof list is hset *)

Require Import List.
Import List.ListNotations.

Fixpoint list_code {A} (la lb : list A) : Type :=
  match (la, lb) with
  | ([], []) => True
  | (_ :: _, []) => False
  | ([], _ :: _) => False
  | (a :: la, b :: lb) => ((a = b) * list_code la lb)%type
  end.

Theorem list_r {A} (l : list A) : @list_code A l l.
Proof.
now induction l.
Defined.

Definition list_encode {A} (la lb : list A) : la = lb → list_code la lb :=
  λ p, transport (list_code la) p (list_r la).

Definition list_decode {A} (la lb : list A) : list_code la lb → la = lb.
Proof.
revert la lb.
fix IHn 1.
intros m n p.
destruct m.
 destruct n; [ reflexivity | refine (match p with end) ].

 destruct n; [ refine (match p with end) | simpl in p ].
 destruct p as (pa, pl).
 destruct pa.
 specialize (IHn m n pl) as H1.
 now destruct H1.
Defined.
