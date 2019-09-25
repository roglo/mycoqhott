(* HoTT stuff required for categories *)
(* Borrowed from the other files over HoTT *)

Set Universe Polymorphism.
Set Nested Proofs Allowed.

Require Import Utf8.

Arguments id {_}.

Notation "'Σ' ( x : A ) , B" :=
  ({ x : A & B }) (at level 0, x at level 0, B at level 100, only parsing).
Notation "'Π' ( x : A ) , B" :=
  (∀ x : A, B) (at level 0, x at level 0, B at level 100, only parsing).

Definition homotopy {A B} (f g : A → B) := Π (x : A), (f x = g x).
Notation "f '∼' g" := (homotopy f g) (at level 70).

Definition composite {A B C} (f : A → B) (g : B → C) x := g (f x).
Notation "g '◦◦' f" := (composite f g) (at level 40, left associativity).

Definition isequiv {A B : Type} f :=
  ((Σ (g : B → A), (f ◦◦ g ∼ id)) * (Σ (h : B → A), (h ◦◦ f ∼ id)))%type.

Definition equivalence (A B : Type) := Σ (f : A → B), isequiv f.
Notation "A ≃ B" := (equivalence A B) (at level 70).

Definition ap {A B x y} (f : A → B) (p : x = y) : f x = f y :=
  match p with
  | eq_refl _ => eq_refl (f x)
  end.

Definition invert {A} {x y : A} (p : x = y) : y = x :=
  match p with
  | eq_refl _ => eq_refl x
  end.
Notation "p '⁻¹'" := (invert p)
  (at level 8, left associativity, format "'[v' p ']' ⁻¹").

Definition compose {A} {x y z : A} : x = y → y = z → x = z :=
  λ p,
  match p with
  | eq_refl _ => id
  end.
Notation "p • q" := (compose p q) (at level 40, left associativity).

Definition qinv {A B} (f : A → B) :=
  Σ (g : B → A), ((f ◦◦ g ∼ id) * (g ◦◦ f ∼ id))%type.

Definition isequiv_qinv {A B} (f : A → B) : isequiv f → qinv f :=
  λ p,
  match p with
  | (existT _ g Hg, existT _ h Hh) =>
      existT _ g (Hg, λ x, ((ap h (Hg (f x)))⁻¹ • Hh (g (f x)))⁻¹ • Hh x)
  end.

Theorem qinv_isequiv {A B} (f : A → B) : qinv f → isequiv f.
Proof.
intros p.
destruct p as (g, (α, β)).
split; exists g; assumption.
Defined.

Definition hott_2_1_4_i_1 {A} {x y : A} : ∀ (p : x = y),
    p = p • eq_refl y
 := (λ (p : x = y),
     match p return (p = p • eq_refl _) with
     | eq_refl _ => eq_refl (eq_refl x • eq_refl x)
     end).

Definition hott_2_1_4_i_2 {A} {x y : A} : ∀ (p : x = y),
    p = eq_refl x • p
 := (λ (p : x = y),
   match p return (p = eq_refl _ • p) with
   | eq_refl _ => eq_refl (eq_refl x • eq_refl x)
   end).

Definition ru {A} {a b : A} (p : a = b) : p = p • eq_refl b :=
  hott_2_1_4_i_1 p.

Definition dotl {A} {a b c : A} {r s : b = c}
  (q : a = b) (β : r = s) : (q • r = q • s).
Proof.
destruct q.
pose proof (@hott_2_1_4_i_2 A a c r) as H2.
apply invert in H2.
eapply compose; [ apply H2 | idtac ].
pose proof (@hott_2_1_4_i_2 A a c s) as H4.
eapply compose; [ apply β | apply H4 ].
Defined.

Definition dotr {A} {a b c : A} {p q : a = b}
  (r : b = c) (α : p = q) : (p • r = q • r).
Proof.
destruct r.
pose proof (@hott_2_1_4_i_1 A a b p) as H1.
apply invert in H1.
eapply compose; [ apply H1 | idtac ].
pose proof (@hott_2_1_4_i_1 A a b q) as H3.
eapply compose; [ apply α | apply H3 ].
Defined.

Lemma compose_invert_l {A} {x y : A} : ∀ (p : x = y), p⁻¹ • p = eq_refl y.
Proof.
intros p; destruct p; reflexivity.
Qed.

Definition compose_invert_r {A} {x y : A} : ∀ (p : x = y), p • p⁻¹ = eq_refl x
  := λ p, match p with eq_refl _ => eq_refl (eq_refl x) end.

Lemma compose_assoc {A} {x y z w : A} :
  ∀ (p : x = y) (q : y = z) (r : z = w),
  p • (q • r) = (p • q) • r.
Proof.
intros p q r; destruct p; reflexivity.
Qed.

Definition hott_2_4_3 {A B x y} (f g : A → B) (H : f ∼ g) (p : x = y)
  : H x • ap g p = ap f p • H y
  := match p with
     | eq_refl _ =>
         match
           match H x as q return (q = q • eq_refl _) with
           | eq_refl _ => eq_refl (eq_refl (f x) • eq_refl (f x))
           end
         with
         | eq_refl _ => eq_refl (id (H x))
         end
     end.

Definition ap_composite {A B C x y}
  : ∀ (f : A → B) (g : B → C) (p : x = y),
    ap g (ap f p) = ap (g ◦◦ f) p
  := λ f g p,
     match p with eq_refl _ => eq_refl (ap g (ap f (eq_refl x))) end.

Definition hott_2_2_2_iv A (x y : A) : ∀ (p : x = y), ap id p = p
  := λ p, match p with eq_refl _ => eq_refl (eq_refl x) end.

Definition isContr A := {a : A & ∀ x : A, a = x }.

Definition transport {A} P {x y : A} (p : x = y) : P x → P y :=
  match p with
  | eq_refl _ => λ x, x
  end.

Definition happly {A B} (f g : Π (x : A), B x)
  : f = g → Π (x : A), f x = g x
  := λ p,
     match p with
     | eq_refl _ => λ y, eq_refl (f y)
     end.

Definition Σ_pr₁ {A B} (x : { y : A & B y }) : A :=
  match x with existT _ a _ => a end.
Definition Σ_pr₂ {A B} (x : { y : A & B y }) : B (Σ_pr₁ x) :=
  match x with existT _ _ b => b end.

Definition pr₁ {A B} := @Σ_pr₁ A B.
Definition pr₂ {A B} := @Σ_pr₂ A B.

Definition isequiv_transport {A B} : ∀ (p : A = B),
  isequiv (transport id p).
Proof.
intros p; destruct p; simpl.
split; exists id; intros x; apply eq_refl.
Defined.

Definition idtoeqv {A B : Type} : A = B → A ≃ B :=
  λ p,
  existT isequiv (transport id p) (isequiv_transport p).

Axiom univ : ∀ A B : Type, isequiv (@idtoeqv A B).

Definition ua {A B} : A ≃ B → A = B :=
  match isequiv_qinv idtoeqv (univ A B) with
  | existT _ f _ => f
  end.

Theorem idtoeqv_ua {A B} : ∀ (f : A ≃ B), idtoeqv (ua f) = f.
Proof.
intros.
unfold ua; simpl.
set (q := isequiv_qinv idtoeqv (univ A B)).
destruct q as (g, (α, β)).
apply α.
Defined.

Tactic Notation "transparent" "assert" "(" ident(H) ":" lconstr(type) ")" :=
  unshelve (refine (let H := (_ : type) in _)).

Definition fib {A B} (f : A → B) (y : B) := Σ (x : A), (f x = y).

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

Theorem hott_4_8_1 A (B : A → Type) (a : A) :
  fib (Σ_pr₁ (B := B)) a ≃ B a.
Proof.
transparent assert (f : fib (Σ_pr₁ (B := B)) a → B a).
 intros p; unfold fib in p.
 destruct p as ((x, p), q), q; apply p.

 exists f; unfold f; clear f; simpl.
 apply qinv_isequiv.
 transparent assert (f : B a → fib (Σ_pr₁ (B := B)) a).
  intros p; unfold fib.
  exists (existT _ a p); apply eq_refl.

  exists f; unfold f; clear f; simpl.
  unfold "∼", id.
  split; [ easy | ].
  intros ((x, p), q); simpl in q.
  destruct q; apply eq_refl.
Defined.

Theorem hott_4_9_2 A B X (e : A ≃ B) : (X → A) ≃ (X → B).
Proof.
unfold "≃".
exists (λ h x, projT1 e (h x)).
apply qinv_isequiv.
exists (λ h x, projT1 (isequiv_qinv _ (projT2 e)) (h x)).
unfold "◦◦", "∼", id; cbn.
split.
-intros f.
 rewrite <- (idtoeqv_ua e).
 destruct (ua e); cbn.
 now unfold id.
-intros f.
 rewrite <- (idtoeqv_ua e).
 now destruct (ua e); cbn.
Defined.

Notation "p '⁎'" := (transport _ p)
  (at level 8, left associativity, format "'[v' p ']' ⁎", only parsing).

Definition Σ_type_pair_eq {A} {P : A → Type} {x y : A} {u : P x} {v : P y} :
  Π (p : x = y), p⁎ u = v → existT _ x u = existT _ y v
:=
  λ p q,
  match p with
  | eq_refl _ =>
      λ (w : P x) (r : transport P (eq_refl x) u = w),
      match r in (_ = t) return (existT P x u = existT P x t) with
      | eq_refl _ => eq_refl (existT P x (transport P (eq_refl x) u))
      end
  end v q.

Theorem pre_hott_4_9_3 A (P : A → Type) (p : Π (x : A), isContr (P x)) :
  (Σ (x : A), P x) ≃ A.
Proof.
exists (λ x, projT1 x).
apply qinv_isequiv; unfold qinv.
exists (λ x, existT _ x (projT1 (p x))).
unfold "◦◦", "∼", id; cbn.
split; [ easy | ].
intros (x, Hx); cbn.
apply eq_existT_uncurried.
exists eq_refl; cbn.
destruct (p x) as (Hx', H); apply H.
Defined.

Theorem hott_4_9_3 A (P : A → Type) (p : Π (x : A), isContr (P x)) :
  (A → Σ (x : A), P x) ≃ (A → A).
Proof.
apply hott_4_9_2.
now apply pre_hott_4_9_3.
Defined.

Definition ishae {A B} f :=
  Σ (g : B → A), Σ (η : g ◦◦ f ∼ id), Σ (ε : f ◦◦ g ∼ id),
    Π (x : A), ap f (η x) = ε (f x).

Definition fib_intro {A B} {f : A → B} {y} x (p : f x = y) :=
  (existT (λ z, f z = y) x p : fib f y).

Lemma hott_2_7_2_f {A} : ∀ P (w w' : Σ (x : A), P x),
  w = w' → Σ (p : pr₁ w = pr₁ w'), p⁎ (pr₂ w) = pr₂ w'.
Proof.
intros P w w' p.
destruct p; simpl.
exists (eq_refl _); apply eq_refl.
Defined.

Lemma hott_2_7_2_g {A} : ∀ P (w w' : Σ (x : A), P x),
  (Σ (p : pr₁ w = pr₁ w'), p⁎ (pr₂ w) = pr₂ w') → w = w'.
Proof.
intros P w w' p.
destruct w as (w₁, w₂).
destruct w' as (w'₁, w'₂); simpl.
simpl in p.
destruct p as (p, q).
destruct p, q; apply eq_refl.
Defined.

Theorem hott_2_7_2 {A} : ∀ (P : A → Type) (w w' : Σ (x : A), P x),
  (w = w') ≃ Σ (p : pr₁ w = pr₁ w'), p⁎ (pr₂ w) = pr₂ w'.
Proof.
intros.
exists (hott_2_7_2_f P w w').
apply qinv_isequiv.
exists (hott_2_7_2_g P w w'); split.
 intros r; unfold id; simpl.
 destruct r as (p, q).
 destruct w as (a, b).
 destruct w' as (a', b').
 simpl in p, q; simpl.
 destruct p, q; simpl.
 unfold hott_2_7_2_f; simpl.
 unfold hott_2_7_2_g; simpl.
 unfold "◦◦"; simpl.
 apply eq_refl.

 intros r; unfold id; simpl.
 destruct r.
 destruct w as (a, b); simpl.
 unfold hott_2_7_2_f; simpl.
 unfold hott_2_7_2_g; simpl.
 unfold "◦◦"; simpl.
 apply eq_refl.
Defined.

Lemma hott_2_1_4_iii A (x y : A) : ∀ (p : x = y), (p⁻¹)⁻¹ = p.
Proof.
intros p; destruct p; reflexivity.
Qed.

Definition Σ_equiv {A} {P Q : A → Type} :
  P ∼ Q → {x : A & P x} ≃ {x : A & Q x}.
Proof.
intros p.
exists
  (λ (q : Σ (x : A), P x),
   existT Q (Σ_pr₁ q)
     match p (Σ_pr₁ q) in (_ = y) return y with
     | eq_refl _ => Σ_pr₂ q
     end).
apply qinv_isequiv.
exists
  (λ (q : Σ (x : A), Q x),
   existT P (Σ_pr₁ q)
     (match p (Σ_pr₁ q) in (_ = y) return y → P (Σ_pr₁ q) with
      | eq_refl _ => id
      end (Σ_pr₂ q))).
unfold "◦◦", "∼", id; simpl.
split; intros (x, q); simpl.
 apply (Σ_type_pair_eq (eq_refl _)).
 simpl; unfold id.
 destruct (p x); apply eq_refl.

 apply (Σ_type_pair_eq (eq_refl _)).
 simpl; unfold id.
 destruct (p x); apply eq_refl.
Defined.

Theorem hott_4_2_5 A B (f : A → B) y x x' (p p' : f _ = y) :
  (fib_intro x p = fib_intro x' p')
  ≃ (Σ (γ : x = x'), ap f γ • p' = p).
Proof.
eapply equiv_compose; [ apply hott_2_7_2 | simpl ].
apply Σ_equiv; intros q.
unfold transport.
destruct q; simpl; unfold id.
apply ua.
exists invert.
apply qinv_isequiv.
exists invert.
unfold "◦◦", "∼", id.
split; intros z; apply hott_2_1_4_iii.
Defined.

Theorem ap_compose {A B} : ∀ (f : A → B) x y z (p : x = y) (q : y = z),
  ap f (p • q) = ap f p • ap f q.
Proof. destruct p, q; constructor. Qed.

Definition hott_4_2_6 A B (f : A → B) : ishae f → ∀ y, isContr (fib f y).
Proof.
intros p y.
destruct p as (g, (η, (ε, q))).
exists (fib_intro (g y) (ε y)).
intros (x, p).
apply (Σ_pr₁ (fst (Σ_pr₂ (hott_4_2_5 A B f y (g y) x (ε y) p)))).
exists (ap g p⁻¹ • η x).
rewrite ap_compose.
destruct p; simpl; unfold id.
eapply compose; [ eapply invert, ru | apply q ].
Defined.

Definition hott_2_4_4 {A x} (f : A → A) (H : f ∼ id) : H (f x) = ap f (H x).
Proof.
intros.
assert (ap f (H x) • H x = H (f x) • H x) as p.
 eapply invert, compose; [ idtac | apply hott_2_4_3 ].
 apply dotl, invert, hott_2_2_2_iv.

 apply dotr with (r := (H x) ⁻¹) in p.
 eapply compose in p; [ idtac | apply compose_assoc ].
 eapply compose in p.
  unfold id in p; simpl in p.
  eapply compose in p; [ idtac | apply hott_2_1_4_i_1 ].
  eapply invert, compose in p; [ idtac | apply compose_assoc ].
  eapply compose in p.
   eapply compose in p; [ eassumption | apply hott_2_1_4_i_1 ].

   eapply dotl, invert.
   eapply compose_invert_r; reflexivity.

  eapply dotl, invert.
  eapply compose_invert_r; reflexivity.
Qed.

Definition alt_τ A B (f : A → B) (g : B → A)
    (ε : f ◦◦ g ∼ id) (η : g ◦◦ f ∼ id)
    (ε' := ((λ b, (ε (f (g b)))⁻¹ • ap f (η (g b)) • ε b) : f ◦◦ g ∼ id)) :
  ∀ a, ap f (η a) = ε' (f a).
Proof.
intros a; simpl in ε'.
assert (p' : η (g (f a)) = ap g (ap f (η a))).
 rewrite (ap_composite f g (η a)).
 apply (hott_2_4_4 (g ◦◦ f) η).

 apply (ap (ap f)) in p'.
 apply (dotr (ε (f a))) in p'.
 pose proof (hott_2_4_3 (f ◦◦ g ◦◦ f) f (λ x, ε (f x)) (η a)) as q.
 unfold id in q; simpl in q; apply invert in q.
 eapply compose in q; [  | eapply compose; [ eapply p' |  ] ].
  unfold ε'.
  rewrite <- compose_assoc.
  unfold id, composite in q; simpl.
  unfold id, composite; simpl.
  rewrite q, compose_assoc, compose_invert_l.
  apply invert, hott_2_1_4_i_2.

  apply dotr.
  eapply compose; [ apply (ap_composite g f (ap f (η a))) |  ].
  apply (ap_composite f (f ◦◦ g) (η a)).
Defined.

Definition hott_4_2_3 A B (f : A → B) : qinv f → ishae f.
Proof.
intros (g, (ε, η)).
unfold ishae.
exists g, η.
pose proof alt_τ A B f g ε η as τ.
set (ε' := (λ b, (ε (f (g b)))⁻¹ • ap f (η (g b)) • ε b) : f ◦◦ g ∼ id) in τ.
simpl in τ.
exists ε'; intros x; apply τ.
Defined.

Definition retraction A B :=
  Σ (r : A → B), Σ (s : B → A), Π (y : B), (r (s y) = y).

Definition hott_3_11_7 A B (r : retraction A B) : isContr A → isContr B.
Proof.
intros p.
destruct r as (r, (s, q)).
destruct p as (a₀, p).
exists (r a₀); intros b₀.
eapply compose; [ | apply (q b₀) ].
apply ap, p.
Defined.

Theorem weak_funext : ∀ {A} (P : A → Type),
  (Π (x : A), isContr (P x)) → isContr (Π (x : A), P x).
Proof.
intros * Hf.
set (H1 := hott_4_8_1 A P).
transparent assert (f : (A → {x : A & P x}) → (A → A)). {
  intros f x.
  apply (projT1 (f x)).
}
clear f.
set (α := hott_4_9_3 A P Hf).
transparent assert (φ : (Π (x : A), P x) → fib (projT1 α) id). {
  intros h.
  exists (λ x, existT _ x (h x)).
  unfold α.
  unfold hott_4_9_3.
  now unfold hott_4_9_2; cbn.
}
transparent assert (ψ : fib (projT1 α) id → (Π (x : A), P x)). {
  intros (g', p) x.
  apply ((happly _ _ p x) ⁎ (pr₂ (g' x))).
}
assert (Hsr : ψ ◦◦ φ = id) by easy.
assert (H : retraction (fib (projT1 α) id) (Π (x : A), P x)). {
  unfold retraction.
  exists ψ, φ.
  intros z.
  replace z with (id z) by easy.
  now rewrite <- Hsr.
}
eapply hott_3_11_7; [ apply H | ].
apply hott_4_2_6.
apply hott_4_2_3.
apply (isequiv_qinv _ (projT2 α)).
Qed.

Check @weak_funext.
Print Assumptions weak_funext.

Theorem funext {A B} :∀ f g : ∀ (x : A), B x,
  (∀ x : A, f x = g x) → f = g.
Proof.
intros  * Hfg.
Check @weak_funext.
...
