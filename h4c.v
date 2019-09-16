(* HoTT stuff required for categories *)
(* Borrowed from the other files over HoTT *)

Set Universe Polymorphism.
Set Nested Proofs Allowed.

Require Import Utf8.

Definition isSet (A : Type) := ∀ (a b : A) (p q : a = b), p = q.

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

Definition qinv_isequiv {A B} (f : A → B) : qinv f → isequiv f.
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

Definition lu {A} {b c : A} (r : b = c) : r = eq_refl b • r :=
  hott_2_1_4_i_2 r.

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

Theorem hott_2_11_1 {A B} : ∀ (f : A → B), isequiv f → ∀ (a a' : A),
  (a = a') ≃ (f a = f a').
Proof.
intros f Hf a a'.
exists (@ap A B a a' f).
apply isequiv_qinv in Hf.
destruct Hf as (f₁, (α, β)).
apply qinv_isequiv.
unfold qinv.
set (g := λ r, (β a)⁻¹ • ap f₁ r • β a').
unfold "◦◦", id in g; simpl in g.
exists g; subst g.
unfold "◦◦", "∼", id; simpl.
split; intros q.
-set (r := @compose _ _ _ a' (@invert _ (f₁ (f a)) a (β a) • ap f₁ q) (β a')).
 apply (@compose _ _ ((α (f a))⁻¹ • α (f a) • ap f r)).
 +eapply compose; [ apply lu | idtac ].
  apply dotr, invert, compose_invert_l.
 +eapply compose; [ eapply invert, compose_assoc | idtac ].
  unfold id, composite; simpl.
  pose proof (hott_2_4_3 ((f ◦◦ f₁) ◦◦ f) f (λ a, α (f a)) r) as H.
  unfold "◦◦" in H; simpl in H.
  eapply compose; [ eapply dotl, H | simpl ].
  apply (@compose _ _ ((α (f a))⁻¹ • (ap f (ap f₁ (ap f r)) • α (f a')))).
  *apply dotl, dotr.
   apply (@compose _ _ (ap (f ◦◦ f₁ ◦◦ f) r)); [ reflexivity | idtac ].
   eapply invert, compose; [ idtac | eapply ap_composite ].
   eapply compose; [ apply (ap_composite f₁ f (ap f r)) | reflexivity ].
  *eapply compose; [ apply compose_assoc | idtac ].
   rewrite (ap_composite f f₁ r).
   apply (@compose _ _ ((α (f a))⁻¹ • ap f (β a • r • (β a')⁻¹) • α (f a'))).
  --apply dotr, dotl, ap.
    rewrite r; simpl.
    rewrite <- ru, compose_invert_r.
    reflexivity.
  --apply (@compose _ _ ((α (f a))⁻¹ • ap f (ap f₁ q) • α (f a'))).
   **apply dotr, dotl, ap; subst r.
     do 2 rewrite compose_assoc.
     rewrite compose_invert_r; simpl.
     unfold id; simpl.
     rewrite <- compose_assoc.
     rewrite compose_invert_r; simpl.
     rewrite <- ru; reflexivity.
   **assert (H1 : α (f a) • q = ap (f ◦◦ f₁) q • α (f a')). {
       rewrite <- (hott_2_4_3 (f ◦◦ f₁) id α q).
       apply dotl, invert, hott_2_2_2_iv.
     }
     unfold id, composite; simpl.
     pose proof (@ap_composite B A B (f a) (f a') f₁ f q) as H2.
     rewrite H2.
     rewrite <- compose_assoc.
     unfold id, composite in H1; simpl in H1.
     unfold composite; simpl.
     rewrite <- H1.
     rewrite compose_assoc, compose_invert_l.
     reflexivity.
-rewrite (ap_composite f f₁ q).
 destruct q; simpl.
 unfold "◦◦", "∼", id in β; simpl in β.
 unfold "◦◦"; simpl; rewrite β; reflexivity.
Defined.

Definition quasi_inv {A B} : A ≃ B → B ≃ A :=
  λ eqf,
  match eqf with
  | existT _ f (existT _ g Hg, existT _ h Hh) =>
      existT isequiv g
        (existT _ f (λ x, (Hh (g (f x)))⁻¹ • ap h (Hg (f x)) • Hh x),
         existT _ f Hg)
 end.

(**)

Definition isProp (A : Type) := ∀ (x y : A), x = y.

Definition isContr A := {a : A & ∀ x : A, a = x }.

Fixpoint isnType A n :=
  match n with
  | 0 => isProp A
  | S p' => ∀ x y : A, isnType (x = y) p'
  end.

Theorem compose_cancel_l {A} {x y z : A} (p : x = y) (q r : y = z) :
  compose p q = compose p r → q = r.
Proof. intros; now destruct p. Qed.

Theorem compose_eq_refl : ∀ A (x : A) (p : x = x), compose p eq_refl = p.
Proof. now intros; destruct p. Qed.

Theorem isContr_isProp {A} : isContr A → isProp A.
Proof.
intros f x y.
destruct f as (a & Ha).
apply @compose with (y := a); [ now destruct (Ha x) | now apply Ha ].
Qed.

Theorem isProp_isSet {A} : isProp A → isSet A.
Proof.
intros f x y p q.
apply (compose_cancel_l (f x x)).
apply @compose with (y := f x y); [ now destruct p, (f x x) | ].
now destruct p, q, (f x x).
Qed.

Theorem isnType_isSnType {A} n : isnType A n → isnType A (S n).
Proof.
intros * f.
revert A f.
induction n; intros; [ intros x y p q; now apply isProp_isSet | ].
intros p q.
apply IHn, f.
Qed.

Definition transport {A} P {x y : A} (p : x = y) : P x → P y :=
  match p with
  | eq_refl _ => λ x, x
  end.

Theorem equiv_eq : ∀ A B (f : A → B) (g : B → A) x y,
  (∀ b, f (g b) = b) → g x = g y → x = y.
Proof.
intros * Hfg H.
apply @compose with (y := f (g y)); [ | apply Hfg ].
destruct H; symmetry; apply Hfg.
Defined.

Lemma isnType_if_equiv : ∀ A B n, A ≃ B → isnType A n → isnType B n.
Proof.
intros * HAB HA.
revert A B HAB HA.
induction n; intros. {
  destruct HAB as (f, Hf).
  destruct Hf as ((g, Hfg), (h, Hhf)).
  move h before g.
  unfold id, "◦◦", "∼" in Hfg, Hhf.
  cbn in HA |-*.
  unfold isProp in HA |-*.
  intros x y.
  rewrite <- Hfg; symmetry.
  rewrite <- Hfg; symmetry.
  f_equal.
  apply HA.
}
destruct HAB as (f, Hf).
destruct Hf as ((g, Hfg), (h, Hhf)).
cbn in HA |-*.
move h before g.
unfold id, "◦◦", "∼" in Hfg, Hhf.
intros x y.
apply (IHn (g x = g y) (x = y)); [ | apply HA ].
apply quasi_inv.
apply hott_2_11_1.
split.
-exists f.
 unfold "◦◦", "∼", id.
 intros z.
 rewrite <- Hhf.
 clear - Hfg Hhf.
 f_equal. (* bizarre que ça marche *)
-exists f.
 unfold "◦◦", "∼", id.
 apply Hfg.
Qed.

Theorem pair_transport_eq_existT {A} {P : A → Type} :
  ∀ a b (Ha : P a) (Hb : P b),
  {p : a = b & transport P p Ha = Hb} → existT P a Ha = existT P b Hb.
Proof.
intros * (p, Hp).
now destruct p, Hp.
Defined.

Theorem eq_existT_pair_transport {A} {P : A → Type} :
  ∀ a b (Ha : P a) (Hb : P b),
  existT P a Ha = existT P b Hb → {p : a = b & transport P p Ha = Hb}.
Proof.
intros * Hee.
inversion_sigma.
destruct Hee0.
now exists eq_refl.
Defined.

Theorem pair_transport_equiv_eq_existT {A : Type} : ∀ (P : A → Type),
  (∀ x, isProp (P x))
  → ∀ a b (Ha : P a) (Hb : P b),
  {p : a = b & transport P p Ha = Hb} ≃ (existT P a Ha = existT P b Hb).
Proof.
intros.
unfold "≃".
exists (pair_transport_eq_existT a b Ha Hb).
split. {
  exists (eq_existT_pair_transport a b Ha Hb).
  unfold "◦◦", "∼", id.
  intros p.
  inversion_sigma.
  destruct p0.
  cbn in p1; cbn.
  now destruct p1.
}
exists (eq_existT_pair_transport a b Ha Hb).
unfold "◦◦", "∼", id.
intros (p, Hp).
now destruct p, Hp.
Qed.

Theorem transport_pair : ∀ A B C (x y : A) (p : x = y) b c,
  transport (λ z, (B z * C z)%type) p (b, c) =
  (transport B p b, transport C p c).
Proof.
intros.
destruct p; reflexivity.
Qed.

Theorem isnType_isnType_sigT (A : Type) : ∀ n P,
  (∀ x, isProp (P x)) → isnType A n → isnType (@sigT A P) n.
Proof.
intros * HP Hn.
revert A P HP Hn.
induction n; intros. {
  cbn in Hn; cbn.
  unfold isProp in Hn |-*.
  intros H1 H2.
  destruct H1 as (a & Ha).
  destruct H2 as (b & Hb).
  move b before a.
  apply eq_existT_uncurried.
  assert (p : a = b) by apply Hn.
  exists p.
  apply HP.
}
intros Ha Hb.
destruct Ha as (a, Ha).
destruct Hb as (b, Hb).
move b before a.
specialize (IHn (a = b)) as H4.
remember (λ p : a = b, transport P p Ha = Hb) as Q.
specialize (H4 Q).
assert (H : ∀ p : a = b, isProp (Q p)). {
  intros p.
  subst Q.
  destruct p.
  cbn.
  specialize (HP a) as H1.
  specialize (isProp_isSet H1 Ha Hb) as H2.
  intros r s.
  apply H2.
}
specialize (H4 H); clear H.
cbn in Hn.
specialize (H4 (Hn a b)).
subst Q.
eapply isnType_if_equiv; [ | apply H4 ].
now apply pair_transport_equiv_eq_existT.
Qed.

Theorem isSet_isSet_sigT {A} {P : A → Type} :
  (∀ x, isProp (P x)) → isSet A → isSet (@sigT A P).
Proof.
intros * HP HS.
now apply (isnType_isnType_sigT A 1 P).
Qed.

Theorem isProp_isProp_sigT {A} {P : A → Type} :
  (∀ x, isProp (P x)) → isProp A → isProp (@sigT A P).
Proof.
intros * HP HS.
now apply (isnType_isnType_sigT A 0 P).
Qed.

Definition happly {A B} (f g : Π (x : A), B x)
  : f = g → Π (x : A), f x = g x
  := λ p,
     match p with
     | eq_refl _ => λ y, eq_refl (f y)
     end.

Axiom extensionality : ∀ {A B} f g, isequiv (@happly A B f g).

Definition funext {A B} {f g : Π (x : A), B x}
  : (∀ x : A, f x = g x) → f = g
  := λ p,
     match isequiv_qinv (happly f g) (extensionality f g) with
     | existT _ h _ => h p
     end.

Theorem funext_prop_uniq_princ {A B} : ∀ (f g : Π (x : A), B x) (p : f = g),
  p = funext (happly f g p).
Proof.
intros.
unfold funext; simpl.
set (q := isequiv_qinv (happly f g) (extensionality f g)).
destruct q as (k, (α, β)).
apply invert, β.
Defined.

Theorem hott_2_6_1 {A B} : ∀ x y : A * B,
  (x = y) → (fst x = fst y) * (snd x = snd y).
Proof.
intros x y p.
split; destruct p; reflexivity.
Defined.

Theorem pair_eq {A B} {x y : A * B} :
  (fst x = fst y) * (snd x = snd y) → (x = y).
Proof.
intros p.
destruct x as (a, b).
destruct y as (a', b').
simpl in p.
destruct p as (p, q).
destruct p, q; reflexivity.
Defined.

Theorem hott_2_6_2 {A B : Type} : ∀ x y : (A * B)%type,
  ((fst x = fst y) * (snd x = snd y))%type ≃ (x = y).
Proof.
intros.
set (f := hott_2_6_1 x y).
set (g := @pair_eq A B x y).
apply quasi_inv.
unfold "≃".
apply existT with (x := f).
apply qinv_isequiv.
exists g; split.
 intros r; unfold id; simpl.
 destruct r as (p, q).
 destruct x as (a, b).
 destruct y as (a', b').
 simpl in p, q, f, g.
 destruct p, q; reflexivity.

 intros p; unfold id; simpl.
 destruct p, x; reflexivity.
Qed.

Definition isSet_pair {A B} : isSet A → isSet B → isSet (A * B).
Proof.
intros r s x y p q.
pose proof hott_2_6_2 x y as e.
destruct x as (xa, xb).
destruct y as (ya, yb); simpl in e.
apply quasi_inv in e.
destruct e as (f, ((g, Hg), (h, Hh))).
unfold "◦◦", "∼", id in Hg, Hh.
pose proof Hh p as Hhp.
pose proof Hh q as Hhq.
destruct (f p) as (fpa, fpb).
destruct (f q) as (fqa, fqb).
pose proof r xa ya fpa fqa as Hra.
pose proof s xb yb fpb fqb as Hrb.
destruct Hra, Hrb.
unfold id in Hhp, Hhq.
destruct Hhp; assumption.
Defined.

Definition isSet_forall A B :
  (Π (a : A), isSet (B a)) → isSet (Π (a : A), B a).
Proof.
intros r f g p q.
unfold isSet in r.
pose proof funext_prop_uniq_princ f g p as Hp.
pose proof funext_prop_uniq_princ f g q as Hq.
assert (∀ x : A, happly _ _ p x = happly _ _ q x) as Hx by (intros; apply r).
apply funext in Hx.
rewrite Hp, Hq, Hx.
reflexivity.
Defined.

Notation "⊥" := False.

Definition Σ_pr₁ {A B} (x : { y : A & B y }) : A :=
  match x with existT _ a _ => a end.
Definition Σ_pr₂ {A B} (x : { y : A & B y }) : B (Σ_pr₁ x) :=
  match x with existT _ _ b => b end.

Module Σ_type.

Definition pr₁ {A B} := @Σ_pr₁ A B.
Definition pr₂ {A B} := @Σ_pr₂ A B.

End Σ_type.

(* "3.7 Propositional truncation" *)

Axiom PT : Type → Type.
Arguments PT _%type.
Notation "∥ A ∥" := (PT A) (A at level 0, format "∥ A ∥") : type_scope.

Axiom PT_intro : ∀ A, A → ∥A∥.
Arguments PT_intro [A] x.
Notation "╎ A ╎" := (PT_intro A) (A at level 0, format "╎ A ╎") : type_scope.

Axiom PT_eq : ∀ A, isProp ∥A∥.
(* Arguments PT_eq [A] x y. *)

(* "If B is a mere proposition and we have f : A → B, then there is an
    induced g : ∥A∥ → B such that g(|a|) ≡ f(a) for all a : A." *)

Axiom PT_rec : ∀ A B (f : A → B), isProp B →
  Σ (g : ∥A∥ → B), ∀ a, g (PT_intro a) = f a.

Definition PT_elim {A} : isProp A → ∥A∥ → A :=
  λ PA, Σ_type.pr₁ (PT_rec A A id PA).
Definition PT_intro_not {A} : notT A → notT ∥A∥ :=
  λ f, Σ_type.pr₁ (PT_rec A ⊥ f (λ x y : ⊥, match x with end)).

Theorem isSet_True : isSet True.
Proof.
apply isProp_isSet.
now intros x y; destruct x, y.
Qed.

Theorem isSet_False : isSet False.
Proof.
apply isProp_isSet.
now intros x y; destruct x, y.
Qed.

(* univalence *)

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

Theorem univalence : ∀ A B : Type, (A ≃ B) ≃ (A = B).
Proof.
intros.
pose proof (@univ A B) as p.
apply quasi_inv.
esplit; eassumption.
Defined.

Definition ua {A B} : A ≃ B → A = B :=
  match isequiv_qinv idtoeqv (univ A B) with
  | existT _ f _ => f
  end.

Definition eqv_refl A : A ≃ A.
Proof.
exists id; apply qinv_isequiv; exists  id.
split; intros a; apply eq_refl.
Defined.

Definition idtoeqv_ua {A B} : ∀ (f : A ≃ B), idtoeqv (ua f) = f.
Proof.
intros.
unfold ua; simpl.
set (q := isequiv_qinv idtoeqv (univ A B)).
destruct q as (g, (α, β)).
apply α.
Defined.

Definition ua_idtoeqv {A B} : ∀ (p : A = B), ua (idtoeqv p) = p.
Proof.
intros.
unfold ua; simpl.
set (q := isequiv_qinv idtoeqv (univ A B)).
destruct q as (f, (α, β)).
apply β.
Defined.

(* j'aimerais bien démontrer que l'univalence implique l'extensionnalité
   mais je n'ai jamais, dans hott, compris la preuve ; j'ai bien vu qu'on
   y parlait de l'extensionnalité faible, mais bon, c'est tout *)

Tactic Notation "transparent" "assert" "(" ident(H) ":" lconstr(type) ")" :=
  unshelve (refine (let H := (_ : type) in _)).

Notation "'Σ' ( x : A ) , B" :=
  ({ x : A & B }) (at level 0, x at level 0, B at level 100, only parsing).
Notation "'Π' ( x : A ) , B" :=
  (∀ x : A, B) (at level 0, x at level 0, B at level 100, only parsing).
(*
Definition isContr A := Σ (a : A), Π (x : A), a = x.
*)

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

Definition ex_2_10 {A B C} :
  (Σ (x : A), Σ (y : B x), C (existT _ x y)) ≃ (Σ (p : Σ (x : A), B x), C p).
Proof.
exists
  (λ xyf,
   match xyf with
   | existT _ x (existT _ y f) => existT C (existT B x y) f
   end).
apply qinv_isequiv.
exists
  (λ xyf : {p : {x : A & B x} & C p},
   match xyf with
   | existT _ (existT _ x y) f =>
       (λ f : C (existT B x y), existT _ x (existT _ y f)) f
   end).
unfold "◦◦", "∼", id; simpl.
split; [ intros ((x, y), f) | intros (x, (y, f)) ]; reflexivity.
Defined.

Definition hott_4_8_1 A (B : A → Type) (a : A) :
  fib (Σ_pr₁ (B := B)) a ≃ B a.
Proof.
(* their proof... *)
assert (p : fib (Σ_pr₁ (B := B)) a ≃ Σ (x : A), Σ (b : B x), x = a).
 eapply equiv_compose; [ eapply quasi_inv, ex_2_10 | apply eqv_refl ].

 eapply equiv_compose; [ apply p | clear p ].
 assert (p : (Σ (x : A), Σ (b : B x), x = a) ≃ Σ (x : A), Σ (p : x = a), B x).
  exists
    (λ w, existT _ (Σ_pr₁ w) (existT _ (Σ_pr₂ (Σ_pr₂ w)) (Σ_pr₁ (Σ_pr₂ w)))).
  apply qinv_isequiv.
  exists
    (λ w, existT _ (Σ_pr₁ w) (existT _ (Σ_pr₂ (Σ_pr₂ w)) (Σ_pr₁ (Σ_pr₂ w)))).
  unfold "◦◦", "∼", id; simpl.
  split; intros (x, (p, q)); apply eq_refl.

  eapply equiv_compose; [ apply p | clear p ].
  transparent assert (f : (Σ (x : A), Σ (_ : x = a), B x) → B a).
   intros (x, (p, q)); destruct p; apply q.

   exists f; unfold f; clear f; simpl.
   apply qinv_isequiv.
   transparent assert (f : B a → (Σ (x : A), Σ (_ : x = a), B x)).
    intros p; apply (existT _ a (existT _ (eq_refl _) p)).

    exists f; unfold f; clear f; simpl.
    unfold "◦◦", "∼", id; simpl.
    split; [ easy | ].
    intros (x, (p, q)); destruct p; apply eq_refl.
(*
(* my proof, shorter... *)
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
*)
Defined.

Definition ua_pup {A B}
  : ∀ (p : A = B),
    p = ua (existT isequiv (transport id p) (isequiv_transport p))
  := λ (p : A = B),
     match p return
       (ua (idtoeqv p) = p
        → p = ua (existT isequiv (transport id p) (isequiv_transport p)))
     with
     | eq_refl _ =>
         λ q,
         match q in (_ = r) return (r = ua (eqv_refl A)) with
         | eq_refl _ => eq_refl _
         end
     end (ua_idtoeqv p).

Definition weak_funext A P :=
  (Π (x : A), isContr (P x)) → isContr (Π (x : A), P x).
Definition weak_funext1 A P :=
  (∀ x : A, {a : P x & ∀ y : P x, a = y}) → {a : ∀ x : A, P x & ∀ y : ∀ x : A, P x, a = y}.

Theorem hott_4_9_2_tac A B X (e : A ≃ B) : (X → A) ≃ (X → B).
Proof.
(**)
unfold "≃".
exists (λ h x, projT1 e (transport (λ _, X → A) (ua e)⁻¹ h x)).
apply qinv_isequiv.
transparent assert (g : (X → B) → X → A). {
  intros h x.
  apply (projT1 (isequiv_qinv _ (projT2 e))).
  apply (transport _ (ua e) h x).
}
exists g; subst g; cbn.
split.
-unfold "◦◦", "∼", id; cbn.
 intros f; cbn.
 destruct e; cbn.
...
remember (ua e) as p eqn:s.
set (t := (idtoeqv_ua e)⁻¹ : e = idtoeqv (ua e)); simpl in t.
rewrite <- s in t.
destruct p.
apply eqv_refl.
Defined.

Definition hott_4_9_2 A B X (e : A ≃ B) : (X → A) ≃ (X → B) :=
  let p : A = B := ua e in
  match
    p in (_ = y)
    return (∀ e1 : A ≃ y, p = ua e1 → e1 = idtoeqv p → (X → A) ≃ (X → y))
  with
  | eq_refl =>
      λ (e0 : A ≃ A) (_ : eq_refl = ua e0) (_ : e0 = idtoeqv eq_refl),
        eqv_refl (X → A)
  end e eq_refl
  (eq_ind_r (λ e0 : A = B, e = idtoeqv e0) (idtoeqv_ua e)⁻¹ eq_refl).

Definition old_hott_4_9_2 A B X (e : A ≃ B) : (X → A) ≃ (X → B) :=
  idtoeqv
    match ua e in (_ = y) return ((X → A) = (X → y)) with
    | eq_refl => eq_refl
    end.

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

Definition isContr_sigma_if A P :
  isContr A → (∀ x, isContr (P x)) → isContr (Σ (x : A), P x).
Proof.
intros p q.
unfold isContr.
destruct p as (a, p).
exists (existT _ a (Σ_pr₁ (q a))); intros (x, r).
apply (Σ_type_pair_eq (p x)).
destruct (p x); simpl.
destruct (q a) as (s, t); apply t.
Defined.

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

Definition pr₁ {A B} := @Σ_pr₁ A B.
Definition pr₂ {A B} := @Σ_pr₂ A B.

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

Definition hott_4_2_5 A B (f : A → B) y x x' (p p' : f _ = y) :
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

Definition isContr_fib_4_9_3 A (P : A → Type) (p : Π (x : A), isContr (P x)) :
  isContr (fib (Σ_pr₁ (hott_4_9_3 A P p)) id).
Proof.
apply hott_4_2_6.
apply hott_4_2_3.
set (q := hott_4_9_3 A P p).
destruct q as (f, q).
apply isequiv_qinv, q.
Defined.

Definition hott_3_11_3_i_ii A : isContr A → isProp A * Σ (a : A), True.
Proof.
intros p.
split; [ apply isContr_isProp; assumption | ].
destruct p as (a, p).
exists a; constructor.
Defined.

Definition hott_3_3_2 P : isProp P → ∀ x₀ : P, P ≃ True
:=
  λ (HP : isProp P) (x₀ : P),
  existT isequiv (λ _, I)
    (qinv_isequiv (λ _, I)
       (existT _ (λ _, x₀)
          (λ x, match x with I => eq_refl (id I) end,  λ x, HP _ x))).

Definition hott_3_11_3_ii_iii A : isProp A * (Σ (a : A), True) → A ≃ True.
Proof.
intros (p, (a, _)).
apply hott_3_3_2; assumption.
Defined.

Definition quasi_inv_l_eq_r {A B} (f : A → B) (g h : B → A) :
  f ◦◦ g ∼ id
  → h ◦◦ f ∼ id
  → g ∼ h
:=
  λ Hfg Hhf x, (Hhf (g x))⁻¹ • ap h (Hfg x).

Definition EqStr_equiv_fun {A B} : A ≃ B
  → Σ (f : A → B), Σ (g : B → A), (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y).
Proof.
intros p.
destruct p as (f, ((g, Hg), (h, Hh))).
exists f, g.
split; [ intros x | intros y; apply Hg ].
pose proof quasi_inv_l_eq_r f g h Hg Hh as p.
unfold "∼" in p.
etransitivity; [ apply p | apply Hh ].
Defined.

Definition hott_3_11_3_iii_i A : A ≃ True → isContr A.
Proof.
intros p.
apply EqStr_equiv_fun in p.
destruct p as (f, (g, (Hg, Hh))).
exists (g I); intros x.
etransitivity; [ | apply Hg ].
destruct (f x); reflexivity.
Defined.

Definition equiv_contr {A B} : A ≃ B → isContr A → isContr B.
Proof.
intros p q.
apply hott_3_11_3_i_ii, hott_3_11_3_ii_iii in q.
apply quasi_inv in p.
eapply equiv_compose in q; [ | apply p ].
apply hott_3_11_3_iii_i; assumption.
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

(*
(* https://stackoverflow.com/questions/48161372/case-analysis-on-evidence-of-equality-type-in-coq *)
Lemma true_num : ∀ m :nat, ∀ x y : m=m, x=y.
Proof.
intros.
destruct x.
*)

Theorem weak_funext_th : ∀ {A} (P : A → Type),
  (Π (x : A), isContr (P x)) → isContr (Π (x : A), P x).
Proof.
intros * Hf.
set (H1 := hott_4_8_1 A P).
(*
transparent assert (H2 : (Σ (x : A), P x) ≃ A). {
  exists (λ x, projT1 x).
  apply qinv_isequiv; unfold qinv.
  exists (λ x, existT _ x (projT1 (Hf x))).
  unfold "◦◦", "∼", id; cbn.
  split; [ easy | ].
  intros (x, Hx); cbn.
  apply eq_existT_uncurried.
  exists eq_refl; cbn.
  destruct (Hf x) as (Hx', H); apply H.
}
*)
transparent assert (f : (A → {x : A & P x}) → (A → A)). {
  intros f x.
  apply (projT1 (f x)).
}
(*
set (α := hott_4_9_3 A P Hf).
transparent assert (φ : (Π (x : A), P x) → fib (projT1 α) id). {
  intros h.
  exists (λ x, existT _ x (h x)).
  unfold α.
  unfold hott_4_9_3.
  unfold hott_4_9_2; cbn.
Check (pre_hott_4_9_3 A P Hf).
...
}
*)
transparent assert (y : fib f id). {
  unfold fib.
  now exists (λ x, existT _ x (projT1 (Hf x))).
}
transparent assert (φ : (Π (x : A), P x) → fib f id). {
  intros h.
  now exists (λ x, existT _ x (h x)).
}
transparent assert (ψ : fib f id → (Π (x : A), P x)). {
  intros (g', p) x.
  apply ((happly _ _ p x) ⁎ (pr₂ (g' x))).
}
assert (Hsr : ψ ◦◦ φ = id) by easy.
assert (H : retraction (fib f id) (Π (x : A), P x)). {
  unfold retraction.
  exists ψ, φ.
  intros z.
  replace z with (id z) by easy.
  now rewrite <- Hsr.
}
eapply hott_3_11_7; [ apply H | ].
apply hott_4_2_6.
apply hott_4_2_3.
unfold qinv.
transparent assert (g : (A → A) → A → {x : A & P x}). {
  intros g x.
  apply (existT _ (g x) (projT1 (Hf (g x)))).
}
exists g; cbn.
split; [ easy | ].
unfold "◦◦", "∼", id; cbn.
intros h.
subst f g.
cbn; cbn in y.
Abort. (* j'y arrive pas
...
apply extensionality; intros x.
destruct (h x).
cbn.
apply eq_existT_uncurried.
exists eq_refl.
cbn.
specialize (Hf x0) as H2.
unfold isContr in H2.
destruct H2 as (q & H2).
specialize (H2 p) as H3.
specialize (H2 (projT1 (Hf x0))) as H4.
now destruct H3, H4.
Defined.

Print Assumptions weak_funext_th.
...
*)
