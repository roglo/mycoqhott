(* HoTT stuff required for categories *)
(* Borrowed from the other files over HoTT *)

Set Universe Polymorphism.
Require Import Utf8.

Definition isSet (A : Type) := ∀ (a b : A) (p q : a = b), p = q.

(*
Definition mid {A} (x : A) := x.
*)
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

(* proving nat and list are hSets *)

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

Theorem equiv_eq_nat_code : ∀ m n, equivalence (m = n) (nat_code m n).
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
pose proof equiv_eq_nat_code m n as r.
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
  | (a :: la, b :: lb) => ((a = b) * list_code la lb)
  end.

Fixpoint list_r {A} (l : list A) : list_code l l :=
  match l with
  | [] => I
  | a :: l => (eq_refl, list_r l)
  end.

Definition list_encode {A} (la lb : list A) :
    la = lb → list_code la lb :=
  λ p, transport (list_code la) p (list_r la).

Definition list_decode {A} (la lb : list A) :
  list_code la lb → la = lb.
Proof.
revert la lb.
fix IHn 1.
intros la lb lc.
destruct la as [| a la]; [ now destruct lb | ].
destruct lb as [| b lb]; [ easy | ].
destruct lc as (p, lc).
destruct p.
specialize (IHn la lb lc) as H1.
now destruct H1.
Defined.

Theorem list_decode_encode {A} {la lb : list A} :
  ∀ lc, list_decode la lb (list_encode la lb lc) = lc.
Proof.
intros lc.
destruct lc; simpl; unfold id; simpl.
induction la; [ reflexivity | simpl ].
now rewrite IHla.
Defined.

Theorem list_encode_decode {A} {la lb : list A} :
  ∀ lc, list_encode la lb (list_decode la lb lc) = lc.
Proof.
intros.
revert lb lc.
induction la as [| a la]; intros. {
  destruct lb; [ now destruct lc | easy ].
}
destruct lb as [| b lb]; [ easy | ].
cbn in lc.
destruct lc as (p, lc).
destruct p.
specialize (IHla lb lc) as H1; simpl.
remember (list_decode la lb lc) as d eqn:Hd.
destruct d; cbn.
rewrite <- H1.
now unfold id.
Defined.

Theorem equiv_eq_list_code {A} : ∀ la lb : list A,
  equivalence (la = lb) (list_code la lb).
Proof.
intros.
exists (list_encode la lb); apply qinv_isequiv.
exists (list_decode la lb).
unfold composite, homotopy, id; simpl.
split; intros p; [ apply list_encode_decode | apply list_decode_encode ].
Defined.

Tactic Notation "transparent" "assert" "(" ident(H) ":" lconstr(type) ")" :=
  unshelve (refine (let H := (_ : type) in _)).

Definition list_code_equiv_1_or_0 {A}
    (eq_dec : ∀ a b : A, {a = b} + {a ≠ b}) :
  isSet A → ∀ (la lb : list A),
  equivalence (list_code la lb) True + equivalence (list_code la lb) False.
Proof.
intros HA *.
revert lb.
induction la as [| a la]; intros. {
  destruct lb as [| b lb]. {
    left; cbn.
    unfold equivalence, isequiv, homotopy, composite, id.
    exists id; unfold id.
    now split; exists id; unfold id.
  }
  right; cbn.
  unfold equivalence, isequiv, homotopy, composite, id.
  exists id; unfold id.
  now split; exists id; unfold id.
}
destruct lb as [| b lb]. {
  right; cbn.
  unfold equivalence, isequiv, homotopy, composite, id.
  exists id; unfold id.
  now split; exists id; unfold id.
}
cbn.
specialize (IHla lb) as H1.
unfold equivalence in H1 |-*.
destruct (eq_dec a b) as [p| p]. 2: {
  right.
  exists (λ X, match p (fst X) with end).
  apply qinv_isequiv.
  exists (λ H : False, match H with end).
  unfold homotopy, composite, id.
  split; [ now intros | ].
  now intros (q, Hq).
}
destruct H1 as [H1| H1].
-left.
 transparent assert (f : (a = b) * list_code la lb → True). {
   intros (q, Hq).
   apply (projT1 H1), Hq.
 }
 exists f; subst f; cbn.
 apply qinv_isequiv.
 unfold qinv.
 specialize (projT2 H1) as H2; cbn in H2.
 apply isequiv_qinv in H2; unfold qinv in H2.
 unfold homotopy, composite, id in H2.
 destruct H2 as (g & Hg1 & Hg2).
 transparent assert (g' : True → (a = b) * list_code la lb). {
   intros H.
   split; [ apply p | apply g, H ].
 }
 exists g'; subst g'.
 unfold homotopy, composite, id; cbn.
 split. {
   intros H.
   now destruct (projT1 H1 (g H)), H.
 }
 intros (i, Hi).
 move i before p.
 destruct (HA _ _ p i).
 apply f_equal, Hg2.
-right.
 transparent assert (f : (a = b) * list_code la lb → False). {
   intros (q, Hq).
   apply (projT1 H1), Hq.
 }
 exists f; subst f; cbn.
 apply qinv_isequiv.
 unfold qinv.
 specialize (projT2 H1) as H2; cbn in H2.
 apply isequiv_qinv in H2; unfold qinv in H2.
 unfold homotopy, composite, id in H2.
 destruct H2 as (g & Hg1 & Hg2).
 transparent assert (g' : False → (a = b) * list_code la lb). {
   now intros H.
 }
 exists g'; subst g'.
 unfold homotopy, composite, id; cbn.
 split; [ now intros H | ].
 intros (i, Hi).
 destruct (projT1 H1 Hi).
Defined.

Definition isSet_list {A} : (∀ a b : A, {a = b} + {a ≠ b}) →
  isSet A → isSet (list A).
Proof.
intros eq_dec HA la lb p q.
specialize (equiv_eq_list_code la lb) as r.
specialize (list_code_equiv_1_or_0 eq_dec HA la lb) as s.
destruct s as [s| s].
-eapply equiv_compose in s; [ | apply r ].
 destruct s as (f, ((g, Hg), (h, Hh))).
 unfold composite, homotopy, id in Hg, Hh.
 pose proof Hh p as Hp.
 pose proof Hh q as Hq.
 destruct (f p), (f q).
 subst p q; reflexivity.
-eapply equiv_compose in s; [ | apply r ].
 destruct s as (f, ((g, Hg), (h, Hh))).
 exfalso; apply f, p.
Defined.
