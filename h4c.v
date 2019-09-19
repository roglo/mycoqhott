(* HoTT stuff required for categories *)
(* Borrowed from the other files over HoTT *)

Set Universe Polymorphism.
Set Nested Proofs Allowed.

Require Import Utf8.
Require Import funext.

Definition isSet (A : Type) := ∀ (a b : A) (p q : a = b), p = q.
Definition isProp (A : Type) := ∀ (x y : A), x = y.

Definition lu {A} {b c : A} (r : b = c) : r = eq_refl b • r :=
  hott_2_1_4_i_2 r.

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

Fixpoint isnType A n :=
  match n with
  | 0 => isProp A
  | S p' => ∀ x y : A, isnType (x = y) p'
  end.

Theorem compose_cancel_l {A} {x y z : A} (p : x = y) (q r : y = z) :
  compose p q = compose p r → q = r.
Proof. intros; now destruct p. Qed.

(*
Theorem compose_eq_refl : ∀ A (x : A) (p : x = x), compose p eq_refl = p.
Proof. now intros; destruct p. Qed.

Theorem isContr_isProp {A} : isContr A → isProp A.
Proof.
intros f x y.
destruct f as (a & Ha).
apply @compose with (y := a); [ now destruct (Ha x) | now apply Ha ].
Qed.
*)

Theorem isProp_isSet {A} : isProp A → isSet A.
Proof.
intros f x y p q.
apply (compose_cancel_l (f x x)).
apply @compose with (y := f x y); [ now destruct p, (f x x) | ].
now destruct p, q, (f x x).
Qed.

(*
Theorem isnType_isSnType {A} n : isnType A n → isnType A (S n).
Proof.
intros * f.
revert A f.
induction n; intros; [ intros x y p q; now apply isProp_isSet | ].
intros p q.
apply IHn, f.
Qed.
*)

(*
Theorem equiv_eq : ∀ A B (f : A → B) (g : B → A) x y,
  (∀ b, f (g b) = b) → g x = g y → x = y.
Proof.
intros * Hfg H.
apply @compose with (y := f (g y)); [ | apply Hfg ].
destruct H; symmetry; apply Hfg.
Defined.
*)

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

(*
Theorem transport_pair : ∀ A B C (x y : A) (p : x = y) b c,
  transport (λ z, (B z * C z)%type) p (b, c) =
  (transport B p b, transport C p c).
Proof.
intros.
destruct p; reflexivity.
Qed.
*)

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

(*
Theorem isProp_isProp_sigT {A} {P : A → Type} :
  (∀ x, isProp (P x)) → isProp A → isProp (@sigT A P).
Proof.
intros * HP HS.
now apply (isnType_isnType_sigT A 0 P).
Qed.
*)

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

(*
Notation "⊥" := False.
*)

Definition Σ_pr₁ {A B} (x : { y : A & B y }) : A :=
  match x with existT _ a _ => a end.
Definition Σ_pr₂ {A B} (x : { y : A & B y }) : B (Σ_pr₁ x) :=
  match x with existT _ _ b => b end.

(*
Module Σ_type.
*)

Definition pr₁ {A B} := @Σ_pr₁ A B.
Definition pr₂ {A B} := @Σ_pr₂ A B.

(*
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
*)

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

(*
Theorem univalence : ∀ A B : Type, (A ≃ B) ≃ (A = B).
Proof.
intros.
pose proof (@univ A B) as p.
apply quasi_inv.
esplit; eassumption.
Defined.
*)

(*
Definition eqv_refl A : A ≃ A.
Proof.
exists id; apply qinv_isequiv; exists  id.
split; intros a; apply eq_refl.
Defined.
*)

(*
Definition ua_idtoeqv {A B} : ∀ (p : A = B), ua (idtoeqv p) = p.
Proof.
intros.
unfold ua; simpl.
set (q := isequiv_qinv idtoeqv (univ A B)).
destruct q as (f, (α, β)).
apply β.
Defined.
*)

(*
Notation "'Σ' ( x : A ) , B" :=
  ({ x : A & B }) (at level 0, x at level 0, B at level 100, only parsing).
Notation "'Π' ( x : A ) , B" :=
  (∀ x : A, B) (at level 0, x at level 0, B at level 100, only parsing).
*)

(*
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
*)

(*
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
*)

(*
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
*)

(*
Definition pr₁ {A B} := @Σ_pr₁ A B.
Definition pr₂ {A B} := @Σ_pr₂ A B.
*)

(*
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
*)
