(* experimentations on HoTT *)
(* requires coq 8.5 *)

Require Import Utf8 QArith NPeano.
Require Import chap1 chap2.

(* no default implicit without arguments *)
Arguments eq_refl [A] x.

Notation "⊥" := False.
Notation "( x , y ) '_{' P }" := (existT P x y)
  (at level 0, format "'[' ( x ,  y ) _{ P } ']'", only parsing).

Open Scope nat_scope.

(* Chapter 3 - Sets and logic *)

(* 3.1 Sets and n-types *)

(* Definition 3.1 *)

Definition isSet A := ∀ (x y : A) (p q : x = y), p = q.

(* personal solution *)
Definition ex_3_1_2_tac : isSet unit.
Proof.
intros x y p q.
destruct x, y.
refine (match p with eq_refl _ => _ end).
refine (match q with eq_refl _ => _ end).
reflexivity.
Defined.

Definition ex_3_1_2 : isSet unit :=
  λ (x y : unit),
  match x with
  | tt =>
      match y with
      | tt =>
          λ p q,
          match p with
          | eq_refl _ => match q with eq_refl _ => eq_refl _ end
          end
      end
  end.

(* "For by Theorem 2.8.1, for any x, y : 1 the type (x = y) is
    equivalent to 1. Since any two elements of 1 are equal, this
    implies that any two elements of x = y are equal." *)

(* hott_2_8_1 : ∀ x y : unit, (x = y) ≃ unit *)

Definition ex_3_1_2_alt_tac : isSet unit.
Proof.
intros x y p q.
pose proof hott_2_8_1 x y as r.
destruct r as (f, ((g, Hg), (h, Hh))).
unfold "◦", "~~", id in Hg, Hh.
pose proof Hh p as Hp.
pose proof Hh q as Hq.
destruct (f p), (f q).
subst p q; reflexivity.
Defined.

(* "Example 3.1.3. The type 0 is a set, for given any x, y : 0 we may
    deduce anything we like, by the induction principle of 0. *)

Definition ex_3_1_3_tac : isSet False.
Proof.
intros x y p q.
destruct x.
Defined.

Definition ex_3_1_3 : isSet False := λ x y, match x with end.

(* "Example 3.1.4. The type ℕ of natural numbers is also a set. This
    follows from Theorem 2.13.1, since all equality types x =_{ℕ} y
    are equivalent to either 1 or 0, and any two inhabitants of 1 or 0
    are equal. We will see another proof of this fact in Chapter 7. *)

(* ℕ.hott_2_13_1 : ∀ m n : nat, (m = n) ≃ ℕ.code m n *)

Print or.

Definition ℕ_code_equiv_1_or_0 m n :
  (ℕ.code m n ≃ unit) + (ℕ.code m n ≃ False).
Proof.
destruct (eq_nat_dec m n) as [H1| H1].
 left; subst m.
 apply (existT _ (λ c, tt)), qinv_isequiv.
 apply (existT _ (λ _, ℕ.r n)).
 unfold "◦", "~~", id; simpl.
 split; [ intros u; destruct u; reflexivity | ].
 intros c.
 induction n; [ destruct c; reflexivity | apply IHn ].

 right.
 apply (existT _ (λ c, H1 (ℕ.decode m n c))), qinv_isequiv.
 apply (existT _ (λ p : False, match p with end)).
 unfold "◦", "~~", id.
 split; [ intros p; destruct p | ].
 intros c; destruct (H1 (ℕ.decode m n c)).
Defined.

Definition ex_3_1_4_tac : isSet nat.
Proof.
intros m n p q.
pose proof ℕ.hott_2_13_1 m n as r.
pose proof ℕ_code_equiv_1_or_0 m n as s.
destruct s as [s| s].
 eapply equiv_compose in s; [ | apply r ].
 destruct s as (f, ((g, Hg), (h, Hh))).
 unfold "◦", "~~", id in Hg, Hh.
 pose proof Hh p as Hp.
 pose proof Hh q as Hq.
 destruct (f p), (f q).
 subst p q; reflexivity.

 eapply equiv_compose in s; [ | apply r ].
 destruct s as (f, ((g, Hg), (h, Hh))).
 exfalso; apply f, p.
Defined.

Definition ex_3_1_4 : isSet nat :=
  λ (m n : nat) (p q : m = n),
  match ℕ_code_equiv_1_or_0 m n with
  | inl s =>
      match s ◦◦ ℕ.hott_2_13_1 m n with
      | existT _ f (existT _ g Hg, existT _ h Hh) =>
          match f p with
          | tt =>
              λ (Hp0 : h tt = p),
              match f q as u1 return (h u1 = q → p = q) with
              | tt =>
                  λ Hq0 : h tt = q,
                  eq_ind (h tt) (λ p0 : m = n, p0 = q)
                    (eq_ind (h tt)
                       (λ q0 : m = n, h tt = q0) (eq_refl _) q Hq0) p
                    Hp0
              end (Hh q)
          end (Hh p)
      end
  | inr s =>
      match s ◦◦ ℕ.hott_2_13_1 m n with
      | existT _ f _ => match f p with end
      end
  end.

(* "Example 3.1.5. If A and B are sets, then so is A × B." *)

(* not sure of what I've done in this proof, but I completed it;
   perhaps simplifiable, understandable? *)
Definition ex_3_1_5 {A B} : isSet A → isSet B → isSet (A * B).
Proof.
intros r s x y p q.
pose proof cartesian.hott_2_6_2 x y as e.
destruct x as (xa, xb).
destruct y as (ya, yb); simpl in e.
apply quasi_inv in e.
destruct e as (f, ((g, Hg), (h, Hh))).
unfold "◦", "~~", id in Hg, Hh.
pose proof Hh p as Hhp.
pose proof Hh q as Hhq.
destruct (f p) as (fpa, fpb).
destruct (f q) as (fqa, fqb).
pose proof r xa ya fpa fqa as Hra.
pose proof s xb yb fpb fqb as Hrb.
destruct Hra, Hrb.
destruct Hhp; assumption.
Defined.

(* "Similarly, if A is a set and B : A → U is such that each B(x) is a
    set, then Σ(x:A),B(x) is a set." *)

(* just like ex_3_1_5 above, not sure of what I've done in this proof,
   but I completed it; perhaps simplifiable, understandable too? *)
Definition ex_3_1_5_bis {A B} :
  isSet A → (Π (x : A), isSet (B x)) → isSet (Σ (x : A), B x).
Proof.
intros r s x y p q.
pose proof Σ_type.hott_2_7_2 B x y as e.
destruct x as (xa, xb).
destruct y as (ya, yb); simpl in e.
destruct e as (f, ((g, Hg), (h, Hh))).
unfold "◦", "~~", id in Hg, Hh.
pose proof Hh p as Hhp.
pose proof Hh q as Hhq.
destruct (f p) as (fpa, fpb).
destruct (f q) as (fqa, fqb).
pose proof r xa ya fpa fqa as Hra.
destruct Hhp.
subst fpa.
rewrite <- Hhq.
apply ap, ap, s.
Defined.

(* "Example 3.1.6. If A is any type and B : A → U is such that each
    B(x) is a set, then the type Π (x:A), B(x) is a set." *)

Section ex_3_1_6.

Import Π_type.

Definition ex_3_1_6 {A B} : (Π (a : A), isSet (B a)) → isSet (Π (a : A), B a).
Proof.
intros r f g p q.
unfold isSet in r.
pose proof funext_prop_uniq_princ f g p as Hp.
pose proof funext_prop_uniq_princ f g q as Hq.
assert (∀ x : A, happly p x = happly q x) as Hx by (intros; apply r).
apply funext in Hx.
rewrite Hp, Hq, Hx.
reflexivity.
Defined.

End ex_3_1_6.

(* "Definition 3.1.7. A type A is a 1-type if for all x, y : A and p,
    q : x = y and r, s : p = q, we have r = s. *)

Definition is1Type A := ∀ (x y : A) (p q : x = y) (r s : p = q), r = s.

(* "Lemma 3.1.8. If A is a set (that is, isSet(A) is inhabited), then
    A is a 1-type." *)

Section lemma_3_1_8.

Import Σ_type2.

Check @compose.

(* required, but general purpose lemma, tac and exp versions *)
Definition compose_cancel_l_tac {A} {x y z : A} (p : x = y) (q r : y = z) :
  p • q = p • r
  → q = r.
Proof.
intros H.
eapply (dotl p⁻¹) in H.
eapply compose.
 eapply compose; [ | apply H ].
 eapply compose; [ | eapply invert, compose_assoc ].
 eapply compose; [ apply lu | apply dotr ].
 apply invert, compose_invert_l.

 eapply compose; [ eapply compose_assoc | ].
 eapply compose; [ | eapply invert, lu ].
 apply dotr, compose_invert_l.
Defined.

Definition compose_cancel_l {A} {x y z : A} (p : x = y) (q r : y = z) :
  p • q = p • r
  → q = r
:=
  λ s,
  lu q • ((compose_invert_l p)⁻¹ •r q) • (compose_assoc p⁻¹ p q)⁻¹ •
  (p⁻¹ •l s) •
  compose_assoc p⁻¹ p r • (compose_invert_l p •r r) • (lu r)⁻¹.

(* magic lemma to prove isSet → is1Type and also used later for
   ispType → isSpType *)
Definition compose_insert_tac {A x} (f : Π (y : A), x = y) {y z} (p : y = z) :
  f y • p = f z.
Proof.
pose proof apd f p as h.
eapply compose; [ | eassumption ].
eapply invert; destruct p; simpl; unfold id; apply ru.
Defined.

Definition compose_insert {A x} (f : Π (y : A), x = y) {y z} (p : y = z) :
  f y • p = f z
:=
  match p return f y • p = transport (eq x) p (f y) with
  | eq_refl _ => (ru (f y))⁻¹
  end
  • apd f p.

Print ru.

(* done but not obvious at all; I had to look at the way they did it,
   and I am sure I don't understand the point *)
Definition hott_3_1_8_tac {A} : isSet A → is1Type A.
Proof.
intros f x y p q r s.
apply (compose_cancel_l (f x y p p)).
eapply compose; [ eapply (compose_insert (f x y p)) | ].
apply invert, compose_insert.
Defined.

Definition hott_3_1_8 {A} : isSet A → is1Type A :=
  λ f x y p q r s,
  compose_cancel_l (f x y p p) r s
    (compose_insert (f x y p) r • (compose_insert (f x y p) s)⁻¹).

End lemma_3_1_8.

(* generalization *)

Definition isProp A := Π (x : A), Π (y : A), x = y.

Fixpoint ispType A p :=
  match p with
  | 0 => isProp A
  | S p' => ∀ x y : A, ispType (x = y) p'
  end.

(* A n-type has property 'ispType A (S n)', because the n of n-types
   start at -1 *)

Definition ispType_isSpType_tac {A} n : ispType A n → ispType A (S n).
Proof.
intros f x y.
revert A f x y.
induction n; intros.
 intros p q.
 apply (compose_cancel_l (f x x)).
 eapply compose; [ eapply (compose_insert (f x)) | ].
 apply invert, compose_insert.

 intros p q; apply IHn, f.
Defined.

Definition ispType_isSpType {A} n : ispType A n → ispType A (S n) :=
  nat_ind
    (λ n, ∀ A, ispType A n → ispType A (S n))
    (λ A f x y p q,
     compose_cancel_l (f x x) p q
       (compose_insert (f x) p • (compose_insert (f x) q)⁻¹))
    (λ n IHn A f x y, IHn (x = y) (f x y))
    n A.

(* "Example 3.1.9. The universe U is not a set." *)

Definition ex_3_1_9 : ¬isSet U.
Proof.
intros r.
unfold isSet in r.
pose proof r bool bool (ua bool_eq_bool_id) (ua bool_eq_bool_negb) as s.
apply (ap idtoeqv) in s.
eapply compose in s; [ | eapply invert, idtoeqv_ua ].
eapply invert, compose in s; [ | eapply invert, idtoeqv_ua ].
unfold bool_eq_bool_id, bool_eq_bool_negb in s.
simpl in s.
injection s; intros H _ _.
assert (negb true = true) as H1; [ rewrite H; reflexivity | ].
revert H1; apply Σ_type2.hott_2_12_6.
Defined.

(* 3.2 Propositions as types? *)

Section hott_3_2_2.
Import Σ_type.
Import Π_type.

(* "Theorem 3.2.2. It is not the case that for all A : U we have ¬(¬A)→A." *)

Definition hott_3_2_2_tac : notT (∀ A, notT (notT A) → A).
Proof.
intros f.
set (e := bool_eq_bool_negb).
set (u (g : notT bool) := g true).
set (nn A := notT (notT A)).
assert (p : pr₁ e (f _ u) = f _ u).
 eapply compose; [ eapply invert, ua_pcr | ].
 eapply compose; [ | apply (happly (apd f (ua e))) ].
 eapply invert, compose.
  apply (happly (@hott_2_9_4 _ nn id _ _ (ua e) (f bool)) u).

  apply ap, ap, funext; intros g; destruct (g true).

 eapply no_fixpoint_negb, p.
Defined.

Definition hott_3_2_2 : notT (∀ A : U, notT (notT A) → A)
:=
  λ f,
  let e := bool_eq_bool_negb in
  let u (x : notT bool) := x true in
  let nn A := notT (notT A) in
  no_fixpoint_negb (f bool u)
    ((ua_pcr e (f bool u))⁻¹
      • (happly (@hott_2_9_4 _ nn id _ _ (ua e) (f bool)) u
         • ap ((ua e)⁎ ◦ f bool)
             (funext (λ (x : notT bool), match x true with end)))⁻¹
      • happly (apd f (ua e)) u).

End hott_3_2_2.

(* "Corollary 3.2.7. It is not the case that for all A : U we have A+(¬A)." *)

Definition hott_3_2_7_tac : notT (∀ A, A + notT A).
Proof.
intros g.
apply hott_3_2_2; intros A u.
destruct (g A) as [a| w]; [ apply a | destruct (u w) ].
Defined.

Definition hott_3_2_7 : notT (∀ A, A + notT A)
:=
  λ g,
  hott_3_2_2
    (λ A u,
     match g A with
     | inl a => a
     | inr w => match u w with end
     end).

(* "3.3 Mere propositions" *)

(* "Definition 3.3.1. A type P is a mere proposition if for all x, y :
    P we have x = y." *)

Print isProp.

(* "Lemma 3.3.2. If P is a mere proposition and x0 : P, then P ≃ 1." *)

Definition hott_3_3_2_tac P : isProp P → ∀ x₀ : P, P ≃ unit.
Proof.
intros HP x₀.
apply (existT _ (λ _, tt)), qinv_isequiv.
apply (existT _ (λ _, x₀)).
split; intros x; [ destruct x; reflexivity | apply HP ].
Defined.

Definition hott_3_3_2 P : isProp P → ∀ x₀ : P, P ≃ unit
:=
  λ (HP : isProp P) (x₀ : P),
  existT isequiv (λ _, tt)
    (qinv_isequiv (λ _, tt)
       (existT _ (λ _, x₀)
          (λ x, match x with tt => eq_refl (id tt) end,  λ x, HP _ x))).

(* "Lemma 3.3.3. If P and Q are mere propositions such that P → Q and
    Q → P, then P ≃ Q." *)

Definition hott_3_3_3_tac P Q :
  isProp P → isProp Q → (P → Q) → (Q → P) → P ≃ Q.
Proof.
intros p q f g.
apply (existT _ f), qinv_isequiv, (existT _ g).
split; intros x; [ apply q | apply p ].
Defined.

Definition hott_3_3_3 P Q : isProp P → isProp Q → (P → Q) → (Q → P) → P ≃ Q
:=
  λ (p : isProp P) (q : isProp Q) (f : P → Q) (g : Q → P),
  existT isequiv f (qinv_isequiv f (existT _ g (λ y, q _ y, λ x, p _ x))).

Definition isContractible P := (isProp P * (P ≃ unit))%type.

(* "Lemma 3.3.4. Every mere proposition is a set." *)

Definition hott_3_3_4 A : isProp A → isSet A := ispType_isSpType 0.

(* "Lemma 3.3.5. For any type A, the types isProp(A) and isSet(A)
    are mere propositions." *)

Section Lemma_3_3_5.

Import Π_type.

Definition hott_3_3_5_i_tac A : isProp (isProp A).
Proof.
intros f g.
eapply funext; intros x.
eapply funext; intros y.
apply (hott_3_3_4 _ f).
Defined.

Definition hott_3_3_5_i A : isProp (isProp A) :=
  λ f g, funext (λ x, funext (λ y, hott_3_3_4 A f x y (f x y) (g x y))).

Definition hott_3_3_5_ii_tac A : isProp (isSet A).
Proof.
intros f g.
eapply funext; intros x.
eapply funext; intros y.
eapply funext; intros p.
eapply funext; intros q.
apply (ispType_isSpType 1), f.
Defined.

Definition hott_3_3_5_ii A : isProp (isSet A) :=
  λ f g,
  funext
    (λ x,
     funext
       (λ y,
        funext
          (λ p,
           funext
             (λ q, ispType_isSpType 1 f x y p q (f x y p q) (g x y p q))))).

Definition isequiv_mere_prop {A B} (f : A → B) :
  @equiv_prop A B isequiv → isProp (isequiv f).
Proof.
intros p e₁ e₂.
pose proof p f as pf.
destruct pf as ((qi, iq), eqv).
apply eqv.
Defined.

End Lemma_3_3_5.

(* "3.4 Classical vs. intuitionistic logic" *)

(* "law of excluded middle in homotopy type theory:
       LEM : Π (A:U), (isProp(A) → (A + ¬A))      (3.4.1)" *)

Definition LEM := Π (A : U), (isProp A → (A + notT A)).

(* "law of double negation
       Π (A:U), (isProp A → (¬¬A → A))            (3.4.2)" *)

Definition LDN := Π (A : U), (isProp A → (notT (notT A) → A)).

(* LEM and LDN are logically equivalent (ex 3.18) *)

Definition isProp_notT_tac A : isProp (A → ⊥).
Proof.
intros x y.
apply Π_type.funext; intros z; destruct (x z).
Defined.

Definition isProp_notT A : isProp (A → ⊥) :=
  λ x y : A → ⊥, Π_type.funext (λ (z : A), match x z with end).

Definition LEM_LDN : (LEM → LDN) * (LDN → LEM).
Proof.
split.
 intros HLEM A HP HNA.
 destruct (HLEM A HP) as [x| x]; [ apply x | destruct (HNA x) ].

 intros HLDN A HPA.
 apply HLDN.
 intros x y.
 destruct x as [x| x].
  destruct y as [y| y]; [ apply Σ_type2.inl_equal, HPA | destruct (y x) ].

  destruct y as [y| y]; [ destruct (x y) | ].
  apply Σ_type2.inr_equal.
  apply HLDN; [ apply (ispType_isSpType 0), isProp_notT | ].
  intros HNE; apply HNE, isProp_notT.

  intros HNA; apply HNA.
  right; intros HA; apply HNA.
  left; apply HA.
Defined.

(* "For emphasis, the proper version (3.4.1) may be denoted LEM-₁" *)

Definition LEM_p p := Π (A : U), (ispType A p → (A + notT A)).
Definition LEM_inf := Π (A : U), (A + notT A).

(* "Definition 3.4.3.
      (i) A type A is called decidable if A + ¬A.
     (ii) Similarly, a type family B : A → U is decidable if
              Π(a:A)(B(a) + ¬B(a)).
    (iii) In particular, A has decidable equality if
              Π(a,b:A)((a = b) + ¬(a = b))." *)

Definition isDecidable A := (A + notT A)%type.
Definition isDecidableFamily A B := Π (a : A), (B a + notT (B a)).
Definition hasDecidableEq A := Π (a : A), Π (b : A), ((a = b) + notT (a = b)).

(* "3.5 Subsets and propositional resizing" *)

Section hott_3_5.

Import Σ_type.

(* "Lemma 3.5.1. Suppose P : A → U is a type family such that P(x) is
    a mere proposition for all x : A. If u, v : Σ(x:A) P(x) are such
    that pr₁(u) = pr₁(v), then u = v." *)

Definition hott_3_5_1_my_proof_tac {A} (P : A → U) :
  (Π (x : A), isProp (P x))
  → ∀ u v : (Σ (x : A), P x),
  pr₁ u = pr₁ v
  → u = v.
Proof.
intros HP u v p.
destruct u as (ua, up); simpl in p.
destruct v as (va, vp); simpl in p.
eapply compose; [ eapply (pair_eq p), HP | reflexivity ].
Defined.

Definition hott_3_5_1_my_proof {A} (P : A → U) :
  (Π (x : A), isProp (P x))
  → ∀ u v : (Σ (x : A), P x),
  pr₁ u = pr₁ v
  → u = v
:=
  λ HP u v,
  match u with existT _ ua up =>
    match v with existT _ va vp =>
    λ p, pair⁼ p (HP va (transport P p up) vp)
    end
  end.

(* their proof *)

Definition hott_3_5_1_tac {A} (P : A → U) :
  (Π (x : A), isProp (P x))
  → ∀ u v : (Σ (x : A), P x),
  pr₁ u = pr₁ v
  → u = v.
Proof.
intros HP u v p.
pose proof @hott_2_7_2 A P u v as H.
destruct H as (f, ((g, Hg), (h, Hh))).
apply g, (existT _ p), HP.
Defined.

Definition hott_3_5_1 {A} (P : A → U) :
  (Π (x : A), isProp (P x))
  → ∀ u v : (Σ (x : A), P x),
  pr₁ u = pr₁ v
  → u = v
:=
  λ HP u v p,
  match hott_2_7_2 P u v with
  | existT _ _ (existT _ g _, _) =>
      g (existT _ p (HP (pr₁ v) (p⁎ (pr₂ u)) (pr₂ v)))
  end.

Definition SetU := {A : U & isSet A}.
Definition PropU := {A : U & isProp A}.

Definition SetU_equiv_eq A B s t :
  (existT isSet A s = existT isSet B t) ≃ (A = B).
Proof.
apply
  (existT _
     (λ p : existT isSet A s = existT isSet B t,
      match p in (_ = s0) return (let (b, _) := s0 in A = b) with
      | eq_refl _ => eq_refl A
      end)).
apply qinv_isequiv.
apply
  (existT _
     (λ p,
      hott_3_5_1 isSet hott_3_3_5_ii (existT isSet A s)
        (existT isSet B t) p)).
unfold "◦", "~~", id; simpl.
split.
 intros p.
 unfold hott_3_5_1; simpl.
 destruct (hott_2_7_2 isSet (existT isSet A s) (existT isSet B t)) as (f, H).
 destruct H as ((g, Hg), (h, Hh)).
 unfold hott_3_3_5_ii; simpl.
 destruct p; simpl.
 (* equivalent, equivalent... are they really equivalent?
    or just logically equivalent? *)
Abort.

Print SetU.

End hott_3_5.

(* "Recall that for any two universes Ui and Ui+1, if A : Ui then also
    A : Ui+1. Thus, for any (A, s) : SetUi we also have (A, s) : SetUi+1,
    and similarly for PropUi , giving natural maps
       SetUi → SetUi+1,              (3.5.3)
       PropUi → PropUi+1.            (3.5.4)" *)

(* ok, but I don't know how to program the hierarchy of universes in Coq;
   and the following axiom cannot be written either *)

(* "Axiom 3.5.5 (Propositional resizing). The map PropUi ! PropUi+1 is
    an equivalence." *)

(* "3.6 The logic of mere propositions" *)

Section hott_3_6.

(* "Example 3.6.1. If A and B are mere propositions, so is A x B." *)

Definition ex_3_6_1 {A B} : isProp A → isProp B → isProp (A * B).
Proof.
intros HA HB x y.
destruct x as (xa, xb).
destruct y as (ya, yb).
apply cartesian.pair_eq; simpl.
split; [ apply HA | apply HB ].
Defined.

(* "Example 3.6.2. If A is any type and B : A → U is such that for all
    x : A, the type B(x) is a mere proposition, then Π(x:A) B(x) is a
    mere proposition." *)

Import Π_type.

Definition ex_3_6_2 {A B} :
  (Π (x : A), isProp (B x)) → isProp (Π (x : A), B x).
Proof.
intros HP f g.
apply funext; intros x; apply HP.
Defined.

Definition isPropImp {A B} : isProp B → isProp (A → B).
Proof.
intros; apply ex_3_6_2; intros x; apply H.
Defined.

Definition isPropNot {A} : isProp A → isProp (notT A).
Proof.
intros. apply isPropImp; intros x y; destruct x.
Defined.

End hott_3_6.

(* "3.7 Propositional truncation" *)

(* I implement the element of a propositional truncation using a
   function of type unit → A. This way, two such elements can be
   forced to be equal (axiom PT_eq below), but the discriminate
   tactic, not appliable to functions, cannot be used with the
   risk of creating a contradiction (H: |1| = |2| and using the
   tactic 'discriminate H'). Not 100% sure since nothing prevent
   to use 'ap PT_elim' before (see theorem 'contradiction' below).
 *)

Inductive prop_trunc A :=
| PT : ∀ f : unit → A, prop_trunc A.
Arguments PT [A] f.

Notation "∥ A ∥" := (prop_trunc A) (A at level 0, format "∥ A ∥").
Notation "| x |" := (PT (λ _, x)) (x at level 0, format "| x |") : type_scope.

Axiom PT_eq : ∀ A, isProp ∥A∥.
Arguments PT_eq [A] x y.

Definition PT_elim {A} (x : ∥A∥) : A := match x with PT f => f tt end.

(* do not use "ap PT_elim"! here is the reason *)
Definition contradiction : False.
Proof.
pose proof PT_eq |1| |2| as H.
apply (ap PT_elim) in H.
discriminate H.
(* no  more subgoals, but aborting it even so *)
Abort.

(* "If B is a mere proposition and we have f : A → B, then there is an
    induced g : ∥A∥ → B such that g(|a|) ≡ f(a) for all a : A." *)

(* the hypothesis for B to be a mere proposition seems not useful... *)
Definition prop_trunc_rec_princ {A B} : (*isProp B →*)
  ∀ f : A → B, ∃ g : ∥A∥ → B, ∀ a : A, g |a| = f a.
Proof.
intros (*H*) f.
exists (λ z, f (PT_elim z)).
reflexivity.
Defined.

Definition prop_trunc_rec_fun {A B} (f : A → B) := f ◦ PT_elim.

Definition prop_trunc_rec_princ2 {A B} (f : A → B) a :
  prop_trunc_rec_fun f |a| = f a.
Proof.
reflexivity.
Defined.

Print prop_trunc_rec_princ2.

(* doing the exercise 3.14 in advance, just to see if my definition of
   propositional truncation works *)

Definition ex_3_14 : LEM → ∀ A, isProp A → (notT (notT A) ≃ ∥A∥).
Proof.
intros HLEM A HPA.
apply (existT _ (λ p, | (pr₁ LEM_LDN HLEM A HPA p) |)), qinv_isequiv.
apply (existT _ (λ p q, q (PT_elim p))).
unfold "◦", "~~", id; simpl.
split; [ intros x; destruct (HLEM A HPA); apply PT_eq | ].
intros f; apply Π_type.funext; intros x; destruct (f x).
Defined.

(* "3.8 The axiom of choice" *)

Axiom AC : ∀ X (A : X → U) (P : Π (x : X), (A x → U)),
  isSet X
  → (Π (x : X), isSet (A x))
  → (Π (x : X), Π (a : A x), isProp (P x a))
  → (Π (x : X), ∥ (Σ (a : A x), P x a) ∥)
  → ∥ (Σ (g : Π (x : X), A x), Π (x : X), P x (g x)) ∥.

Print AC.

Definition hott_3_8_2 :
  AC ↔
  ∀ (X : U) (Y : X → U), (Π (x : X), isSet (Y x)) →
  (Π (x : X), ∥ (Y x) ∥) → ∥ (Π (x : X), Y x) ∥.
bbb.

(* reminder

Definition hott_2_15_7 {X A} P :
  (Π (x : X), Σ (a : A x), P x a) ≃
  (Σ (g : Π (x : X), A x), Π (x : X), P x (g x)).

*)

_5htp.
