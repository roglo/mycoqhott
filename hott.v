(* experimentations on HoTT *)
(* requires coq 8.5 *)

Require Import Utf8 QArith NPeano.
Require Import chap1 chap2.

(* no default implicit without arguments *)
Arguments eq_refl [A] x.

Notation "⊥" := False.
Notation "⊤" := True.
Notation "'ℬ'" := (bool : Type).
Notation "( x , y ) '_{' P }" := (existT P x y)
  (at level 0, format "'[' ( x ,  y ) _{ P } ']'", only parsing).

Open Scope nat_scope.

(* Chapter 3 - Sets and logic *)

(* 3.1 Sets and n-types *)

(* Definition 3.1 *)

Definition isSet A := ∀ (x y : A) (p q : x = y), p = q.

(* personal solution *)
Definition ex_3_1_2_tac : isSet True.
Proof.
intros x y p q.
destruct x, y.
refine (match p with eq_refl _ => _ end).
refine (match q with eq_refl _ => _ end).
reflexivity.
Defined.

Definition ex_3_1_2 : isSet True :=
  λ (x y : True),
  match x with
  | I =>
      match y with
      | I =>
          λ p q,
          match p with
          | eq_refl _ => match q with eq_refl _ => eq_refl _ end
          end
      end
  end.

(* "For by Theorem 2.8.1, for any x, y : 1 the type (x = y) is
    equivalent to 1. Since any two elements of 1 are equal, this
    implies that any two elements of x = y are equal." *)

(* hott_2_8_1 : ∀ x y : True, (x = y) ≃ True *)

Definition ex_3_1_2_alt_tac : isSet ⊤.
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
    deduce anything we like, by the induction principle of 0." *)

Definition ex_3_1_3_tac : isSet False.
Proof.
intros x y p q.
destruct x.
Defined.

Definition ex_3_1_3 : isSet False := λ x y, match x with end.

(* bool is also a set *)

Definition bool_set : isSet ℬ.
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

(* "Example 3.1.4. The type ℕ of natural numbers is also a set. This
    follows from Theorem 2.13.1, since all equality types x =_{ℕ} y
    are equivalent to either 1 or 0, and any two inhabitants of 1 or 0
    are equal. We will see another proof of this fact in Chapter 7." *)

(* ℕ.hott_2_13_1 : ∀ m n : nat, (m = n) ≃ ℕ.code m n *)

Definition ℕ_code_equiv_1_or_0 m n :
  (ℕ.code m n ≃ True) + (ℕ.code m n ≃ False).
Proof.
destruct (eq_nat_dec m n) as [H1| H1].
 left; subst m.
 apply (existT _ (λ c, I)), qinv_isequiv.
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
          | I =>
              λ (Hp0 : h I = p),
              match f q as u1 return (h u1 = q → p = q) with
              | I =>
                  λ Hq0 : h I = q,
                  eq_ind (h I) (λ p0 : m = n, p0 = q)
                    (eq_ind (h I)
                       (λ q0 : m = n, h I = q0) (eq_refl _) q Hq0) p
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
    q : x = y and r, s : p = q, we have r = s." *)

Definition is1Type A := ∀ (x y : A) (p q : x = y) (r s : p = q), r = s.

(* "Lemma 3.1.8. If A is a set (that is, isSet(A) is inhabited), then
    A is a 1-type." *)

Section lemma_3_1_8.

Import Σ_type2.

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
eapply compose; [ | apply (apd f p) ].
eapply invert; destruct p; simpl; apply ru.
Defined.

Definition compose_insert {A x} (f : Π (y : A), x = y) {y z} (p : y = z) :
  f y • p = f z
:=
  match p return f y • p = transport (eq x) p (f y) with
  | eq_refl _ => (ru (f y))⁻¹
  end
  • apd f p.

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
   starts at -1 *)

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

Definition ex_3_1_9_tac : ¬isSet Type.
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

Definition isSet_Type_counterex (r : isSet Type) {A B} (p q : A ≃ B) : p = q :=
 (idtoeqv_ua p)⁻¹ • ap idtoeqv (r A B (ua p) (ua q)) • idtoeqv_ua q.

Definition ex_3_1_9 : ¬ isSet Type :=
  λ r : isSet Type,
  let ni : negb = id :=
    match isSet_Type_counterex r bool_eq_bool_negb bool_eq_bool_id with
    | eq_refl _ => eq_refl (Σ_type.pr₁ (pr₂ (Σ_type.pr₂ bool_eq_bool_negb)))
    end
  in
  Σ_type2.hott_2_12_6 (eq_ind_r (λ b, b true = true) (eq_refl true) ni).

(* 3.2 Propositions as types? *)

Section hott_3_2_2.
Import Σ_type.
Import Π_type.

(* "Theorem 3.2.2. It is not the case that for all A : Type we have ¬(¬A)→A." *)

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

Definition hott_3_2_2 : notT (∀ A : Type, notT (notT A) → A)
:=
  λ f,
  let e := bool_eq_bool_negb in
  let u (x : notT ℬ) := x true in
  let nn A := notT (notT A) in
  no_fixpoint_negb (f bool u)
    ((ua_pcr e (f bool u))⁻¹
      • (happly (@hott_2_9_4 _ nn id _ _ (ua e) (f bool)) u
         • ap ((ua e)⁎ ◦ f bool)
             (funext (λ (x : notT bool), match x true with end)))⁻¹
      • happly (apd f (ua e)) u).

End hott_3_2_2.

(* "Corollary 3.2.7. It is not the case that for all A : Type we have A+(¬A)." *)

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

(* Print isProp. *)

(* "Lemma 3.3.2. If P is a mere proposition and x0 : P, then P ≃ 1." *)

Definition hott_3_3_2_tac P : isProp P → ∀ x₀ : P, P ≃ True.
Proof.
intros HP x₀.
apply (existT _ (λ _, I)), qinv_isequiv.
apply (existT _ (λ _, x₀)).
split; intros x; [ destruct x; reflexivity | apply HP ].
Defined.

Definition hott_3_3_2 P : isProp P → ∀ x₀ : P, P ≃ True
:=
  λ (HP : isProp P) (x₀ : P),
  existT isequiv (λ _, I)
    (qinv_isequiv (λ _, I)
       (existT _ (λ _, x₀)
          (λ x, match x with I => eq_refl (id I) end,  λ x, HP _ x))).

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

Definition isContractible P := (isProp P * (P ≃ True))%type.

(* "Lemma 3.3.4. Every mere proposition is a set." *)

Definition isProp_isSet A : isProp A → isSet A := ispType_isSpType 0.

(* "Lemma 3.3.5. For any type A, the types isProp(A) and isSet(A)
    are mere propositions." *)

Section Lemma_3_3_5.

Import Π_type.

Definition hott_3_3_5_i_tac A : isProp (isProp A).
Proof.
intros f g.
eapply funext; intros x.
eapply funext; intros y.
apply (isProp_isSet _ f).
Defined.

Definition hott_3_3_5_i A : isProp (isProp A) :=
  λ f g, funext (λ x, funext (λ y, isProp_isSet A f x y (f x y) (g x y))).

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

Definition isProp_isequiv {A B} (f : A → B) : isProp (isequiv f).
Proof.
intros e₁ e₂.
pose proof equivalence_isequiv f as pf.
destruct pf as ((qi, iq), eqv).
apply eqv.
Defined.

End Lemma_3_3_5.

(* "3.4 Classical vs. intuitionistic logic" *)

(* "law of excluded middle in homotopy type theory:
       LEM : Π (A:Type), (isProp(A) → (A + ¬A))      (3.4.1)" *)

Definition LEM := Π (A : Type), (isProp A → (A + notT A)).

(* "law of double negation
       Π (A:Type), (isProp A → (¬¬A → A))            (3.4.2)" *)

Definition LDN := Π (A : Type), (isProp A → (notT (notT A) → A)).

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

Definition LEM_p p := Π (A : Type), (ispType A p → (A + notT A)).
Definition LEM_inf := Π (A : Type), (A + notT A).

(* "Definition 3.4.3.
      (i) A type A is called decidable if A + ¬A.
     (ii) Similarly, a type family B : A → Type is decidable if
              Π(a:A)(B(a) + ¬B(a)).
    (iii) In particular, A has decidable equality if
              Π(a,b:A)((a = b) + ¬(a = b))." *)

Definition isDecidable A := (A + notT A)%type.
Definition isDecidableFamily A B := Π (a : A), (B a + notT (B a)).
Definition hasDecidableEq A := Π (a : A), Π (b : A), ((a = b) + notT (a = b)).

(* "3.5 Subsets and propositional resizing" *)

Section hott_3_5.

Import Σ_type.

(* "Lemma 3.5.1. Suppose P : A → Type is a type family such that P(x) is
    a mere proposition for all x : A. If u, v : Σ(x:A) P(x) are such
    that pr₁(u) = pr₁(v), then u = v." *)

Definition hott_3_5_1_my_proof_tac {A} (P : A → Type) :
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

Definition hott_3_5_1_my_proof {A} (P : A → Type) :
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

Definition hott_3_5_1_tac {A} (P : A → Type) :
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

Definition hott_3_5_1 {A} (P : A → Type) :
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

Definition SetU := {A : Type & isSet A}.
Definition PropU := {A : Type & isProp A}.

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

(* "Example 3.6.2. If A is any type and B : A → Type is such that for all
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

Axiom prop_trunc : Type → Type.
Notation "∥ A ∥" := (prop_trunc A) (A at level 0, format "∥ A ∥") : type_scope.

Axiom PT_intro : ∀ A, A → ∥A∥.
Axiom PT_elim : ∀ A, ∥A∥ → A.
Arguments prop_trunc _%type.
Arguments PT_intro [A] x.
Arguments PT_elim [A] x.

Notation "| x |" := (PT_intro x) (x at level 0, format "| x |").

Axiom PT_eq : ∀ A, isProp ∥A∥.
Arguments PT_eq [A] x y.

(* "If B is a mere proposition and we have f : A → B, then there is an
    induced g : ∥A∥ → B such that g(|a|) ≡ f(a) for all a : A." *)

Definition prop_trunc_rec_tac {A B} : isProp B →
  ∀ (f : A → B) a, f (PT_elim |a|) = f a.
Proof.
intros PB f a.
apply PB.
Defined.

Definition prop_trunc_rec {A B} : isProp B →
  ∀ (f : A → B) a, f (PT_elim |a|) = f a
:=
  λ PB f a, PB (f (PT_elim |a|)) (f a).

(* doing the exercise 3.14 in advance, just to see if my definition of
   propositional truncation works *)

Definition ex_3_14 : LEM → ∀ A, isProp A → (notT (notT A) ≃ ∥A∥).
Proof.
intros HLEM A HPA.
apply (existT _ (λ p, | (pr₁ LEM_LDN HLEM A HPA p) |)), qinv_isequiv.
(*
assert (∥A∥ → notT (notT A)) as g by (intros p q; destruct (q (PT_elim p))).
*)
apply (existT _ (λ p (q : notT A), match q (PT_elim p) return ⊥ with end)).
split; [ intros x; destruct (HLEM A HPA); apply PT_eq | ].
intros f; apply Π_type.funext; intros x; destruct (f x).
Defined.

(* "3.8 The axiom of choice" *)

Definition AC := ∀ (X : Type) (A : X → Type) (P : Π (x : X), (A x → Type)),
  isSet X
  → (Π (x : X), isSet (A x))
  → (Π (x : X), Π (a : A x), isProp (P x a))
  → (Π (x : X), ∥ (Σ (a : A x), P x a) ∥)
  → ∥ (Σ (g : Π (x : X), A x), Π (x : X), P x (g x)) ∥.

Definition AC_3_8_3 :=
  ∀ (X : Type) (Y : X → Type), isSet X → (Π (x : X), isSet (Y x))
  → (Π (x : X), ∥ (Y x) ∥) → ∥ (Π (x : X), Y x) ∥.

Definition hott_3_8_2 : AC ≃ AC_3_8_3.
Proof.
apply hott_3_3_3.
 do 7 (apply ex_3_6_2; intros).
 intros u v; apply PT_eq.

 do 5 (apply ex_3_6_2; intros).
 intros u v; apply PT_eq.

 intros AC X Y SX SY.
 assert (H1 : ∀ x : X, Y x → isProp ⊤).
  intros _ _ x y.
  apply (Σ_type.pr₁ (quasi_inv (hott_2_8_1 x y))), x.

  assert (∀ Z (z : Z), ∥{_ : Z & X → ⊤}∥ → ∥Z∥) as H2.
   intros Z z H2; apply PT_intro, z.

   intros H; apply H2; [ intros x; apply PT_elim, H | ].
   apply (AC X Y (λ _ _, ⊤) SX SY H1); intros x.
   apply PT_intro, (existT _ (PT_elim (H x))), I.

 unfold AC.
 intros H X A P SX SA PP H1.
 pose proof (λ A P, ua (quasi_inv (@UnivProp.hott_2_15_7 X A P))) as H3.
 rewrite H3.
 apply (λ S, H X (λ x, Σ (a : A x), P x a) SX S H1); intros x.
 apply ex_3_1_5_bis; [ apply SA | intros y; apply isProp_isSet, PP ].
Defined.

Definition isProp_Σ_type_tac {A B} :
  isProp A → (Π (x : A), isProp (B x)) → isProp Σ (x : A), B x.
Proof.
intros PA PB (x₁, x₂) (y₁, y₂).
pose proof (PA x₁ y₁) as H; destruct H.
pose proof (PB x₁ x₂ y₂) as H; destruct H.
reflexivity.
Defined.

Definition isProp_Σ_type {A B} :
  isProp A → (Π (x : A), isProp (B x)) → isProp Σ (x : A), B x
:=
  λ PA PB x,
  match x with
  | existT _ x₁ x₂ =>
      λ y,
      match y with
      | existT _ y₁ y₂ =>
          match PA x₁ y₁ with
          | eq_refl _ =>
              λ y₂,
              match PB x₁ x₂ y₂  with
              | eq_refl _ => eq_refl (existT B x₁ x₂)
              end
          end y₂
      end
  end.

Definition AC_3_8_3_equiv :=
  ∀ (X : Type) (Y : X → Type), isSet X → (Π (x : X), isSet (Y x))
  → (Π (x : X), ∥ (Y x) ∥) ≃ ∥ (Π (x : X), Y x) ∥.

Definition AC_equiv_3_8_3_equiv : AC ≃ AC_3_8_3_equiv.
Proof.
eapply equiv_compose; [ apply hott_3_8_2 |  ].
apply hott_3_3_3.
 do 5 (apply ex_3_6_2; intros).
 intros u v; apply PT_eq.

 do 4 (apply ex_3_6_2; intros).
 unfold equivalence.
 apply isProp_Σ_type.
  apply ex_3_6_2; intros.
  intros u v; apply PT_eq.

  intros y; apply isProp_isequiv.

 unfold AC_3_8_3, AC_3_8_3_equiv.
 intros AC X Y SX SY.
 apply hott_3_3_3.
  apply ex_3_6_2; intros; intros u v; apply PT_eq.

  intros u v; apply PT_eq.

  intros H; apply (PT_intro (λ x, PT_elim (H x))).

  intros H x; apply (PT_intro (PT_elim H x)).

 unfold AC_3_8_3, AC_3_8_3_equiv.
 intros AC X Y SX SY.
 apply hott_3_3_3.
  apply ex_3_6_2; intros; intros u v; apply PT_eq.

  intros u v; apply PT_eq.

  intros H; apply (PT_intro (λ x, PT_elim (H x))).

  intros H x; apply (PT_intro (PT_elim H x)).
Defined.

(* equivalence is a set, whenever A and B are *)

Definition isSet_equiv {A B : Type} : isSet A → isSet B → isSet (A ≃ B).
Proof.
intros SA SB.
apply ex_3_1_5_bis; [ apply ex_3_1_6; intros; apply SB | idtac ].
intros f; apply isProp_isSet, isProp_isequiv.
Defined.

(* univalence implies equality *)

Definition univ_imp_eq :  ∀ (A B : Type), A ≃ B → A = B.
Proof.
intros A B H.
pose proof (Σ_type.pr₁ (univalence2 A B) H) as H1.
assumption.
Defined.

(* "Lemma 3.8.5. There exists a type X and a family Y : X → Type such
    that each Y(x) is a set, but such that (3.8.3) is false." *)

(* If I understand well, the axiom of choice is not compatible with
   families of sets whose father is not a set. *)

Definition pair_eq_bool_trunc := Σ (A : Type), ∥(ℬ = A)∥.

Definition equiv_eq_pair_trunc A B p q :
  ((existT _ A p : pair_eq_bool_trunc) = existT _ B q) ≃ (A ≃ B).
Proof.
intros; simpl.
apply
 (existT _
    (λ H,
     (λ
      H2 : Σ_type.pr₁ (existT (λ A0 : Type, ∥(ℬ = A0)∥) A p)
           ≃ Σ_type.pr₁ (existT (λ A0 : Type, ∥(ℬ = A0)∥) B q), H2)
       (idtoeqv (ap Σ_type.pr₁ H)))).
apply qinv_isequiv.
apply (existT _ (λ r : A ≃ B, Σ_type.pair_eq (ua r) (PT_eq ((ua r)⁎ p) q))).
unfold "◦", "~~", id; simpl.
split.
 intros r.
 rewrite <- idtoeqv_ua; f_equal.
 destruct (ua r); simpl; unfold id.
 destruct (PT_eq p q); reflexivity.

 intros r.
 rewrite ua_idtoeqv.
 refine match r with
        | eq_refl _ => _
        end; simpl; unfold id.
 assert (SA : isSet ∥(ℬ = A)∥) by apply isProp_isSet, PT_eq.
 assert (H : PT_eq p p = eq_refl p) by apply SA.
 rewrite H; reflexivity.
Defined.

Definition equiv_eq_bool_trunc :
  (existT (λ A, ∥(ℬ = A)∥) ℬ |(eq_refl ℬ)| =
   existT (λ A, ∥(ℬ = A)∥) ℬ |(eq_refl ℬ)|) ≃
   (ℬ ≃ ℬ).
Proof.
intros; apply equiv_eq_pair_trunc.
Defined.

Definition isProp_pair_trunc {A} : isProp (Σ (B : Type), ∥(A = B)∥).
Proof.
intros x y.
set (X := Σ (B : Type), ∥(A = B)∥).
set (x₀ := existT _ A |(eq_refl A)|:X); simpl in x₀.
transitivity x₀; subst x₀.
 symmetry.
 destruct x as (C, p).
pose proof PT_elim p as q.
bbb.

; apply (Σ_type.pair_eq (PT_elim p)), PT_eq.

 destruct y as (C, p); apply (Σ_type.pair_eq (PT_elim p)), PT_eq.
Defined.

bbb.

Definition what : ∃ X (Y : X → Type), ⊥.
Proof.
(* I suspect my PT_elim to be the origin of this contradiction;
   aim: find the minimum proof that show that. Perhaps theorem
   isProp_pair_trunc is so corrupted. *)
bbb.
set (X := Σ (A : Type), ∥(ℬ = A)∥).
set (x₀ := existT _ ℬ |(eq_refl ℬ)|:X); simpl in x₀.
set (Y := λ x, x₀ = x:Type); simpl in Y.
exists X, Y.
assert (PX : isProp X) by apply isProp_pair_trunc.
apply isProp_isSet in PX.
destruct equiv_eq_bool_trunc as (f, ((g, Hg), _)).
pose proof (PX x₀ x₀ (g bool_eq_bool_id) (g bool_eq_bool_negb)) as s.
unfold bool_eq_bool_id, bool_eq_bool_negb in s; simpl in s.
apply (ap f) in s.
eapply compose in s; [ symmetry in s | eapply invert, Hg ].
eapply compose in s; [ symmetry in s | eapply invert, Hg ].
apply EqdepFacts.eq_sigT_fst in s.
pose proof (hap s false) as H2.
revert H2; apply Σ_type2.hott_2_12_6.
What. ?????

Definition hott_3_8_5_tac : ∃ X (Y : X → Type),
  notT ((Π (x : X), ∥(Y x)∥) → ∥(Π (x : X), Y x)∥).
Proof.
set (X := Σ (A : Type), ∥(ℬ = A)∥).
set (x₀ := existT _ ℬ |(eq_refl ℬ)|:X); simpl in x₀.
set (Y := λ x, x₀ = x:Type); simpl in Y.
exists X, Y.
intros _.
assert (PX : isProp X) by apply isProp_pair_trunc.
apply isProp_isSet in PX.
destruct equiv_eq_bool_trunc as (f, ((g, Hg), _)).
pose proof (PX x₀ x₀ (g bool_eq_bool_id) (g bool_eq_bool_negb)) as s.
unfold bool_eq_bool_id, bool_eq_bool_negb in s; simpl in s.
apply (ap f) in s.
eapply compose in s; [ symmetry in s | eapply invert, Hg ].
eapply compose in s; [ symmetry in s | eapply invert, Hg ].
apply EqdepFacts.eq_sigT_fst in s.
pose proof (hap s false) as H2.
revert H2; apply Σ_type2.hott_2_12_6.
Defined.

Set Printing Depth 100.
Definition hott_3_8_5 : ∃ X (Y : X → Type), (∀ x, isSet (Y x))
  → notT ((Π (x : X), ∥(Y x)∥) → ∥(Π (x : X), Y x)∥)
:=
  let X := {A : Type & ∥(ℬ = A)∥} in
  let x₀ := existT (λ A : Type, ∥(ℬ = A)∥) ℬ |(eq_refl ℬ)|:X in
  let Y := λ x : X, x₀ = x:Type in
  ex_intro _ X
    (ex_intro _ Y
       (λ _ _,
        let (f, i) := equiv_eq_bool_trunc in
        let (s, x) := i in
        let (g, Hg) := s in
        Σ_type2.hott_2_12_6
          (hap
             (f_equal
                (λ e0 : ℬ ≃ ℬ,
                 let (x, i0) := e0 in
                 let (_, s7) := i0 in let (x0, _) := s7 in x0)
                (eq_sym
                   ((Hg
                       (existT isequiv negb
                          (existT (λ g0 : ℬ → ℬ, negb ◦ g0 ~~ id) negb
                             (λ b : ℬ,
                              if b as b0 return (negb (negb b0) = b0)
                              then eq_refl true
                              else eq_refl false),
                          existT (λ h : ℬ → ℬ, h ◦ negb ~~ id) negb
                            (λ b : ℬ,
                             if b as b0 return (negb (negb b0) = b0)
                             then eq_refl true
                             else eq_refl false))))⁻¹ •
                   (eq_sym
                      ((Hg
                          (existT isequiv id
                             (existT (λ g0 : ℬ → ℬ, id ◦ g0 ~~ id) id
                                (λ H : ℬ, eq_refl ((id ◦ id) H)),
                              existT (λ h : ℬ → ℬ, h ◦ id ~~ id) id
                                (λ H : ℬ, eq_refl ((id ◦ id) H)))))⁻¹ •
                 (ap f
                    (isProp_isSet X isProp_pair_trunc x₀ x₀
                        (g bool_eq_bool_id) (g bool_eq_bool_negb))))))))
        false))).

bbb.
