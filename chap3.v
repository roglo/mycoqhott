(* experimentations on HoTT *)
(* requires coq 8.5 *)

Require Import Utf8 QArith NPeano.
Require Import chap1 chap2.

(* no default implicit without arguments *)
Arguments eq_refl [A] x.

Notation "⊥" := False.
Notation "⊤" := True.
Notation "'ℬ'" := (bool : Type).
Notation "A ⇔ B" := ((A → B) * (B → A))%type (at level 100).
Notation "( x , y ) '_{' P }" := (existT P x y)
  (at level 0, format "'[' ( x ,  y ) _{ P } ']'", only parsing).

Open Scope nat_scope.

Theorem Nat_le_neq_lt : ∀ a b, a ≤ b → a ≠ b → a < b.
Proof.
intros a b Hab Hnab.
apply le_lt_eq_dec in Hab.
destruct Hab as [Hle| Heq]; [ assumption | idtac ].
exfalso; apply Hnab; assumption.
Qed.

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

(* ex_3_1_2_alt_tac *)

Definition isSet_True : isSet ⊤.
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

Definition isSet_bool : isSet ℬ.
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

(* ℕ.hott_2_13_1 : ∀ m n : ℕ, (m = n) ≃ ℕ.code m n *)

Definition N_code_equiv_1_or_0 m n :
  (N.code m n ≃ True) + (N.code m n ≃ False).
Proof.
destruct (eq_nat_dec m n) as [H1| H1].
 left; subst m.
 exists (λ c, I); apply qinv_isequiv.
 exists (λ _, N.r n).
 unfold "◦", "~~", id; simpl.
 split; [ intros u; destruct u; reflexivity | intros c ].
 induction n; [ destruct c; reflexivity | apply IHn ].

 right.
 exists (λ c, H1 (N.decode m n c)); apply qinv_isequiv.
 exists (λ p : False, match p with end).
 unfold "◦", "~~", id.
 split; [ intros p; destruct p | ].
 intros c; destruct (H1 (N.decode m n c)).
Defined.

(* ex_3_1_4 *)

Definition isSet_nat_tac : isSet ℕ.
Proof.
intros m n p q.
pose proof N.hott_2_13_1 m n as r.
pose proof N_code_equiv_1_or_0 m n as s.
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

Definition isSet_nat : isSet ℕ :=
  λ (m n : ℕ) (p q : m = n),
  match N_code_equiv_1_or_0 m n with
  | inl s =>
      match s ◦◦ N.hott_2_13_1 m n with
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
      match s ◦◦ N.hott_2_13_1 m n with
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
  let g := f x y p in
  compose_cancel_l (g p) r s (compose_insert g r • (compose_insert g s)⁻¹).

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

(* "Theorem 3.2.2. It is not the case that for all A : Type we have
    ¬(¬A)→A." *)

Definition hott_3_2_2_tac : notT (∀ A, notT (notT A) → A).
Proof.
intros f.
set (u := (λ g, g true) : notT (notT bool)); simpl in u.
set (nn A := notT (notT A)).
assert (p : pr₁ bool_eq_bool_negb (f _ u) = f _ u).
 eapply compose; [ eapply invert, ua_pcr | ].
 eapply compose; [ | apply (happly (apd f (ua bool_eq_bool_negb))) ].
 eapply invert, compose.
  apply (happly (@hott_2_9_4 _ nn id _ _ (ua bool_eq_bool_negb) (f bool)) u).

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

(* "Corollary 3.2.7. It is not the case that for all A : Type we have
    A+(¬A)." *)

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
exists (λ _, I); apply qinv_isequiv.
exists (λ _, x₀).
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
exists f; apply qinv_isequiv; exists g.
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
exists
  (λ p : existT isSet A s = existT isSet B t,
   match p in (_ = s0) return (let (b, _) := s0 in A = b) with
   | eq_refl _ => eq_refl A
   end).
apply qinv_isequiv.
exists (hott_3_5_1 isSet hott_3_3_5_ii (existT isSet A s) (existT isSet B t)).
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

(* "Axiom 3.5.5 (Propositional resizing). The map PropUi → PropUi+1 is
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
 do 7 (apply ex_3_6_2; intros); apply PT_eq.

 do 5 (apply ex_3_6_2; intros); apply PT_eq.

 intros AC₁ X Y SX SY YX.
 unfold AC in AC₁; rename AC₁ into AC.
 assert (H1 : ∀ x : X, Y x → isProp ⊤).
  intros _ _ x y.
  apply (Σ_type.pr₁ (quasi_inv (hott_2_8_1 x y))), x.

  assert (H2 : ∀ x : X, ∥{_ : Y x & ⊤}∥).
   intros x.
   apply (PT_rec (Y x)); [ | apply PT_eq | apply YX ].
   intros y; apply PT_intro, (existT (λ (_ : Y x), True) (y : Y x) I).

   pose proof AC X Y (λ _ _, ⊤) SX SY H1 H2 as H; simpl in H.
   assert (f : {_ : ∀ x : X, Y x & X → ⊤} → ∥(∀ x : X, Y x)∥).
    intros H3; apply PT_intro, H3.

    assert (PB : isProp ∥(∀ x : X, Y x)∥) by apply PT_eq.
    apply (Σ_type.pr₁ (PT_rec _ _ f PB) H).

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

  intros H; apply AC; assumption.

  intros H x.
  pose proof (λ B PB H1, Σ_type.pr₁ (PT_rec (∀ x : X, Y x) B H1 PB) H) as H1.
  apply H1; [ apply PT_eq | intros H2; apply PT_intro, H2 ].

 unfold AC_3_8_3, AC_3_8_3_equiv.
 intros AC X Y SX SY.
 apply hott_3_3_3.
  apply ex_3_6_2; intros; intros u v; apply PT_eq.

  intros u v; apply PT_eq.

  intros H; apply AC; assumption.

  intros H x.
  pose proof (λ B PB H1, Σ_type.pr₁ (PT_rec (∀ x : X, Y x) B H1 PB) H) as H1.
  apply H1; [ apply PT_eq | intros H2; apply PT_intro, H2 ].
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
exists
  (λ H,
   (λ
    H2 : Σ_type.pr₁ (existT (λ A0 : Type, ∥(ℬ = A0)∥) A p)
         ≃ Σ_type.pr₁ (existT (λ A0 : Type, ∥(ℬ = A0)∥) B q), H2)
     (idtoeqv (ap Σ_type.pr₁ H))).
apply qinv_isequiv.
exists (λ r : A ≃ B, Σ_type.pair_eq (ua r) (PT_eq _ ((ua r)⁎ p) q)).
unfold "◦", "~~", id; simpl.
split.
 intros r.
 rewrite <- idtoeqv_ua; f_equal.
 destruct (ua r); simpl; unfold id.
 destruct (PT_eq _ p q); reflexivity.

 intros r.
 rewrite ua_idtoeqv.
 refine match r with
        | eq_refl _ => _
        end; simpl; unfold id.
 assert (SA : isSet ∥(ℬ = A)∥) by apply isProp_isSet, PT_eq.
 assert (H : PT_eq _ p p = eq_refl p) by apply SA.
 rewrite H; reflexivity.
Defined.

Definition equiv_eq_bool_trunc :
  (existT (λ A, ∥(ℬ = A)∥) ℬ (PT_intro (eq_refl ℬ)) =
   existT (λ A, ∥(ℬ = A)∥) ℬ (PT_intro (eq_refl ℬ))) ≃
   (ℬ ≃ ℬ).
Proof.
intros; apply equiv_eq_pair_trunc.
Defined.

Definition hott_3_8_5_tac :
  Σ (X : Type), Σ (Y : X → Type),
  notT ((Π (x : X), ∥(Y x)∥) → ∥(Π (x : X), Y x)∥).
Proof.
set (X := Σ (A : Type), ∥(ℬ = A)∥).
set (x₀ := existT _ ℬ (PT_intro (eq_refl ℬ)):X); simpl in x₀.
set (Y := λ x, x₀ = x : Type); simpl in Y.
exists X, Y; intros H1.
apply (@PT_intro_not (∀ x, Y x)).
 intros H2; subst Y; simpl in H2.
 assert (PX : isProp X).
  intros x y.
  transitivity x₀; [ symmetry; apply H2 | apply H2 ].

  apply isProp_isSet in PX.
  destruct equiv_eq_bool_trunc as (f, ((g, Hg), _)).
  pose proof (PX x₀ x₀ (g bool_eq_bool_id) (g bool_eq_bool_negb)) as s.
  unfold bool_eq_bool_id, bool_eq_bool_negb in s; simpl in s.
  apply (ap f) in s.
  eapply compose in s; [ symmetry in s | eapply invert, Hg ].
  eapply compose in s; [ symmetry in s | eapply invert, Hg ].
  apply EqdepFacts.eq_sigT_fst in s.
  pose proof (hap s false) as H3.
  revert H3; apply Σ_type2.hott_2_12_6.

 apply H1; intros (A, p); subst x₀.
 apply (PT_rec (ℬ = A)); [ | apply PT_eq | assumption ].
 intros q; destruct q.
 apply PT_intro, (Σ_type.pair_eq (eq_refl ℬ)), PT_eq.
Defined.

(* Set Printing Depth 100. *)

(* "3.9 The principle of unique choice" *)

(* Lemma 3.9.1 *)

Definition hott_3_9_1_tac {P} : isProp P → P ≃ ∥P∥.
Proof.
intros PP.
apply hott_3_3_3; [ assumption | apply PT_eq | apply PT_intro | ].
apply PT_elim; assumption.
Defined.

Definition hott_3_9_1 {P} : isProp P → P ≃ ∥P∥ :=
  λ (PP : isProp P),
  hott_3_3_3 P ∥P∥ PP (PT_eq P) (PT_intro (A:=P)) (PT_elim PP).

(* "Corollary 3.9.2 (The principle of unique choice). Suppose a type
    family P : A → U such that
         (i) For each x, the type P(x) is a mere proposition, and
        (ii) For each x we have ∥P(x)∥.
    Then we have ∏ (x:A) P(x)." *)

Definition hott_3_9_2 {A P} :
  (Π (x : A), isProp (P x)) → (Π (x : A), ∥(P x)∥) → Π (x : A), P x.
Proof.
intros PP PTP x.
apply PT_elim; [ apply PP | apply PTP ].
Defined.

(* "3.10 When are propositions truncated?" *)

(* "3.11 Contractibility" *)

Section Contr.
Import Σ_type.

(* "In Lemma 3.3.2 we observed that a mere proposition which is
    inhabited must be equivalent to 1, and it is not hard to see
    that the converse also holds." *)

Definition hott_3_3_2_conv P : ∀ x₀ : P, P ≃ ⊤ → isProp P.
Proof.
intros x₀ H x y.
destruct H as (f, ((g, Hg), (h, Hh))).
unfold "◦", "~~", id in Hg, Hh.
do 2 (rewrite <- Hh; symmetry).
apply ap.
destruct (f x), (f y); reflexivity.
Defined.

(* "Definition 3.11.1. A type A is *contractible*, or a *singleton*,
    if there is a : A, called the *center of contraction*, such that
    a = x for all x : A. We denote the specified path a = x by contr_x." *)

Definition isContr A := Σ (a : A), Π (x : A), a = x.

(* "Lemma 3.11.3. For a type A, the following are logically
    equivalent.
        (i) A is contractible in the sense of Definition 3.11.1.
       (ii) A is a mere proposition, and there is a point a : A.
      (iii) A is equivalent to 1." *)

Definition isContr_isProp A : isContr A → isProp A.
Proof.
intros p x y.
destruct p as (a, p).
transitivity a; [ symmetry; apply p | apply p ].
Defined.

Definition hott_3_11_3_i_ii A : isContr A → isProp A * Σ (a : A), ⊤.
Proof.
intros p.
split; [ apply isContr_isProp; assumption | ].
destruct p as (a, p).
exists a; constructor.
Defined.

Definition hott_3_11_3_ii_iii A : isProp A * (Σ (a : A), ⊤) → A ≃ ⊤.
Proof.
intros (p, (a, _)).
apply hott_3_3_2; assumption.
Defined.

Definition hott_3_11_3_iii_i A : A ≃ ⊤ → isContr A.
Proof.
intros p.
apply EqStr.equiv_fun in p.
destruct p as (f, (g, (Hg, Hh))).
exists (g I); intros x.
etransitivity; [ | apply Hg ].
destruct (f x); reflexivity.
Defined.

(* "Lemma 3.11.4. For any type A, the type isContr(A) is a mere
    proposition." *)

Definition hott_3_11_4 A : isProp (isContr A).
Proof.
intros c c'.
assert (isProp A) as r by (apply isContr_isProp; assumption).
destruct c as (a, p).
destruct c' as (a', p').
set (q := p a').
apply (pair_eq q).
unfold transport.
destruct q; unfold id.
apply isProp_isSet in r.
apply Π_type.funext; intros x; apply r.
Defined.

(* "Corollary 3.11.5. If A is contractible, then so is isContr(A)." *)

Definition hott_3_11_5 A : isContr A → isContr (isContr A).
Proof.
intros c.
apply hott_3_11_3_iii_i, hott_3_11_3_ii_iii.
split; [ apply hott_3_11_4 | ].
exists c; constructor.
Defined.

(* "Lemma 3.11.6. If P : A → U is a type family such that each P(a)
    is contractible, then ∏ (x:A) P(x) is contractible." *)

Definition hott_3_11_6 {A P} :
  (Π (a : A), isContr (P a)) → isContr (Π (x : A), P x).
Proof.
intros p.
unfold isContr.
exists (λ a, pr₁ (p a)); intros f.
apply Π_type.funext; intros x.
pose proof p x as q.
apply isContr_isProp in q; apply q.
Defined.

(* "Of course, if A is equivalent to B and A is contractible, then so
    is B." *)

Definition equiv_contr {A B} : A ≃ B → isContr A → isContr B.
Proof.
intros p q.
apply hott_3_11_3_i_ii, hott_3_11_3_ii_iii in q.
apply quasi_inv in p.
eapply equiv_compose in q; [ | apply p ].
apply hott_3_11_3_iii_i; assumption.
Defined.

(* "By definition, a *retraction* is a function r : A → B such that
    there exists a function s : B → A, called its *section*, and a
    homotopy : ∏ (y:B) (r(s(y)) = y); then we say that B is a
    *retract* of A." *)

Definition retraction A B :=
  Σ (r : A → B), Σ (s : B → A), Π (y : B), (r (s y) = y).

Definition section {A B} : retraction A B → B → A := λ r, pr₁ (pr₂ r).

Definition retract A : Type := Σ (B : Type), retraction A B.

(* "Lemma 3.11.7. If B is a retract of A, and A is contractible, then
    so is B." *)

Definition hott_3_11_7_tac A B (r : retraction A B) : isContr A → isContr B.
Proof.
intros p.
destruct r as (r, (s, q)).
destruct p as (a₀, p).
exists (r a₀); intros b₀.
eapply compose; [ | apply (q b₀) ].
apply ap, p.
Defined.

Definition hott_3_11_7 A B (r : retraction A B) : isContr A → isContr B
:=
  λ (p : isContr A),
  match r with
  | existT _ r (existT _ s q) =>
      match p with
      | existT _ a₀ p =>
          existT (λ b, ∀ b₀, b = b₀) (r a₀) (λ b₀, ap r (p (s b₀)) • q b₀)
      end
  end.

(* "Lemma 3.11.8. For any A and any a : A, the type Σ (x:A) (a = x)
    is contractible." *)

Definition hott_3_11_8 {A} : ∀ a : A, isContr (Σ (x : A), a = x).
Proof.
intros a.
exists (existT _ a (eq_refl a)).
intros (x, p).
destruct p; reflexivity.
Defined.

(* "Lemma 3.11.9. Let P : A → U be a type family.
      (i) If each P(x) is contractible, then ∑(x:A) P(x) is
          equivalent to A.
     (ii) If A is contractible with center a, then ∑(x:A) P(x) is
          equivalent to P(a)." *)

Definition hott_3_11_9_i {A P} :
  (Π (x : A), isContr (P x)) → (Σ (x : A), P x) ≃ A.
Proof.
intros p.
exists pr₁; apply qinv_isequiv.
exists (λ x, existT _ x (pr₁ (p x))).
unfold "◦", "~~", id; simpl.
split; [ reflexivity | intros x ].
destruct x as (a, q); simpl.
apply (pair_eq (eq_refl a)); simpl; unfold id.
assert (isProp (P a)) as H; [ | apply H ].
apply isContr_isProp, p.
Defined.

Definition hott_3_11_9_ii_tac {A P} (p : isContr A) (a := pr₁ p) :
  (Σ (x : A), P x) ≃ P a.
Proof.
subst a; destruct p as (a, p); simpl.
exists (λ q : {x : A & P x}, transport P (p (pr₁ q))⁻¹ (pr₂ q)).
apply qinv_isequiv.
exists (λ q : P a, existT (λ x : A, P x) a (transport P (p a) q)).
unfold "◦", "~~", id; simpl.
split.
 intros x.
 eapply compose; [ apply transport_compose |  ].
 eapply compose; [ apply transport_compat, compose_invert_r | reflexivity ].

 intros (b, q); simpl.
 apply (pair_eq (p b)).
 eapply compose; [ apply transport_compose |  ].
 eapply compose; [ apply transport_compose |  ].
 eapply compose; [ apply transport_compat, compose_assoc |  ].
 eapply compose; [ eapply invert, transport_compose | ].
 set (x := (p b)⁻¹).
 set (y := p b).
 destruct y; simpl; subst x; unfold id.
 eapply (@compose _ _ (transport P (eq_refl a) q)); [ | reflexivity ].
 apply hap, ap, compose_invert_l.
Defined.

Definition hott_3_11_9_ii {A P} (p : isContr A) (a := pr₁ p) :
  (Σ (x : A), P x) ≃ P a
:=
  let _ := pr₁ p in
  match p return (Σ (x : A), P x) ≃ P (pr₁ p) with
  | existT _ a p =>
      existT isequiv
        (λ q, transport P (p (pr₁ q))⁻¹ (pr₂ q))
        (qinv_isequiv (λ q : {x : A & P x}, transport P (p (pr₁ q))⁻¹ (pr₂ q))
           (existT _
              (λ q, existT P a (transport P (p a) q))
              (λ x,
               transport_compose P (p a) (p a)⁻¹ x
               • transport_compat (p a • (p a)⁻¹) (eq_refl a)
                   (compose_invert_r (p a)),
               λ x,
               match x return
                 existT P a
                   (transport P (p a) (transport P (p (pr₁ x))⁻¹ (pr₂ x)))
                 = x
               with
               | existT _ b q =>
                   pair⁼ (p b)
                     (transport_compose P (p a) (p b) (transport P (p b)⁻¹ q)
                      • transport_compose P (p b)⁻¹ (p a • p b) q
                      • transport_compat ((p b)⁻¹ • (p a • p b))
                           ((p b)⁻¹ • p a • p b)
                           (compose_assoc (p b)⁻¹ (p a) (p b))
                      • (transport_compose P ((p b)⁻¹ • p a) (p b) q)⁻¹
                      • match p b as e in (_ = y) return
                          (∀ q,
                           transport P e (transport P ((p y)⁻¹ • p a) q) = q)
                        with
                        | eq_refl _ =>
                            hap (ap (transport P) (compose_invert_l (p a)))
                        end q)
               end)))
  end.

(* "Lemma 3.11.10. A type A is a mere proposition if and only if for
    all x, y : A, the type x =_{A} y is contractible." *)

Definition hott_3_11_10 {A} : isProp A ⇔ ∀ x y : A, isContr (x = y).
Proof.
split; intros p x y; [ | apply p ].
exists (p x y); intros q.
generalize p; intros r.
apply isProp_isSet in p.
apply p.
Defined.

End Contr.

(* "Exercises" *)

(* "Exercise 3.1. Prove that if A ≃ B and A is a set, then so is B." *)

Section ex_3_1.
Import Σ_type.

Definition ex_3_1_tac A B : A ≃ B → isSet A → isSet B.
Proof.
intros AB SA x y p q.
destruct AB as (f, ((g, fg), _)).
apply Π_type.funext in fg.
assert (r : ∀ p, ap id p = transport (λ u, u x = u y) fg (ap (f ◦ g) p)).
 intros t; destruct fg; reflexivity.

 apply (@compose _ _ (ap id p)); [ destruct p; reflexivity | apply invert ].
 apply (@compose _ _ (ap id q)); [ destruct q; reflexivity | ].
 eapply compose; [ apply r | apply invert ].
 eapply compose; [ apply r | apply ap ].
 eapply compose; [ eapply invert | eapply ap_composite ].
 eapply compose; [ | eapply ap_composite ].
 apply ap, SA.
Defined.

Definition ex_3_1 A B : A ≃ B → isSet A → isSet B
:=
  λ (AB : A ≃ B) (SA : isSet A) (x y : B) (p q : x = y),
  match AB with
  | existT _ f (existT _ g fg, _) =>
      let fg := Π_type.funext fg in
      let r t :=
        match fg in (_ = z) return
          (ap z t = transport (λ u : B → B, u x = u y) fg (ap (f ◦ g) t))
        with
        | eq_refl _ =>
            eq_refl
              (transport (λ u : B → B, u x = u y) 
                 (eq_refl (f ◦ g)) (ap (f ◦ g) t))
        end
      in 
      match p return (p = ap id p) with
      | eq_refl _ => eq_refl (ap id (eq_refl x))
      end
      • r p
      • ap (transport (λ u : B → B, u x = u y) fg)
          ((ap_composite g f p)⁻¹
           • (ap (ap f) (SA (g x) (g y) (ap g q) (ap g p)))⁻¹
           • ap_composite g f q)
      • (r q)⁻¹
      • match q return (ap id q = q) with
        | eq_refl _ => eq_refl (ap id (eq_refl x))
        end
  end.

End ex_3_1.

(* "Exercise 3.2. Prove that if A and B are sets, then so is A + B." *)

Section ex_3_2.
Import Σ_type.

Definition ex_3_2 {A B} : isSet A → isSet B → isSet (A + B).
Proof.
intros SA SB x y p q.
destruct x as [x| x].
 destruct y as [y| y]; [ | discriminate p ].
 set (e := @Σ_type2.inl_eq_equiv A B x y).
 set (f := pr₁ e).
 set (g := pr₁ (fst (pr₂ e))).
 assert (r : ∀ p, g (f p) = p).
  intros r; subst f g.
  destruct e as (f, ((g, Hg), (h, Hh))); simpl in *.
  pose proof EqStr.quasi_inv_l_eq_r f g h Hg Hh as H.
  eapply compose; [ apply H | apply Hh ].

  eapply compose; [ eapply invert | apply r ].
  eapply compose; [ eapply invert | apply r ].
  apply ap, SA.

 destruct y as [y| y]; [ discriminate p | ].
 set (e := @Σ_type2.inr_eq_equiv A B x y).
 set (f := pr₁ e).
 set (g := pr₁ (fst (pr₂ e))).
 assert (r : ∀ p, g (f p) = p).
  intros r; subst f g.
  destruct e as (f, ((g, Hg), (h, Hh))); simpl in *.
  pose proof EqStr.quasi_inv_l_eq_r f g h Hg Hh as H.
  eapply compose; [ apply H | apply Hh ].

  eapply compose; [ eapply invert | apply r ].
  eapply compose; [ eapply invert | apply r ].
  apply ap, SB.
Defined.

End ex_3_2.

(* "Exercise 3.3. Prove that if A is a set and B : A → U is a type
    family such that B (x) is a set for all x : A, then ∑ (x:A) B(x)
    is a set." *)

(* already done in 3.1.5 *)
Definition ex_3_3 {A B} : isSet A → (Π (x : A), isSet (B x))
  → isSet (Σ (x : A), B x).
Proof.
intros SA SB.
apply ex_3_1_5_bis; assumption.
Defined.

(* "Exercise 3.4. Show that A is a mere proposition if and only if
    A → A is contractible." *)

Definition ex_3_4 {A} : isProp A ⇔ isContr (A → A).
Proof.
split; intros p.
 exists id; intros f.
 apply Π_type.funext; intros; apply p.

 destruct p as (f, p).
 intros x y.
 set (g := (λ _ : A, x)).
 set (h := (λ _ : A, y)).
 eapply (@compose _ _ (g x)); [ apply eq_refl | destruct (p g) ].
 eapply (@compose _ _ (h x)); [ destruct (p h) | apply eq_refl ].
 apply eq_refl.
Defined.

(* "Exercise 3.5. Show that isProp A ≃ (A → isContr A)." *)

Definition ex_3_5 {A} : isProp A ≃ (A → isContr A).
Proof.
apply hott_3_3_3.
 apply hott_3_3_5_i.

 apply isPropImp, hott_3_11_4.

 intros p a.
 exists a; intros b; apply p.

 intros f x y.
 destruct (f x) as (a, p).
 destruct (f y) as (b, q).
 eapply compose; [ | apply p ].
 eapply compose; [ | apply q ].
 eapply invert, q.
Defined.

(* "Exercise 3.6. Show that if A is a mere proposition, then so is
     A + (¬A). Thus, there is no need to insert a propositional
     truncation in (3.4.1)." *)

Definition ex_3_6 {A} : isProp A → isProp (A + ¬A).
Proof.
intros SA x y.
destruct x as [x| x].
 destruct y as [y| y]; [ apply ap, SA | destruct (y x) ].
 destruct y as [y| y]; [ destruct (x y) | ].
 apply ap, Π_type.funext; intros a; destruct (x a).
Defined.

(* "Exercise 3.7. More generally, show that if A and B are mere
    propositions and ¬(A×B), then A+B is also a mere proposition." *)

Definition ex_3_7 {A B} : isProp A → isProp B → notT (A * B) → isProp (A + B).
Proof.
intros SA SB NAB x y.
destruct x as [x| x].
 destruct y as [y| y]; [ apply ap, SA | destruct (NAB (x, y)) ].
 destruct y as [y| y]; [ destruct (NAB (y, x)) | apply ap, SB ].
Defined.

(* "Exercise 3.8. Assuming that some type isequiv(f) satisfies
    conditions (i)–(iii) of §2.4, show that the type ∥qinv(f)∥
    satisfies the same conditions and is equivalent to isequiv(f)." *)

Section ex_3_8.
Import Σ_type.

Definition ex_3_8_i {A B} (isequiv : (A → B) → Type) :
  equiv_prop isequiv
  → ∀ f : A → B,
    (qinv f → ∥(qinv f)∥) *
    (∥(qinv f)∥ → qinv f) *
    (∀ e₁ e₂ : ∥(qinv f)∥, e₁ = e₂).
Proof.
intros p f.
pose proof p f as H.
destruct H as ((qi, iq), pf).
split; [ | apply PT_eq ].
split; [ apply PT_intro | ].
intros q.
pose proof (PT_rec (qinv f) (isequiv f) qi pf) as r.
destruct r as (h, r).
apply iq, h, q.
Defined.

Definition ex_3_8_ii {A B} (isequiv : (A → B) → Type) :
  equiv_prop isequiv
  → ∀ f : A → B, isequiv f ≃ ∥(qinv f)∥.
Proof.
intros p f.
pose proof p f as H.
destruct H as ((qi, iq), pf).
pose proof ex_3_8_i isequiv p f as H.
destruct H as ((qf, fq), pq).
apply hott_3_3_3.
 intros e₁ e₂; apply pf.

 intros e₁ e₂; apply pq.

 intros r; apply qf, iq, r.

 intros r; apply qi, fq, r.
Defined.

End ex_3_8.

(* "Exercise 3.9. Show that if LEM holds, then the type
    Prop : ≡ ∑ (A:U) isProp(A) is equivalent to 2." *)

Definition uip_refl_True : ∀ p : I = I, p = eq_refl I.
Proof.
intros p; refine (match p with eq_refl _ => _ end); reflexivity.
Defined.

Definition ex_3_9 : LEM → (Σ (A : Type), isProp A) ≃ ℬ.
Proof.
intros lem.
set
  (f := λ p : {A : Type & isProp A},
   match p with
   | existT _ A PA => match lem A PA with inl _ => true | inr _ => false end
   end).
exists f; apply qinv_isequiv.
set
  (g x y :=
   match x return (x = y) with I => match y with I => eq_refl I end end).
set (h (x y : ⊥) := match x return x = y with end).
exists
  (λ b : bool,
   if b then existT (λ A : Type, isProp A) ⊤ g
   else existT (λ A : Type, isProp A) ⊥ h).
unfold "◦", "~~", id; simpl.
split.
 intros b; destruct b; simpl.
  destruct (lem ⊤ g) as [x| x]; [ apply eq_refl | destruct x; constructor ].
  destruct (lem ⊥ h) as [x| x]; [ destruct x | reflexivity ].

 intros (A, PA); simpl.
 destruct (lem A PA) as [a| b].
  assert (p : ⊤ ≃ A) by (apply quasi_inv, hott_3_3_2; [ apply PA | apply a]).
  eapply (Σ_type.pair_eq (ua p)).
  destruct (ua p); simpl; unfold id; simpl.
  apply Π_type.funext; intros x.
  apply Π_type.funext; intros y.
  destruct x, y.
  subst g; simpl.
  set (u := PA I I); simpl in u.
  refine (match u with eq_refl _ => _ end).
  apply eq_refl.

  assert (p : ⊥ ≃ A).
   exists (λ a : ⊥, match a with end); apply qinv_isequiv; exists b.
   unfold "◦", "~~", id.
   split; [ intros a; destruct (b a) | intros x; destruct x ].

   eapply (Σ_type.pair_eq (ua p)).
   destruct (ua p); simpl; unfold id; simpl.
   apply Π_type.funext; intros x; destruct x.
Defined.

(* "Exercise 3.10. Show that if U_{i+1} satisfies LEM, then the
    canonical inclusion Prop_{U_{i}} → Prop_{U+{i+1}} is an
    equivalence." *)

(* don't know how to define Prop_{i} in Coq... *)

(* "Exercise 3.11. Show that it is not the case that for all A : U we
    have ∥A∥ → A. (However, there can be particular types for which
    ∥A∥ → A. Exercise 3.8 implies that qinv (f) is such.)" *)

(* With the recursion principle of ∥A∥ (§3.7) that we defined as
   "PT_rec", we can define the case A≡B and f≡id, resulting on the
   existence of the function g of type isProp A → ∥A∥ → A. Therefore,
   if A is a mere proposition, we indeed have ∥A∥ → A. We named
   this particular case "PT_elim". *)

(* Print PT_rec.
*** [ PT_rec :
∀ (A B : Type) (f : A → B),
isProp B → {g : ∥A∥ → B & ∀ a : A, g (PT_intro a) = f a} ] *)

(* Print PT_elim.
PT_elim =
λ (A : Type) (PA : isProp A), Σ_type.pr₁ (PT_rec A A id PA)
     : ∀ A : Type, isProp A → ∥A∥ → A *)

(* and since ∥qinv f∥ ≃ isequiv f (exercise 3.8), there is a function
   of type ∥qinv f∥ → isequiv f. But by the property (ii) of isequiv
   in §2.4, we have isequiv f → qinv f. So ∥qinv f∥ → qinv f. *)

(* "Exercise 3.12. Show that if LEM holds, then for all A : U we have
    ∥(∥A∥ → A)∥. (This property is a very simple form of the axiom of
    choice, which can fail in the absence of LEM; see [KECA13].)" *)

(* very strange proof; in the case when A is not a mere proposition,
   we artifially create an element of A by the following steps:
   - using LEM to save the opposite of the goal in the hypotheses, as H
   - the new goal is then the contradiction ⊥
   - putting isProp A as new goal by applying notT (isProp A)
   - introducing then x et y as elements of A
   - setting it is a contradiction (exfalso)
   - putting H back as goal
   Since we have values of type A, x and y, in the hypotheses, we can
   prove A, therefore ∥A∥→A, therefore ∥(∥A∥→A)∥. *)

Definition ex_3_12_tac : LEM → ∀ A, ∥(∥A∥ → A)∥.
Proof.
intros lem A.
pose proof hott_3_3_5_i A as PPA.
pose proof lem (isProp A) PPA as H.
destruct H as [PA| NPA]; [ apply PT_intro, PT_elim, PA; assumption | ].
pose proof lem _ (PT_eq (∥A∥ → A)) as H.
destruct H as [H| H]; [ apply H | exfalso ].
apply NPA; intros x y.
exfalso; apply H.
apply PT_intro; intros; apply x.
Defined.

Definition ex_3_12 : LEM → ∀ A, ∥(∥A∥ → A)∥ :=
  λ (lem : LEM) (A : Type),
  match lem (isProp A) (hott_3_3_5_i A) with
  | inl PA => PT_intro (PT_elim PA)
  | inr NPA =>
      match lem ∥(∥A∥ → A)∥ (PT_eq (∥A∥ → A)) with
      | inl H => H
      | inr H =>
          match NPA (λ x y, match H (PT_intro (λ _, x)) with end) with end
      end
  end.

(* "Exercise 3.13. We showed in Corollary 3.2.7 that the following
    naive form of LEM is inconsistent with univalence:
                 Π (A : U) (A + (¬A))
    In the absence of univalence, this axiom is consistent. However,
    show that it implies the axiom of choice (3.8.1)." *)

(* according to hott_3_8_2, AC ≃ AC_3_8_3, but hott_3_8_2 uses ua *)
(* according to AC_equiv_3_8_3_equiv, AC ≃ AC_3_8_3_equiv, but
   AC_equiv_3_8_3_equiv uses AC_3_8_3 that uses ua *)

(* So this exercise, which is said to be in a context where univalence
   is not set, is not allowed to use these lemmas; the definition of
   AC must remain the initial one. *)

Definition ex_3_13_tac : (Π (A : Type), A + notT A) → AC.
Proof.
intros lem.
intros X A P SX SA PXA T.
clear SX SA PXA. (* not used hypotheses *)
apply PT_intro.
exists
   (λ (x : X),
    match lem (Σ (a : A x), P x a) with
    | inl (existT _ a _) => a
    | inr p => match PT_intro_not p (T x) with end
    end).
intros x.
destruct (lem (Σ (a : A x), P x a)) as [(a, p)| p]; [ apply p | ].
destruct (PT_intro_not p (T x)).
Defined.

Definition ex_3_13 : (Π (A : Type), A + notT A) → AC
:=
  λ lem X A P _ _ _ T,
  PT_intro
    (existT (λ g : ∀ x : X, A x, ∀ x : X, P x (g x))
       (λ x : X,
        match lem {a : A x & P x a} with
        | inl (existT _ a _) => a
        | inr p => match PT_intro_not p (T x) return (A x) with end
        end)
       (λ (x : X),
        let s := lem {a : A x & P x a} in
        match s return
          (P x
             match s with
             | inl (existT _ a _) => a
             | inr p => match PT_intro_not p (T x) return (A x) with end
             end)
        with
        | inl (existT _ a p) => p
        | inr p => match PT_intro_not p (T x) with end
        end)).

(* "Exercise 3.14. Show that assuming LEM, the double negation ¬¬A
    has the same universal property as the propositional truncation
    ∥A∥, and is therefore equivalent to it. Thus, under LEM, the
    propositional truncation can be defined rather than taken as a
    separate type former." *)

(*
PT_intro: ∀ A : Type, A → ∥A∥
PT_eq: ∀ A : Type, isProp ∥A∥
PT_rec:
  ∀ (A B : Type) (f : A → B),
  isProp B → Σ (g : ∥A∥ → B), ∀ a : A, g (PT_intro a) = f a
*)

Definition DN_intro {A} : A → notT (notT A).
Proof.
intros a p; destruct (p a).
Defined.

(* no need to LEM, but uses function extensionality *)
Definition DN_eq₀ {A} : isProp (notT (notT A)).
Proof.
intros x y.
apply Π_type.funext; intros a; destruct (x a).
Defined.

Definition DN_eq : LEM → ∀ A : Type, isProp (notT (notT A)).
Proof.
intros lem A x y.
unfold LEM in lem.
destruct (lem _ (hott_3_3_5_i A)) as [p| p].
 apply (isPropNot (isPropNot p)).

Abort. (* blocked; perhaps DN_eq₀ is the only solution? *)

Definition DN_rec : LEM
  → ∀ A B (f : A → B), isProp B
  → Σ (g : notT (notT A) → B), ∀ a, g (DN_intro a) = f a.
Proof.
intros lem A B f PB.
unfold LEM in lem.
destruct (lem _ (hott_3_3_5_i A)) as [PA| NPA].
 destruct (lem A PA) as [a| na].
  exists (λ _, f a).
  intros a'; apply PB.

  exists (λ nna : notT (notT A), match nna na return B with end).
  intros a; destruct (na a).

 destruct (lem B PB) as [b| nb].
  exists (λ _, b).
  intros a; apply PB.

  exfalso; apply NPA; intros a.
  destruct (nb (f a)).
Defined.

Definition ex_3_14 : LEM → ∀ A, notT (notT A) ≃ ∥A∥.
Proof.
intros lem A.
destruct (lem _ (hott_3_3_5_i A)) as [PA| NPA].
 exists (λ p, PT_intro (pr₁ LEM_LDN lem A PA p)); apply qinv_isequiv.
 exists (λ p q, q (Σ_type.pr₁ (PT_rec A A id PA) p)); simpl.
 split; [ intros x; apply PT_eq | ].
 intros f; apply Π_type.funext; intros x; destruct (f x).

 assert (f : notT (notT A) → ∥A∥).
  intros nna.
  apply PT_intro.
  unfold LEM in lem.
  (* wrong if A is not a Prop; cf 3.2.2 *)
Abort.

(* version where hypothesis "isProp A" has been added *)
(* but not satisfactory since when A is a mere proposition, ∥A∥ is
   not interesting at all *)
Definition ex_3_14_not_satis : LEM → ∀ A, isProp A → (notT (notT A) ≃ ∥A∥).
Proof.
intros HLEM A HPA.
exists (λ p, PT_intro (pr₁ LEM_LDN HLEM A HPA p)); apply qinv_isequiv.
exists (λ p q, q (Σ_type.pr₁ (PT_rec A A id HPA) p)); simpl.
split; [ intros x; apply PT_eq | ].
intros f; apply Π_type.funext; intros x; destruct (f x).
Defined.

(* version with naive version of LEM, instead of normal LEM *)
Definition ex_3_14 : (Π (A : Type), A + notT A) → ∀ A, notT (notT A) ≃ ∥A∥.
Proof.
intros lem A.
exists
  (λ nna : notT (notT A),
   PT_intro
     (match lem A with
      | inl a => a
      | inr na => match nna na return A with end
      end)).
apply qinv_isequiv.
exists
  (λ (x : ∥A∥),
   match lem A with
   | inl a => λ (na : notT A), match na a with end
   | inr na => match PT_intro_not na x with end
   end).
unfold "◦", "~~", id; simpl.
split.
 intros x.
 destruct (lem A) as [a| na]; [ apply PT_eq | ].
 destruct (PT_intro_not na x).

 intros nna.
 destruct (lem A) as [a| na]; [ | destruct (nna na) ].
 apply Π_type.funext; intros na; destruct (nna na).
Defined.

(* "Exercise 3.15. Show that if we assume propositional resizing as in
    §3.5, then the type
          Π (P : Prop), (A → P) → P
    has the same universal property as ∥A∥. Thus, we can also define
    the propositional truncation in this case." *)

(*
PT_intro: ∀ A : Type, A → ∥A∥
PT_eq: ∀ A : Type, isProp ∥A∥
PT_rec:
  ∀ (A B : Type) (f : A → B),
  isProp B → Σ (g : ∥A∥ → B), ∀ a : A, g (PT_intro a) = f a
*)

Definition APP A := Π (P : Type), isProp P → (A → P) → P.

Definition APP_intro {A} : A → APP A.
Proof.
intros a P PP p; apply p, a.
Defined.

Definition APP_eq {A} : isProp (APP A).
Proof.
intros f g.
apply Π_type.funext; intros P.
apply Π_type.funext; intros PP.
apply Π_type.funext; intros h.
apply PP.
Defined.

Definition APP_rec {A B} (f : A → B) :
  isProp B → Σ (g : APP A → B), ∀ a : A, g (APP_intro a) = f a.
Proof.
intros PB.
exists (λ (g : APP A), g B PB f).
intros a; apply eq_refl.
Defined.

Definition ex_3_15 {A} : APP A ≃ ∥A∥.
Proof.
exists (λ g : APP A, g ∥A∥ (PT_eq A) (@PT_intro A)).
apply qinv_isequiv.
assert (∥A∥ → APP A) as g.
 intros x P PP i.
 exfalso; revert x.
 pose proof (@APP_rec P P id PP) as R.
 destruct R as (h, R); unfold id in R.
 (* Seems not working; perhaps they are not equivalent? This is indeed
    possible, since the wording of this exercise does not say they are. *)
Abort.

(* "Exercise 3.16. Assuming LEM, show that double negation commutes
    with universal quantification of mere propositions over sets. That
    is, show that if X is a set and each Y(x) is a mere proposition,
    then LEM implies
          (Π (x:X) ¬¬Y(x)) ≃ ¬¬ (Π (x:X) Y(x))
    Observe that if we assume instead that each Y(x) is a set, then
    (3.11.11) becomes equivalent to the axiom of choice (3.8.3)." *)

Section ex_3_16.
Import Σ_type.

Definition ex_3_16_i {X Y} : isSet X → (Π (x : X), isProp (Y x))
  → LEM → (Π (x : X), notT (notT (Y x))) ≃ notT (notT (Π (x : X), Y x)).
Proof.
intros SX PY lem.
apply hott_3_3_3.
 apply ex_3_6_2; intros x; apply isPropNot, isPropNot, PY.

 apply isPropNot, isPropNot, ex_3_6_2, PY.

 intros NNY NY; apply NY; intros x.
 destruct (lem (Y x) (PY x)) as [p| p]; [ apply p | ].
 destruct (NNY x p).

 intros NNY x q; apply q.
 destruct (lem (Y x) (PY x)) as [p| p]; [ apply p | ].
 exfalso; apply NNY; intros r.
 destruct (p (r x)).
Defined.

Definition ex_3_16_ii :
  LEM
  → (∀ X Y, isSet X → (Π (x : X), isSet (Y x))
     → (Π (x : X), notT (notT (Y x))) ≃ notT (notT (Π (x : X), Y x)))
    ≃ AC_3_8_3.
Proof.
intros lem.
(*
assert
  ((∀ X Y, isSet X → (Π (x : X), isSet (Y x))
    → (Π (x : X), notT (notT (Y x))) ≃ notT (notT (Π (x : X), Y x)))
   → AC_3_8_3) as ffff.
 intros p X Y SX SY q.
 destruct (lem _ (PT_eq (∀ x : X, Y x))) as [r| r]; [ apply r | ].
 exfalso; apply r, PT_intro; intro x.
 destruct (lem _ (hott_3_3_5_i (Y x))) as [PY| NPY].
  apply PT_elim; [ apply PY | apply q ].

  assert (s : ∀ x : X, notT (notT (Y x))).
   intros x' nx'.
   apply PT_intro_not in nx'.
   destruct (nx' (q x')).

   pose proof pr₁ (p X Y SX SY) s as t.
   exfalso; apply t; intros u.
   apply r, PT_intro, u.
Show Proof.
*)
exists
  (λ p X Y SX SY q,
   match lem ∥(∀ x : X, Y x)∥ (PT_eq (∀ x : X, Y x)) with
   | inl r => r
   | inr r =>
       match
         (r
            (PT_intro
               (λ x,
                match lem (isProp (Y x)) (hott_3_3_5_i (Y x)) with
                | inl PY => PT_elim PY (q x)
                | inr _ =>
                    match
                      (((pr₁ (p X Y SX SY)
                           (λ x' nx',
                            match PT_intro_not nx' (q x') return ⊥ with end)
                           (λ u, r (PT_intro u)))) : ⊥)
                    with end
                end)))
       with end
   end).
apply qinv_isequiv.
assert
  (AC_3_8_3
   → (∀ X Y, isSet X → (Π (x : X), isSet (Y x))
     → (Π (x : X), notT (notT (Y x))) ≃ notT (notT (Π (x : X), Y x))))
  as gggg.
 intros ac X Y SX SY.
 pose proof ac X Y SX SY as p.
 assert (isProp (∀ x : X, ∥(Y x)∥)) as q.
  apply ex_3_6_2; intros x; apply PT_eq.

  destruct (lem (∀ x : X, ∥(Y x)∥) q) as [r| r].
   pose proof p r as s.
(*
   assert ((∀ x : X, notT (notT (Y x))) → notT (notT (∀ x : X, Y x))) as ffff.
    intros t u; apply u; intros x.
    apply PT_intro_not in u; destruct (u s).
   Show Proof.
*)
   exists (λ _ u, u (λ x, match PT_intro_not u s with end)).
   apply qinv_isequiv.
(*
   assert (notT (notT (∀ x : X, Y x)) → (∀ x : X, notT (notT (Y x)))) as ffff.
    intros t x u; apply u.
    apply PT_intro_not in u; destruct (u (r x)).
   Show Proof.
*)
   exists (λ _ x u, u (match PT_intro_not u (r x) with end)).
   unfold "◦", "~~", id; simpl.
   split.
    intros x; apply Π_type.funext; intros nx; destruct (x nx).

    intros f; apply Π_type.funext; intros x.
    apply Π_type.funext; intros nx; destruct (f x nx).

   assert ((∀ x : X, notT (notT (Y x))) → notT (notT (∀ x : X, Y x))) as ffff.
    intros t u; apply u; intros x.
    pose proof t x as v.
    exfalso; apply v; intros w.
(* well, the proof seems not trivial; it is perhaps the reason why the
   wording of this exercise says "observe that" instead of "prove that";
   I give up. *)
Abort.

End ex_3_16.

(* "Exercise 3.17. Show that the rules for the propositional
    truncation given in §3.7 are sufficient to imply the following
    induction principle: for any type family B:∥A∥→U such that each
    B(x) is a mere proposition, if for every a:A we have B(|a|), then
    for every x:∥A∥ we have B(x)." *)

Definition ex_3_17 A B : (Π (x : ∥A∥), isProp (B x))
  → (Π (a : A), B (PT_intro a)) → (Π (x : ∥A∥), B x).
Proof.
intros PB BA x.
assert (f : A → B x).
 intros a.
 pose proof BA a as s.
 destruct (PT_eq _ x (PT_intro a)); apply s.

 destruct (PT_rec A (B x) f (PB x)) as (g, s).
 apply g, x.
Defined.

(* "Exercise 3.18. Show that the law of excluded middle (3.4.1) and
    the law of double negation (3.4.2) are logically equivalent." *)

(* already done *)
Definition ex_3_18 : LEM ⇔ LDN.
Proof. apply LEM_LDN. Defined.

(* "Exercise 3.19. Suppose P:ℕ→U is a decidable family of mere
    propositions. Prove that
         ∥Σ (n:ℕ) P(n)∥ → Σ (n:ℕ) P(n)." *)

(* return 0 if not enough iterations, else S n for n *)
Fixpoint first_such_that P (DP : isDecidableFamily ℕ P) m n :=
  match m with
  | 0 => 0
  | S m' =>
      match DP n with
      | inl _ => S n
      | inr _ => first_such_that P DP m' (S n)
      end
  end.

Definition first_such_that_prop P (DP : isDecidableFamily ℕ P) m n a :
  first_such_that P DP (S n) a = S m
  → P m * ∀ b, a ≤ b → b < m → notT (P b).
Proof.
intros p; simpl in p.
destruct (DP a) as [q| q].
 injection p; intros; subst a.
 split; [ apply q | intros b Ha Hb ].
 apply Nat.nlt_ge in Ha; destruct (Ha Hb).

 revert m a p q.
 induction n; intros; [ discriminate p | simpl in p ].
 destruct (DP (S a)) as [r| r].
  injection p; intros; subst m.
  split; [ apply r | intros b Ha Hb ].
  apply Nat.succ_le_mono, Nat.le_antisymm in Hb; [ | apply Ha ].
  destruct Hb; apply q.

  eapply IHn in p; [ | apply r ].
  destruct p as (p, s).
  split; [ apply p | intros b Ha Hb ].
  destruct (le_dec (S a) b) as [t| t].
   apply s; [ apply t | apply Hb ].

   apply Nat.nle_gt in t.
   apply Nat.succ_le_mono, Nat.le_antisymm in t; [ | apply Ha ].
   destruct t; apply q.
Defined.

Definition no_first_such_that_prop P (DP : isDecidableFamily ℕ P) n a :
  first_such_that P DP (S n) a = 0
  → notT (P (a + n)).
Proof.
intros p; simpl in p.
destruct (DP a) as [q| q]; [ discriminate p | ].
revert a p q.
induction n; intros; [ rewrite Nat.add_0_r; apply q | ].
simpl in p.
destruct (DP (S a)) as [r| r]; [ discriminate p | ].
rewrite <- Nat.add_succ_comm.
apply IHn; [ apply p | apply r ].
Defined.

Definition smallest_such_that P : isDecidableFamily ℕ P
  → (Σ (n : ℕ), P n)
  → (Σ (n : ℕ), (P n * ∀ m, m < n → notT (P m))%type).
Proof.
intros DP (n, p).
remember (first_such_that P DP (S n) 0) as x eqn:Hx; symmetry in Hx.
destruct x as [| m].
 apply no_first_such_that_prop in Hx; destruct (Hx p).

 exists m; apply first_such_that_prop in Hx.
 destruct Hx as (q, r); split; [ apply q | intros a Ha ].
 apply r; [ apply Nat.le_0_l | apply Ha ].
Defined.

Definition isProp_first_such_that P (PP : Π (n : ℕ), isProp (P n)) :
  isProp (Σ (n : ℕ), (P n * (∀ m : ℕ, m < n → notT (P m)))%type).
Proof.
intros q r.
destruct q as (m, (pm, q)).
destruct r as (n, (pn, r)).
destruct (lt_eq_lt_dec m n) as [[Hmn| Hmn] | Hmn].
 destruct (r m Hmn pm).

 subst m.
 apply (Σ_type.pair_eq (eq_refl n)); simpl; unfold id.
 apply split_pair_eq.
 split; [ apply PP | ].
 apply Π_type.funext; intros m.
 apply Π_type.funext; intros s.
 apply isPropNot, PP.

 destruct (q n Hmn pn).
Defined.

Definition ex_3_19_tac P : isDecidableFamily ℕ P
  → (Π (n : ℕ), isProp (P n))
  → ∥(Σ (n : ℕ), P n)∥
  → Σ (n : ℕ), P n.
Proof.
intros DP PP p.
set (A := Σ (n : ℕ), P n) in p |-*.
set (B := Σ (n : ℕ), (P n * (∀ m : ℕ, m < n → notT (P m)))%type).
set (f := smallest_such_that P DP : A → B).
set (PB := isProp_first_such_that P PP : isProp B).
set (g := Σ_type.pr₁ (PT_rec A B f PB)).
destruct (g p) as (n, (pn, _)).
exists n; apply pn.
Defined.

Definition ex_3_19 P : isDecidableFamily ℕ P
  → (Π (n : ℕ), isProp (P n))
  → ∥(Σ (n : ℕ), P n)∥
  → Σ (n : ℕ), P n
:=
  λ DP PP p,
  let f := smallest_such_that P DP in
  let PB := isProp_first_such_that P PP in
  match Σ_type.pr₁ (PT_rec _ _ f PB) p with
  | existT _ n (pn, _) => existT P n pn
  end.

(* "Exercise 3.20. Prove Lemma 3.11.9(ii): if A is contractible with
    center a, then Σ (x:A) P(x) is equivalent to P(a)." *)

(* already done: see hott_3_11_9_ii *)

(* "Exercise 3.21. Prove that isProp(P) ≃ (P ≃ ∥P∥)." *)

Definition ex_3_21 P : isProp P ≃ (P ≃ ∥P∥).
Proof.
apply hott_3_3_3.
 apply hott_3_3_5_i.

 intros p q.
 destruct p as (f, p).
 destruct q as (g, q).
 assert (PP : isProp (P → ∥P∥)) by (apply isPropImp, PT_eq).
 assert (f = g) by apply PP; subst g.
 destruct (equivalence_isequiv f) as (r, s).
 assert (p = q) by apply s; subst q.
 reflexivity.

 apply hott_3_9_1.

 intros p q r.
 destruct p as (f, (_, (h, Hh))).
 unfold "◦", "~~", id in Hh.
 eapply compose; [ eapply invert | apply Hh ].
 eapply compose; [ eapply invert | apply Hh ].
 apply ap, PT_eq.
Defined.

(* "Exercise 3.22. As in classical set theory, the finite version of
    the axiom of choice is a theorem. Prove that the axiom of choice
    (3.8.1) holds when X is a finite type Fin(n) (as defined in
    Exercise 1.9)." *)

Definition my_nle_succ_0 : ∀ a, not (S a ≤ 0).
Proof.
intros a ale.
inversion ale.
Defined.

Definition my_le_S_n : ∀ a b, S a ≤ S b → a ≤ b.
Proof.
intros a b p.
induction b.
 inversion p as [| c q r]; [ apply le_n | inversion q ].

 inversion p as [| c q r]; [ apply le_n | apply le_S, IHb, q ].
Defined.

Definition my_lt_1_r : ∀ a, a < 1 → a = 0.
Proof.
intros a alt; unfold lt in alt.
apply my_le_S_n in alt.
destruct a; [ apply eq_refl | inversion alt ].
Defined.

Definition isProp_Fin_1 : isProp (Fin 1).
Proof.
intros (a, p) (b, q).
assert (az : a = 0) by (apply my_lt_1_r, p).
assert (bz : b = 0) by (apply my_lt_1_r, q).
destruct az, bz; apply ap, le_unique.
Defined.

Definition Fin_succ_equiv : ∀ n, Fin (S n) ≃ Fin n + ⊤.
Proof.
intros n.
exists
  (λ (p : Fin (S n)),
   match p with
   | elem _ i _ =>
       match lt_dec i n with
       | left p => inl (elem n i p)
       | right _ => inr I
       end
   end).
apply qinv_isequiv.
exists
  (λ p : Fin n + ⊤,
   match p with
   | inl (elem _ i ilt) => elem (S n) i (Nat.lt_lt_succ_r i n ilt)
   | inr _ => elem (S n) n (Nat.lt_succ_diag_r n)
   end).
unfold "◦", "~~", id; simpl.
split.
 intros [ (i, ilt) | x].
  destruct (lt_dec i n) as [p| p]; [ | destruct (p ilt) ].
  apply ap, ap, le_unique.

  destruct (lt_dec n n) as [p| p]; [ | destruct x; apply eq_refl ].
  exfalso; revert p; apply Nat.lt_irrefl.

 intros (i, ilt).
 destruct (lt_dec i n) as [p| p]; [ apply ap, le_unique | ].
 apply Nat.nlt_ge, Nat.succ_le_mono in p.
 apply Nat.le_antisymm in p; [ | apply ilt ].
 apply Nat.succ_inj in p; subst i.
 apply ap, le_unique.
Defined.

Definition isSet_Fin : ∀ n, isSet (Fin n).
Proof.
intros n.
induction n.
 intros x y p q.
 destruct x as (i, ilt).
 exfalso; clear p q; apply Nat.nlt_0_r in ilt; destruct ilt.

 eapply ex_3_1; [ eapply quasi_inv, Fin_succ_equiv | ].
 eapply ex_3_2; [ apply IHn | apply isSet_True ].
Defined.

Definition ACX X :=
 ∀ (A : X → Type) (P : Π (x : X), (A x → Type)),
  isSet X
  → (Π (x : X), isSet (A x))
  → (Π (x : X), Π (a : A x), isProp (P x a))
  → (Π (x : X), ∥ (Σ (a : A x), P x a) ∥)
  → ∥ (Σ (g : Π (x : X), A x), Π (x : X), P x (g x)) ∥.

Definition ex_3_22_isContr X (CX : isContr X) : ACX X.
Proof.
intros A P SX SA PP T.
destruct CX as (x₀, PX).
pose proof (T x₀) as tx.
set (A₀ := Σ (a : A x₀), P x₀ a).
set (B₀ := ∥(Σ (g : ∀ x : X, A x), ∀ x : X, P x (g x))∥).
assert (f : A₀ → B₀).
 intros t; subst A₀ B₀; apply PT_intro.
 destruct t as (ax, pax).
 set (g (x : X) := eq_rect_r (λ x0 : X, A x0) ax (PX x)⁻¹); simpl in g.
 exists g; subst g; simpl.
 intros x; destruct (PX x); apply pax.

 pose proof (PT_rec A₀ B₀ f (PT_eq _)) as g.
 destruct g as (g, p); apply g, tx.
Defined.

Definition ex_3_22_Fin_1 : ACX (Fin 1).
Proof.
apply ex_3_22_isContr.
exists (elem 1 0 Nat.lt_0_1); intros x.
apply isProp_Fin_1.
Defined.

Definition Fin_2_dec : ∀ x : Fin 2,
  {x = elem 2 0 Nat.lt_0_2} + {x = elem 2 1 Nat.lt_1_2}.
Proof.
intros (i, ilt).
destruct i; [ left; apply ap, le_unique | ].
destruct i; [ right; apply ap, le_unique | ].
exfalso; apply my_le_S_n, my_le_S_n, my_nle_succ_0 in ilt; apply ilt.
Defined.

Definition Fin_3_x₀ :=
  elem 3 0 (Nat.lt_0_succ 2).
Definition Fin_3_x₁ :=
  elem 3 1 (proj1 (Nat.succ_lt_mono 0 2) (Nat.lt_0_succ 1)).
Definition Fin_3_x₂ :=
  elem 3 2 (proj1 (Nat.succ_lt_mono 1 2) (Nat.lt_1_2)).

Definition Fin_3_dec x :
  sumor (sumor (x = Fin_3_x₀) (x = Fin_3_x₁)) (x = Fin_3_x₂).
Proof.
destruct x as (i, ilt).
destruct i; [ left; left; apply ap, le_unique | ].
destruct i; [ left; right; apply ap, le_unique | ].
destruct i; [ right; apply ap, le_unique | ].
pose proof (my_le_S_n (S (S (S i))) 2 ilt) as p.
do 2 apply my_le_S_n in p.
destruct (my_nle_succ_0 i p).
Defined.

Definition PT_and_elim A B : ∥(A * B)∥ → ∥A∥ * ∥B∥.
Proof.
intros p.
split.
 set (q := PT_rec (A * B) ∥A∥ (λ p, PT_intro (fst p)) (PT_eq _)).
 destruct q as (g, q); apply g, p.

 set (q := PT_rec (A * B) ∥B∥ (λ p, PT_intro (snd p)) (PT_eq _)).
 destruct q as (g, q); apply g, p.
Defined.

Definition PT_and_intro A B : ∥A∥ → ∥B∥ → ∥(A * B)∥.
Proof.
intros x y.
assert (f : A → ∥(A * B)∥).
 intros a.
 assert (f : B → ∥(A * B)∥) by (intros b; apply PT_intro; split; assumption).
 set (r := PT_rec B ∥(A * B)∥ f (PT_eq _)).
 destruct r as (g, r); apply g, y.

 set (r := PT_rec A ∥(A * B)∥ f (PT_eq _)).
 destruct r as (g, r); apply g, x.
Defined.

Definition PT_and_equiv A B : ∥(A * B)∥ ≃ ∥A∥ * ∥B∥.
Proof.
apply hott_3_3_3.
 apply PT_eq.

 apply ex_3_6_1; apply PT_eq.

 apply PT_and_elim.

 intros (x, y).
 apply PT_and_intro; assumption.
Defined.

Definition ex_3_22_Fin_2 : ACX (Fin 2).
Proof.
intros A P SX SA PP T.
set (x₀ := elem 2 0 Nat.lt_0_2).
set (x₁ := elem 2 1 Nat.lt_1_2).
set (A₀ := ((Σ (a₀ : A x₀), P x₀ a₀) * (Σ (a₁ : A x₁), P x₁ a₁))%type).
set (B₀ := ∥(Σ (g : ∀ x : Fin 2, A x), ∀ x : Fin 2, P x (g x))∥).
assert (f : A₀ → B₀).
 intros ((a₀, p₀), (a₁, p₁)); subst A₀ B₀; apply PT_intro.
 set
   (g (x : Fin 2) :=
    match Fin_2_dec x with
    | left p =>
        match p in (_ = y) return A y → A x with eq_refl _ => id end a₀
    | right p =>
        match p in (_ = y) return A y → A x with eq_refl _ => id end a₁
    end : A x).
 simpl in g.
 exists g; intros (i, ilt).
 subst g; simpl.
 destruct i.
  destruct (ap (elem 2 0) (le_unique 1 2 ilt Nat.lt_0_2)); apply p₀.

  destruct i.
   destruct (ap (elem 2 1) (le_unique 2 2 ilt Nat.lt_1_2)); apply p₁.

   exfalso; do 2 apply my_le_S_n in ilt; revert ilt; apply my_nle_succ_0.

 pose proof (PT_rec A₀ B₀ f (PT_eq _)) as p.
 destruct p as (g, p).
 apply g; subst A₀.
 apply PT_and_intro; apply T.
Defined.

Definition lt_succ_l_lt m n (p : S n < m) : n < m.
Proof.
apply Nat.lt_succ_l, p.
Defined.

Definition Fin_code n : Fin n → nat := λ x, match x with elem _ m _ => m end.

Definition ex_3_22_Fin_3 : ACX (Fin 3).
Proof.
intros A P SX SA PP T.
set (x₀ := Fin_3_x₀).
set (x₁ := Fin_3_x₁).
set (x₂ := Fin_3_x₂).
set (h x := Σ (a : A x), P x a); simpl in h.
set (A₀ := (h x₀ * h x₁ * h x₂)%type).
set (B₀ := ∥(Σ (g : ∀ x : Fin 3, A x), ∀ x : Fin 3, P x (g x))∥).
assert (f : A₀ → B₀).
 intros (((a₀, p₀), (a₁, p₁)), (a₂, p₂)); subst A₀ B₀; apply PT_intro.
 set
   (g (x : Fin 3) :=
    match Fin_3_dec x with
    | inleft (inleft p) =>
        match p in (_ = y) return A y → A x with eq_refl _ => id end a₀
    | inleft (inright p) =>
        match p in (_ = y) return A y → A x with eq_refl _ => id end a₁
    | inright p =>
        match p in (_ = y) return A y → A x with eq_refl _ => id end a₂
    end : A x).
 simpl in g.
 exists g; intros (i, ilt).
 subst g; simpl.
 destruct i.
bbb.
  destruct (ap (elem 2 0) (le_unique 1 2 ilt Nat.lt_0_2)); apply p₀.

  destruct i.
   destruct (ap (elem 2 1) (le_unique 2 2 ilt Nat.lt_1_2)); apply p₁.

   exfalso; do 2 apply my_le_S_n in ilt; revert ilt; apply my_nle_succ_0.

 pose proof (PT_rec A₀ B₀ f (PT_eq _)) as p.
 destruct p as (g, p).
 apply g; subst A₀.
 apply PT_and_intro; apply T.
Defined.

Fixpoint Fin_and m n (p : n < m) (A : Fin m → Type) (P : ∀ x, A x → Type) :=
  match n return n < m → Type with
  | O => λ _, True
  | S n' =>
      let x := elem m n p in
      λ q,
      (Fin_and m n' (lt_succ_l_lt m n' q) A P * (Σ (a : A x), P x a))%type
  end p.

Fixpoint Fin_or m n (p : n < m) (A : Fin m → Type) (P : ∀ x, A x → Type) :=
  match n return n < m → Type with
  | O => λ _, False
  | S n' =>
      let x := elem m n p in
      λ q,
      (Fin_or m n' (lt_succ_l_lt m n' q) A P + ∥(Σ (a : A x), P x a)∥)%type
  end p.

Definition ex_3_22 n : ACX (Fin n).
Proof.
(*
intros A P SX SA PP T.
revert A P SX SA PP T.
induction n; intros.
 assert (g : ∀ x : Fin 0, A x).
  destruct x as (i, lt); exfalso.
  apply Nat.nlt_0_r in lt; destruct lt.

  apply PT_intro.
  exists g; intros x.
  destruct x as (i, lt); exfalso.
  apply Nat.nlt_0_r in lt; destruct lt.

 set
   (An (x : Fin n) :=
    match x with
    | elem _ i lti => A (elem (S n) i (Nat.lt_lt_succ_r i n lti))
    end).
 set
   (Pn (x : Fin n) :=
    match x return An x → Type with
    | elem _ i ilt => P (elem (S n) i (Nat.lt_lt_succ_r i n ilt))
    end).
 set
   (SAn (x : Fin n) :=
    match x return (isSet (An x)) with
    | elem _ i ilt => SA (elem (S n) i (Nat.lt_lt_succ_r i n ilt))
    end).
 set
   (PPn (x : Fin n) :=
    match x return (∀ a : An x, isProp (Pn x a)) with
    | elem _ i ilt => PP (elem (S n) i (Nat.lt_lt_succ_r i n ilt))
    end).
 set
   (Tn (x : Fin n) :=
    match x return ∥{a : An x & Pn x a}∥ with
    | elem _ i ilt => T (elem (S n) i (Nat.lt_lt_succ_r i n ilt))
    end).
 pose proof (IHn An Pn (isSet_Fin n) SAn PPn Tn) as p.
*)
intros A P SX SA PP T.
apply PT_intro.
revert A P SX SA PP T.
induction n; intros.
 assert (g : ∀ x : Fin 0, A x).
  destruct x as (n, nlt); destruct (Nat.nlt_0_r n nlt).

  exists g; intros x.
  destruct x as (n, nlt); destruct (Nat.nlt_0_r n nlt).

 set (Ao := Fin_or (S n) n (Nat.lt_succ_diag_r n) A P).
 assert (Fin n ≃ Ao).
  assert (Fin n → Ao).
   subst Ao; intros x.
bbb.

   destruct m; [ destruct x as (n, nlt); destruct (Nat.nlt_0_r n nlt) | ].
   simpl; destruct x as (n, nlt).
   destruct (eq_nat_dec n m) as [H1| H1].
    subst n; right.
    set (x := elem (S (S m)) (S m) (Nat.lt_succ_diag_r (S m))).
    apply T.

    left.
bbb.

Definition toto m n (p : n < m) A P : Fin_or m n p A P.

bbb.

  induction n; [ constructor | ].
  rename n into m.
  simpl; split.
   destruct x as (n, nlt).
   destruct (eq_nat_dec n (S m)) as [H₁| H₁].
    subst n.

bbb.
 destruct n.
  apply ex_3_22_Fin_1; assumption.

  destruct n.
   apply ex_3_22_Fin_2; assumption.

bbb.
set (x₀ := elem 2 0 Nat.lt_0_2).
set (x₁ := elem 2 1 Nat.lt_1_2).
set (A₀ := ((Σ (a₀ : A x₀), P x₀ a₀) * (Σ (a₁ : A x₁), P x₁ a₁))%type).
set (B₀ := ∥(Σ (g : ∀ x : Fin 2, A x), ∀ x : Fin 2, P x (g x))∥).
bbb.
