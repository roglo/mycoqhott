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

Tactic Notation "transparent" "assert" "(" ident(H) ":" lconstr(type) ")" :=
 refine (let H := (_ : type) in _).

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

Definition Σ_eq_inv A (x : A) : (Σ (y : A), x = y) ⇔ (Σ (y : A), y = x).
Proof.
split; intros (z, s); exists z; apply invert, s.
Defined.

Definition isProp_Σ_eq_inv A (x : A) :
  isProp (Σ (y : A), y = x) ⇔ isProp (Σ (y : A), x = y).
Proof.
unfold isProp; split; intros P (z, p) (t, q); destruct p, q; reflexivity.
Defined.

Definition Σ_Π_eq_inv A :
  (Σ (x : A), Π (y : A), y = x)
  ⇔ (Σ (x : A), Π (y : A), x = y).
Proof.
split; intros (x, p); exists x; intros y; apply invert, p.
Defined.

Definition isContr_Σ_inv A (x : A) :
  isProp (Σ (y : A), y = x)
  → isContr (Σ (y : A), x = y)
  ⇔ isContr (Σ (y : A), y = x).
Proof.
intros P.
unfold isContr; split; intros (p, q).
 pose proof (fst (Σ_eq_inv _ _) p) as y.
 exists y; intros z; apply P.

 apply isProp_Σ_eq_inv in P.
 pose proof (snd (Σ_eq_inv _ _) p) as y.
 exists y; intros z; apply P.
Defined.

Definition hott_4_1_1 A B (f : A → B) (q : qinv f) :
  qinv f ≃ (Π (x : A), x = x).
Proof.
assert (e : isequiv f) by apply qinv_isequiv, q.
set (fe := existT isequiv f e : A ≃ B); simpl in fe.
remember (ua fe) as p eqn:s .
set (t := (idtoeqv_ua fe)⁻¹ : fe = idtoeqv (ua fe)); simpl in t.
rewrite <- s in t.
destruct p; unfold idtoeqv in t; simpl in t.
subst fe; injection t; clear t; intros t u; subst f.
unfold qinv.
apply (@equiv_compose _ {g : A → A & ((g = id) * (g = id))%type}).
 apply Σ_equiv, Π_type.funext; intros f.
 unfold "◦", "~~"; simpl.
 apply type_pair_eq.
  apply ua.
  exists (λ g, Π_type.funext g).
  apply qinv_isequiv.
  exists (λ g x, Π_type.happly g x).
  unfold "◦", "~~"; simpl.
  split; [ intros p; apply invert, Π_type.funext_prop_uniq_princ |  ].
  intros p; apply Π_type.funext; intros x.
  apply (Π_type.funext_quasi_inverse_of_happly f id p x).

  apply ua.
  exists (λ g, Π_type.funext g).
  apply qinv_isequiv.
  exists (λ g x, Π_type.happly g x).
  unfold "◦", "~~"; simpl.
  split; [ intros p; apply invert, Π_type.funext_prop_uniq_princ |  ].
  intros p; apply Π_type.funext; intros x.
  apply (Π_type.funext_quasi_inverse_of_happly f id p x).

 assert
  (H :
   {g : A → A & ((g = id) * (g = id))%type}
   ≃ Σ (h : Σ (g : A → A), g = @id A), Σ_pr₁ h = @id A).
  eapply equiv_compose; [  | eapply ex_2_10 ]; simpl.
  apply Σ_equiv, Π_type.funext; intros x; apply ua.
  exists (λ p, existT (λ _, x = id) (fst p) (snd p)).
  apply qinv_isequiv.
  exists (λ p : {_ : x = id & x = id}, (Σ_pr₁ p, Σ_pr₂ p)).
  unfold "◦", "~~", id; simpl.
  split; [ intros (p, u); apply eq_refl |  ].
  intros p; apply invert, surjective_pairing.

  eapply equiv_compose; [ apply H | clear H ].
  set (A₀ := {g : A → A & g = id}).
  set (P₀ := λ a : A₀, Σ_pr₁ a = id).
  set
   (c₀ :=
    existT _ (existT (λ g : A → A, g = id) id (eq_refl id))
      (λ x : A₀,
       match x return (existT (λ g : A → A, g = id) id (eq_refl id) = x) with
       | existT _ g p =>
           match p with
           | eq_refl _ =>
               λ _, eq_refl (existT (λ g₀ : A → A, g₀ = g) g (eq_refl g))
           end t
       end)
    :
    isContr A₀).
  simpl in c₀.
  pose proof (@hott_3_11_9_ii A₀ P₀ c₀) as p.
  subst A₀ P₀ c₀; simpl in p.
  eapply equiv_compose; [ apply p |  ].
  exists (λ (p : @id A = @id A) (x : A), Π_type.happly p x).
  apply qinv_isequiv.
  exists (λ g, Π_type.funext g).
  unfold "◦", "~~", id; simpl.
  split.
   intros u.
   apply Π_type.funext; intros x.
   apply (@Π_type.funext_quasi_inverse_of_happly A (λ _, A) id id u x).

   intros u.
   apply invert, Π_type.funext_prop_uniq_princ.
Defined.

(* "Lemma 4.1.2. Suppose we have a type A with a:A and q:a=a such that
        (i) The type a=a is a set.
       (ii) For all x:A we have ∥a=x∥.
      (iii) For all p:a=a we have p•q=q•p

    Then there exists f:Π(x:A)(x=x) with f(a) = q." *)

Section lemma_4_1_2.
Import Σ_type2.

Definition PT_eq_sym A (a b : A) : ∥(a = b)∥ → ∥(b = a)∥.
Proof.
intros p.
apply (PT_rec (a = b) ∥(b = a)∥ (λ p, PT_intro (eq_sym p)) (PT_eq _)), p.
Defined.

Definition PT_imp A B : (A → B) → (∥A∥ → ∥B∥).
Proof.
intros p x.
apply (PT_rec A ∥B∥ (λ a, ╎(p a)╎) (PT_eq _)), x.
Defined.

Definition PT_equiv_imp A B : (A ≃ B) → ∥A∥ → ∥B∥.
Proof.
intros p x.
apply (PT_rec A ∥B∥ (λ a, ╎(Σ_pr₁ p a)╎) (PT_eq _)), x.
Defined.

Definition PT_equiv A B : (A ≃ B) → (∥A∥ ≃ ∥B∥).
Proof.
intros p.
apply hott_3_3_3; [ apply PT_eq | apply PT_eq | | ].
 apply PT_equiv_imp, p.

 apply PT_equiv_imp, quasi_inv, p.
Defined.

Definition hott_4_1_2 A (a : A) (q : a = a) :
  isSet (a = a)
  → (∀ x : A, ∥(a = x)∥)
  → (∀ p : a = a, p • q = q • p)
  → Σ (f : Π (x : A), (x = x)), f a = q.
Proof.
intros Sa g Pc.
assert (Sx : ∀ y, a = y → isSet (a = y)) by (intros; destruct H; apply Sa).
assert (Se : ∀ x y : A, isSet (x = y)).
 intros x y.
 assert (Saxy : (a = x) * (a = y) → isSet (x = y)).
  intros (p, r); destruct p, r; apply Sa.

  assert (Ps : isProp (isSet (x = y))) by apply hott_3_3_5_ii.
  pose proof (PT_rec ((a = x) * (a = y)) (isSet (x = y)) Saxy Ps) as p.
  destruct p as (h, p); apply h, PT_and_intro; apply g.

 set (B (x : A) := Σ (r : x = x), Π (s : a = x), (r = s⁻¹ • q • s) : Type).
 simpl in B.
 assert (u : ∀ x, isProp (B x)).
  intros x.
  assert (v : isProp (isProp (B x))) by apply hott_3_3_5_i.
  assert (f : a = x → isProp (B x)).
   intros p.
   simpl in v; simpl.
   intros (r, h) (r', h').
   pose proof h p as H; subst r.
   pose proof h' p as H; subst r'.
   apply ap, Π_type.funext; intros s.
   apply Se.

   pose proof PT_rec (a = x) (isProp (B x)) f v as p.
   destruct p as (h, p); apply h, g.

  assert (v : Π (x : A), B x).
   intros x.
   assert (f : a = x → B x).
    intros p; unfold B; destruct p.
    exists q; intros s.
    rewrite Pc, <- compose_assoc, compose_invert_l, <- ru.
    apply eq_refl.

    apply (PT_rec (a = x) (B x) f (u x)), g.

   transparent assert (f : ∀ x : A, x = x).
    intros x.
    pose proof v x as p; unfold B in p; simpl in p.
    destruct p as (r, p); apply r.

    exists f; unfold f.
    destruct (v a) as (r, s).
    pose proof s r as H; rewrite H.
    rewrite Pc, <- compose_assoc, compose_invert_l, <- ru.
    apply eq_refl.
Defined.

End lemma_4_1_2.

(* "Theorem 4.1.3. There exist types A and B and a function f : A → B
    such that qinv(f) is not a mere proposition." *)

(* note: very clean proof: its 'Show Proof' generates exactly the next
   definition quasi_inv_eq *)
Definition quasi_inv_eq_tac A B (x y : A ≃ B) : x⁻⁻¹ = y⁻⁻¹ → x = y.
Proof.
intros p.
eapply compose; [ | apply idtoeqv_ua ].
eapply compose; [ eapply invert, idtoeqv_ua | ].
apply ap.
eapply compose; [ | apply hott_2_1_4_iii ].
eapply compose; [ eapply invert, hott_2_1_4_iii | ].
apply (ap invert).
eapply compose; [ | eapply invert, ua_inverse ].
eapply compose; [ eapply ua_inverse | ].
apply ap, p.
Defined.

Definition quasi_inv_eq A B (x y : A ≃ B) : x⁻⁻¹ = y⁻⁻¹ → x = y :=
  λ p,
  (idtoeqv_ua x)⁻¹
  • ap idtoeqv
      ((hott_2_1_4_iii Type A B (ua x))⁻¹
       • ap invert (ua_inverse x • ap ua p • (ua_inverse y)⁻¹)
       • hott_2_1_4_iii Type A B (ua y))
  • idtoeqv_ua y.

Definition isProp_inv A B : isProp (A ≃ B) → isProp (B ≃ A).
Proof.
intros PAB x y.
apply quasi_inv_eq, PAB.
Defined.

Definition bool_equiv_dec p : {p = bool_eq_bool_id} + {p = bool_eq_bool_negb}.
Proof.
transparent assert (t: (bool ≃ bool) ≃ bool); [ apply ex_2_13 | ].
set (f := Σ_type.pr₁ t); simpl in f.
set (h := Σ_type.pr₁ (snd (Σ_type.pr₂ t))); simpl in h.
set (Hh := Σ_type.pr₂ (snd (Σ_type.pr₂ t))).
unfold "◦", "~~", id in Hh.
remember (f p) as u eqn:Hu; symmetry in Hu.
apply (ap h) in Hu.
rewrite Hh in Hu.
destruct u; [ left | right ]; apply Hu.
Defined.

Definition hott_4_1_3 :
  Σ (A : Type), Σ (B : Type), Σ (f : A → B), notT (isProp (qinv f)).
Proof.
(*
hott_4_1_1
     : ∀ (A B : Type) (f : A → B), qinv f → qinv f ≃ (∀ x : A, x = x)
hott_4_1_2
     : ∀ (A : Type) (a : A) (q : a = a),
       isSet (a = a)
       → (∀ x : A, ∥(a = x)∥)
         → (∀ p : a = a, p • q = q • p) → {f : ∀ x : A, x = x & f a = q}
*)

(* "It suffices to exhibit a type X such that Π (x:X) (x = x) is not a
    mere proposition." *)
transparent assert (p : Σ (X : Type), notT (isProp (Π (x : X), x = x))).
 (* "Define X :≡ Σ (A:U) ∥2 = A∥, as in the proof of Lemma 3.8.5." *)
 (* hott_3_8_5
     : {X : Type &
       {Y : X → Type & notT ((∀ x : X, ∥(Y x)∥) → ∥(∀ x : X, Y x)∥)}} *)
 set (X := Σ (A : Type), ∥(ℬ = A)∥).
 (* "It will suffice to exhibit an f : Π (x:X) (x = x) which is
     unequal to λx.refl_x." *)
 assert (f : Π (x : X), x = x).
  (* "Let a : ≡ (2, |refl 2|) : X, ..." *)
  set (a := existT _ ℬ ╎(eq_refl ℬ)╎ : X).
  (* "... and let q : a = a be the path corresponding to the
      nonidentity equivalence e : 2 ≃ 2 defined by e(0₂):≡1₂
      and e(1₂):≡0₂." *)
  set (e := bool_eq_bool_negb).
  transparent assert (q : a = a).
   unfold a; simpl; apply ap.
   apply (compose (y := ╎(ua e)╎)); apply PT_eq.

   simpl in q.
   (* "By definition of X, equalities in subset types (§3.5), and
       univalence, we have (a = a) ≃ (2 ≃ 2), ..." *)
   set (r := equiv_eq_bool_trunc : (a = a) ≃ (ℬ ≃ ℬ)); simpl in r.
   (* "... which is a set, ..." *)
   assert (sa2 : isSet ((a = a) ≃ (ℬ ≃ ℬ))).
    apply ex_3_1_5_bis.
     apply ex_3_1_6; intros; apply isSet_equiv; apply isSet_bool.

     intros; apply isProp_isSet, isProp_isequiv.

    (* "... so (i) holds." *)
    (* reminder: (i) The type a=a is a set.
                (ii) For all x:A we have ∥a=x∥.
               (iii) For all p:a=a we have p•q=q•p *)
    assert (saa : isSet (a = a)).
     eapply ex_3_1; [ eapply quasi_inv, r | ].
     apply isSet_equiv; apply isSet_bool.

     (* "Similarly, by definition of X and equalities in subset types
         we have (ii)." *)
     (* reminder: (ii) For all x:A we have ∥a=x∥. *)
     assert (tax : ∀ x : X, ∥(a = x)∥).
      intros p.
      set (P A := ∥(ℬ = A)∥); simpl in P.
      pose proof hott_3_5_1 Type P (λ A, PT_eq (ℬ = A)) a p as s.
      set (B := Σ_type.pr₁ a = Σ_type.pr₁ p).
      apply (PT_rec B ∥(a = p)∥ (λ p, PT_intro (s p)) (PT_eq _)); unfold B.
      destruct p as (C, BC); apply BC.

      (* "Finally, Exercise 2.13 implies that every equivalence 2≃2
          is equal to either id₂ or e, so we can show (iii) by a
          four-way case analysis." *)
      (* reminder: ex_2_13 : (bool ≃ bool) ≃ bool
                   (iii) For all p:a=a we have p•q=q•p *)
      assert (cpq : ∀ p, p • q = q • p).
       intros p.
       assert (pbb : ∀ p : ℬ ≃ ℬ, {p = bool_eq_bool_id} + {p = e}).
        apply bool_equiv_dec.

        simpl in pbb.
        destruct (pbb (Σ_pr₁ r p)) as [H1 | H1].
bbb.
       transparent assert (aab : (a = a : Type) ≃ ℬ).
        eapply equiv_compose; [ apply r | apply ex_2_13 ].

        set (f := Σ_type.pr₁ aab); simpl in f.
        unfold "◦" in f; simpl in f.
        set (h := snd (Σ_type.pr₂ aab)).
        destruct h as (h, Hh).
        unfold "◦", "~~", id in Hh; simpl in Hh.
        unfold "◦" in Hh; simpl in Hh.
        rewrite <- Hh; rewrite <- Hh at 1.
        apply ap.
        set
          (ss :=
             (@ap _ _
                (existT _ _ ╎(@eq_refl Type bool)╎)
                (existT _ _ ╎(@eq_refl Type bool)╎)
                (@Σ_type.pr₁ _ (λ A, ∥(ℬ = A)∥)) (p • q))).
        simpl in ss.
        set
          (tt :=
             (@ap _ _
                (existT _ _ ╎(@eq_refl Type bool)╎)
                (existT _ _ ╎(@eq_refl Type bool)╎)
                (@Σ_type.pr₁ _ (λ A, ∥(ℬ = A)∥)) (q • p))).
        simpl in tt.
        remember (transport id ss true) as s eqn:Hs.
        remember (transport id tt true) as t eqn:Ht.
        unfold id in s, t.
        destruct s, t.
         apply eq_refl.

         unfold transport in Ht.
         unfold id in Ht.
bbb.
        destruct aab as (f, ((g, Hg), (h, Hh))).
        pose proof EqStr.quasi_inv_l_eq_r f g h Hg Hh as H.
        unfold "◦", "~~", id in Hg, Hh, H.
        rewrite <- Hh; rewrite <- Hh at 1.
        apply ap.
        remember (f (p • q)) as s eqn:Hs.
        remember (f (q • p)) as t eqn:Ht.
        destruct s, t; [ apply eq_refl | | | apply eq_refl ].


bbb.

apply PT_intro, s.
(* on ne peut pas utiliser PT_elim, puisque bool = B n'est pas une prop : en
   effet, on a le contre-exemple avec B ≡ bool, où bool = bool a deux preuves
   différentes *)
bbb.

assert (isProp (a = p)) as u. Focus 2.
pose proof PT_rec (Σ_type.pr₁ a = Σ_type.pr₁ p) (a = p) s u as t.
destruct t as (g, t).

bbb.

Focus 2.
 destruct p as (X, p).
bbb.
 exists X, X, id.
 intros q.
 pose proof hott_4_1_1 X X id as r.
 assert (s : qinv (id (A := X))).
  exists id; unfold "◦", "~~"; simpl.
  split; apply eq_refl.

  pose proof r s as t.
bbb.
