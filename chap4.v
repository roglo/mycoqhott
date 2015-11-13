(* experimentations on HoTT *)
(* requires coq 8.5 *)

Require Import Utf8 QArith NPeano.
Require Import chap1 chap2 chap3.
Set Universe Polymorphism.

(* no default implicit without arguments *)
Arguments eq_refl [A] x.

Notation "⊥" := False.
Notation "⊤" := True.
Notation "'ℬ'" := (bool : Type).
Notation "A ⇔ B" := ((A → B) * (B → A))%type (at level 100).
Notation "( x , y ) '_{' P }" := (existT P x y)
  (at level 0, format "'[' ( x ,  y ) _{ P } ']'", only parsing).

Open Scope nat_scope.

(* "Chapter 4 - Equivalences" *)

(* "4.1 - Quasi-inverses" *)

(* "Lemma 4.1.1. If f : A → B is such that qinv(f) is inhabited, then
        qinv(f) ≃ (Π (x : A) (x = x). " *)

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
unfold "◦", "∼", id; simpl.
split; intros (x, q); simpl.
 apply (Σ_type.pair_eq (eq_refl _)).
 simpl; unfold id.
 destruct (p x); apply eq_refl.

 apply (Σ_type.pair_eq (eq_refl _)).
 simpl; unfold id.
 destruct (p x); apply eq_refl.
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
  isContr (Σ (y : A), x = y)
  ⇔ isContr (Σ (y : A), y = x).
Proof.
split; intros p.
 generalize p; intros P.
 apply isContr_isProp in P.
 destruct p as (p, q).
 pose proof (fst (Σ_eq_inv _ _) p) as y.
 apply isProp_Σ_eq_inv in P.
 exists y; intros z; apply P.

 generalize p; intros P.
 apply isContr_isProp in P.
 destruct p as (p, q).
 pose proof (snd (Σ_eq_inv _ _) p) as y.
 apply isProp_Σ_eq_inv in P.
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
 apply Σ_equiv; intros f.
 unfold "◦", "∼"; simpl.
 apply type_pair_eq.
  apply ua.
  exists (λ g, Π_type.funext g).
  apply qinv_isequiv.
  exists (λ g x, Π_type.happly g x).
  unfold "◦", "∼"; simpl.
  split; [ intros p; apply invert, Π_type.funext_prop_uniq_princ |  ].
  intros p; apply Π_type.funext; intros x.
  apply (Π_type.funext_quasi_inverse_of_happly f id p x).

  apply ua.
  exists (λ g, Π_type.funext g).
  apply qinv_isequiv.
  exists (λ g x, Π_type.happly g x).
  unfold "◦", "∼"; simpl.
  split; [ intros p; apply invert, Π_type.funext_prop_uniq_princ |  ].
  intros p; apply Π_type.funext; intros x.
  apply (Π_type.funext_quasi_inverse_of_happly f id p x).

 assert
  (H :
   {g : A → A & ((g = id) * (g = id))%type}
   ≃ Σ (h : Σ (g : A → A), g = @id A), Σ_pr₁ h = @id A).
  eapply equiv_compose; [  | eapply ex_2_10 ]; simpl.
  apply Σ_equiv; intros x; apply ua.
  exists (λ p, existT (λ _, x = id) (fst p) (snd p)).
  apply qinv_isequiv.
  exists (λ p : {_ : x = id & x = id}, (Σ_pr₁ p, Σ_pr₂ p)).
  unfold "◦", "∼", id; simpl.
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
  unfold "◦", "∼", id; simpl.
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
unfold "◦", "∼", id in Hh.
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
      assert (pbb : ∀ p : ℬ ≃ ℬ, {p = bool_eq_bool_id} + {p = e}).
       apply bool_equiv_dec.

       transparent assert (aab : (a = a) ≃ ℬ).
        eapply equiv_compose; [ apply r | apply ex_2_13 ].

        set (h := Σ_pr₁ (snd (Σ_pr₂ aab))).
        assert (aad : ∀ p : a = a, {p = h true} + {p = h false}).
         intros p.

(* bon, j'y arrive pas, je laisse tomber temporairement ; il faudra
   que j'y revienne un jour... *)

Abort.

(* "4.2 Half adjoint equivalences" *)

(* "Definition 4.2.1. A function f : A → B is a *half adjoint
    equivalence* if there are g : B → A and homotopies η : g ◦ f ∼
    id_A and ε : f ◦ g ∼ id_B such that there exists a homotopy
          τ : Π (x:A) f(ηx)=ε(fx).
    Thus we have a type ishae(f), defined to be
          Σ (g:B→A) Σ (η:g◦f~id_A) Σ (ε:f◦g~id_B) Π (x:A) f(ηx)=ε(fx)." *)

Definition ishae {A B} f :=
  Σ (g : B → A), Σ (η : g ◦ f ∼ id), Σ (ε : f ◦ g ∼ id),
    Π (x : A), ap f (η x) = ε (f x).

Definition ishae' {A B} f :=
  Σ (g : B → A), Σ (η : g ◦ f ∼ id), Σ (ε : f ◦ g ∼ id),
    Π (y : B), ap g (ε y) = η (g y).

(* "Lemma 4.2.2. For functions f : A → B and g : B → A and homotopies
    η : g ◦ f ∼ id_A and ε : f ◦ g ∼ id_B, the following conditions
    are logically equivalent:
      • Π (x:A) f(ηx)=ε(fx)
      • Π (y:B) g(εy)=η(gy)" *)

Definition hott_4_2_2_one_dir A B (f : A → B) (g : B → A)
  (η : g ◦ f ∼ id) (ε : f ◦ g ∼ id) :
    (Π (x : A), ap f (η x) = ε (f x)) → (Π (y : B), ap g (ε y) = η (g y)).
Proof.
intros τ y.
(* "Using naturality of ε and applying g, we get the following
    commuting diagram of paths:
                       gfg(εy)
               gfgfgy ========= gfgy
                 ||              ||
       g(ε(fgy)) ||              || g(εy)
                 ||              ||
                gfgy =========== gy
                        g(εy)
   " *)
 set (u := ap (g ◦ f ◦ g) (ε y) : (g ◦ f ◦ g ◦ f ◦ g) y = (g ◦ f ◦ g) y).
 set (d := ap g (ε y) : (g ◦ f ◦ g) y = g y); simpl in u, d.
 set (l := ap g (ε ((f ◦ g) y)) : (g ◦ f ◦ g ◦ f ◦ g) y = (g ◦ f ◦ g) y).
 set (r := ap g (ε y) : (g ◦ f ◦ g) y = g y); simpl in l, r.
 assert (ny : u • r = l • d).
  subst u r l d; apply dotr.
  assert (ap (g ◦ f ◦ g) (ε y) = ap (g ◦ (f ◦ g)) (ε y)) by apply eq_refl.
  eapply compose; [ apply H | ].
  eapply compose; [ eapply invert, (ap_composite (f ◦ g) g) | ].
  apply ap, invert, (hott_2_4_4 (f ◦ g) ε).

  (* "Using τ(gy) on the left side of the diagram gives us
                       gfg(εy)
               gfgfgy ========= gfgy
                 ||              ||
       gf(η(gy)) ||              || g(εy)
                 ||              ||
                gfgy =========== gy
                        g(εy)
    " *)
  assert (lη : l = ap (g ◦ f) (η (g y))).
   unfold l, "◦"; rewrite <- (τ (g y)).
   eapply compose; [ apply (@ap_composite A B A) | apply eq_refl ].

   (* "Using the commutativity of η with g◦f (Corollary 2.4.4), we have
                       gfg(εy)
               gfgfgy ========= gfgy
                 ||              ||
        η(gfgy)) ||              || g(εy)
                 ||              ||
                gfgy =========== gy
                        g(εy)
      " *)
   assert (ηl : l = η ((g ◦ f ◦ g) y)).
    apply invert; rewrite lη.
    apply (hott_2_4_4 (g ◦ f) η).

    (* "However, by naturality of η we also have
                       gfg(εy)
               gfgfgy ========= gfgy
                 ||              ||
        η(gfgy)) ||              || η(gy)
                 ||              ||
                gfgy =========== gy
                        g(εy)
       " *)
    (* reminder:
                        f(p)
                f(x) ========== f(y)
                 ||              ||
            H(x) ||              || H(y)
                 ||              ||
                g(x) ========== g(y)
                        g(p)

       Lemma 2.4.3 : H(x) • g(p) = f(p) • H(y)
     *)
    pose proof (hott_2_4_3 (g ◦ f ◦ g) g (λ y, η (g y)) (ε y)) as N.
    rewrite ηl in ny.
    unfold u, r, d in ny.
    eapply compose in N; [ | apply ny ].
    eapply compose_cancel_l, N.
Defined.

Definition hott_4_2_2 A B (f : A → B) (g : B → A)
  (η : g ◦ f ∼ id) (ε : f ◦ g ∼ id) :
    (Π (x : A), ap f (η x) = ε (f x)) ↔ (Π (y : B), ap g (ε y) = η (g y)).
Proof.
split; intros τ; [ intros y | intros x ].
 apply hott_4_2_2_one_dir, τ.

 apply hott_4_2_2_one_dir, τ.
Defined.

(* "Of course, it is obvious that ishae(f) → qinv(f): simply
    forget the coherence datum." *)
(* The "coherence datum" seems to be
     ∀ x : A, ap f (η x) = ε (f x) *)

Definition ishae_qinv A B (f : A → B) : ishae f → qinv f.
Proof.
intros (g, (η, (ε, p))).
exists g; split; [ apply ε | apply η ].
Defined.

(* "Theorem 4.2.3. For any f : A → B we have qinv(f) → ishae(f)." *)

Definition alt_τ A B (f : A → B) (g : B → A)
    (ε : f ◦ g ∼ id) (η : g ◦ f ∼ id)
    (ε' := ((λ b, (ε (f (g b)))⁻¹ • ap f (η (g b)) • ε b) : f ◦ g ∼ id)) :
  ∀ a, ap f (η a) = ε' (f a).
Proof.
intros a; simpl in ε'.
assert (p' : η (g (f a)) = ap g (ap f (η a))).
 rewrite (ap_composite f g (η a)).
 apply (hott_2_4_4 (g ◦ f) η).

 apply (ap (ap f)) in p'.
 apply (dotr (ε (f a))) in p'.
 pose proof (hott_2_4_3 (f ◦ g ◦ f) f (λ x, ε (f x)) (η a)) as q.
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
  apply (ap_composite f (f ◦ g) (η a)).
Defined.

Definition alt_ν A B (f : A → B) (g : B → A)
    (ε : f ◦ g ∼ id) (η : g ◦ f ∼ id)
    (η' := ((λ a : A, (η (g (f a)))⁻¹ • ap g (ε (f a)) • η a) : g ◦ f ∼ id)) :
  ∀ b, ap g (ε b) = η' (g b).
Proof.
intros b; simpl in η'.
assert (p' : ε (f (g b)) = ap f (ap g (ε b))).
 rewrite (ap_composite g f (ε b)).
 apply (hott_2_4_4 (f ◦ g) ε).

 apply (ap (ap g)) in p'.
 apply (dotr (η (g b))) in p'.
 pose proof (hott_2_4_3 (g ◦ f ◦ g) g (λ y, η (g y)) (ε b)) as q.
 unfold id in q; simpl in q; apply invert in q.
 eapply compose in q; [  | eapply compose; [ eapply p' |  ] ].
  unfold η'.
  rewrite <- compose_assoc.
  unfold id, composite in q; simpl.
  unfold id, composite; simpl.
  rewrite q, compose_assoc, compose_invert_l.
  apply invert, hott_2_1_4_i_2.

  apply dotr.
  eapply compose; [ apply (ap_composite f g (ap g (ε b))) |  ].
  apply (ap_composite g (g ◦ f) (ε b)).
Defined.

Definition hott_4_2_3 A B (f : A → B) : qinv f → ishae f.
Proof.
intros (g, (ε, η)).
unfold ishae.
exists g, η.
pose proof alt_τ A B f g ε η as τ.
set (ε' := (λ b, (ε (f (g b)))⁻¹ • ap f (η (g b)) • ε b) : f ◦ g ∼ id) in τ.
simpl in τ.
exists ε'; intros x; apply τ.
Defined.

Definition hott_4_2_3' A B (f : A → B) : qinv f → ishae' f.
Proof.
intros p.
pose proof hott_4_2_3 _ _ _ p as q.
destruct q as (g, (η, (ε, q))).
unfold ishae'; exists g, η, ε.
apply (proj1 (hott_4_2_2 A B f g η ε) q).
Defined.

(* "Definition 4.2.4. The *fiber* of a map f:A→B over a point y:B is
         fib_f(y) := Σ (x : A) (f x = y)." *)

Definition fib {A B} (f : A → B) (y : B) := Σ (x : A), (f x = y).
Definition fib_a {A B} {f : A → B} {y : B} (w : fib f y) := Σ_pr₁ w.
Definition fib_p {A B} {f : A → B} {y : B} (w : fib f y) := Σ_pr₂ w.

(* "Lemma 4.2.5. For any f:A→B, y:B, and (x,p),(x',p') : fib_f(y),
    we have ((x,p) = (x',p')) ≃ (Σ (γ : x = x') f(γ) • p' = p)" *)

(* they say "The path lemmas in §2.5 yield the following
   characterization of paths in fibers", but it is not §2.5
   but §2.7! *)

Definition fib_intro {A B} {f : A → B} {y} x (p : f x = y) :=
  (existT (λ z, f z = y) x p : fib f y).

Definition hott_4_2_5_dir {A B} {f : A → B} {y} x x' (p p' : f _ = y) :
  (fib_intro x p = fib_intro x' p')
  → (Σ (γ : x = x'), ap f γ • p' = p).
Proof.
intros q.
apply Σ_type.pair_eq_if in q.
destruct q as (γ, q).
exists γ; destruct γ; simpl in q; destruct q; apply eq_refl.
Defined.

Definition hott_4_2_5_rev {A B} {f : A → B} {y} x x' (p p' : f _ = y) :
  (Σ (γ : x = x'), ap f γ • p' = p)
  → (fib_intro x p = fib_intro x' p').
Proof.
intros q.
destruct q as (γ, q).
destruct q, γ; apply eq_refl.
Defined.

(*
Definition hott_4_2_5 A B (f : A → B) y x x' p p' :
  (fib_intro f y x p = fib_intro f y x' p')
  ≃ (Σ (γ : x = x'), ap f γ • p' = p).
Proof.
exists (hott_4_2_5_dir f y x x' p p').
apply qinv_isequiv.
exists (hott_4_2_5_rev f y x x' p p').
split.
 unfold "◦", "∼", id; simpl.
 intros (γ, q); simpl.
 destruct q, γ.
 apply eq_refl.

 unfold "◦", "∼", id; simpl.
 intros q; simpl.
 unfold hott_4_2_5_dir; simpl.
 set (u := Σ_type.pair_eq_if A (λ z : A, f z = y) x x' p p' q).
 destruct u as (r, s).
 destruct r; simpl; simpl in s; unfold id in s.
 destruct s.
 unfold fib_intro; simpl.
 unfold fib_intro in q; simpl in q.
 destruct p; simpl in q.
 destruct q.
bbb.
*)

(* well, not using hott_4_2_5_dir and hott_4_2_5_rev defined above,
   because I did not manage to prove their reversivity; so I used
   Σ_type.hott_2_7_2, but I had also to use function extensionality
   and univalence axioms. *)
Definition hott_4_2_5 A B (f : A → B) y x x' (p p' : f _ = y) :
  (fib_intro x p = fib_intro x' p')
  ≃ (Σ (γ : x = x'), ap f γ • p' = p).
Proof.
eapply equiv_compose; [ apply Σ_type.hott_2_7_2 | simpl ].
apply Σ_equiv; intros q.
unfold transport.
destruct q; simpl; unfold id.
apply ua.
exists invert.
apply qinv_isequiv.
exists invert.
unfold "◦", "∼", id.
split; intros z; apply hott_2_1_4_iii.
Defined.

(* "Theorem 4.2.6. If f : A → B is a half adjoint equivalence, then
    for any y : B the fiber fib_f(y) is contractible." *)

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

(* "Definition 4.2.7. Given a function f : A → B, we define the types
         linv(f) :≡ Σ (g : B → A) (g ◦ f ∼ id_A)
         rinv(f) :≡ Σ (g : B → A) (f ◦ g ∼ id_B)
    of *left inverses* and *right inverses* to f, respectively. We
    call f *left invertible* if linv(f) is inhabited, and similarly
    *right invertible* if rinv(f) is inhabited." *)

Definition linv {A B} (f : A → B) := Σ (g : B → A), (g ◦ f ∼ id).
Definition rinv {A B} (f : A → B) := Σ (g : B → A), (f ◦ g ∼ id).

(* "Lemma 4.2.8. If f : A → B has a quasi-inverse, then so do
          (f ◦ -) : (C → A) → (C → B)
          (- ◦ f) : (B → C) → (A → C)." *)

Definition hott_4_2_8 A B C (f : A → B) :
  qinv f → qinv (λ g : C → A, f ◦ g) * qinv (λ g : B → C, g ◦ f).
Proof.
intros p.
split.
 destruct p as (g, (ε, η)).
 exists (λ h c, g (h c)).
 unfold "◦", "∼", id.
 split; intros h; apply Π_type.funext; intros c; [ apply ε | apply η ].

 destruct p as (g, (ε, η)).
 exists (λ (h : A → C) (b : B), h (g b)).
 unfold "◦", "∼", id.
 split; intros; apply Π_type.funext; intros; apply ap; [ apply η | apply ε ].
Defined.

(* "Lemma 4.2.9. If f : A → B has a quasi-inverse, then the types
    rinv(f) and linv(f) are contractible." *)

Definition linv_equiv A B (f : A → B) : linv f ≃ Σ (g : B → A), g ◦ f = id.
Proof.
unfold linv.
apply Σ_equiv; intros g; apply ua.
exists Π_type.funext.
apply qinv_isequiv.
exists Π_type.happly.
split; [ intros x; apply invert, Π_type.funext_prop_uniq_princ | ].
intros p; apply Π_type.funext; intros x.
apply (Π_type.funext_quasi_inverse_of_happly (g ◦ f) id p x).
Defined.

Definition rinv_equiv A B (f : A → B) : rinv f ≃ Σ (g : B → A), f ◦ g = id.
Proof.
unfold rinv.
apply Σ_equiv; intros g; apply ua.
exists Π_type.funext.
apply qinv_isequiv.
exists Π_type.happly.
split; [ intros x; apply invert, Π_type.funext_prop_uniq_princ | ].
intros p; apply Π_type.funext; intros x.
apply (Π_type.funext_quasi_inverse_of_happly (f ◦ g) id p x).
Defined.

Definition hott_4_2_9 A B (f : A → B) :
  qinv f → isContr (rinv f) * isContr (linv f).
Proof.
intros p.
split.
 assert (q : rinv f ≃ Σ (g : B → A), f ◦ g = id) by apply rinv_equiv.
 assert (r : qinv (λ g : B → A, f ◦ g)) by apply hott_4_2_8, p.
 apply hott_4_2_3 in r.
 assert (s : ∀ y, isContr (fib (λ g : B → A, f ◦ g) y)).
  apply hott_4_2_6, r.

  assert (t : isContr (fib (λ g, f ◦ g) id)) by apply s.
  unfold fib in t.
  eapply equiv_contr in t; [ apply t | eapply quasi_inv, q ].

 assert (q : linv f ≃ Σ (g : B → A), g ◦ f = id) by apply linv_equiv.
 assert (r : qinv (λ g : B → A, g ◦ f)) by apply hott_4_2_8, p.
 apply hott_4_2_3 in r.
 assert (s : ∀ y, isContr (fib (λ g : B → A, g ◦ f) y)).
  apply hott_4_2_6, r.

  assert (t : isContr (fib (λ g, g ◦ f) id)) by apply s.
  unfold fib in t.
  eapply equiv_contr in t; [ apply t | eapply quasi_inv, q ].
Defined.

(* "Definition 4.2.10. For f : A → B, a left inverse (g, η) : linv (f),
    and a right inverse (g, ε) : rinv(f), we denote
        lcoh_f(g, η) :≡ Σ (ε : f◦g~id_B) Π (y : B) g(εy) = η(gy)
        rcoh_f(g, ε) :≡ Σ (η : g◦f~id_A) Π (x : A) f(ηx) = ε(fx)." *)

Definition lcoh {A B} (f : A → B) (g : B → A) (η : g ◦ f ∼ id) :=
  Σ (ε : f ◦ g ∼ id), Π (y : B), ap g (ε y) = η (g y).

Definition rcoh {A B} (f : A → B) (g : B → A) (ε : f ◦ g ∼ id) :=
  Σ (η : g ◦ f ∼ id), Π (x : A), ap f (η x) = ε (f x).

(* "Lemma 4.2.11. For any f, g, ε, η, we have
        lcoh_f(g, η) ≃ Π (y : B) (f g y, η (g y)) =_fib_g(gy) (y, refl_gy)
        lcoh_f(g, ε) ≃ Π (x : A) (g f x, ε (f x)) =_fib_f(fx) (x, refl_fx)" *)

Definition pi_equiv_imp_equiv A (f g : A → Type) :
  (Π (x : A), (f x ≃ g x)) → ((∀ x, f x) ≃ (∀ x, g x)).
Proof.
intros p.
exists (λ q x, Σ_pr₁ (p x) (q x)).
apply qinv_isequiv.
exists (λ q x, Σ_pr₁ (p x)⁻⁻¹ (q x)).
split.
 intros r.
 apply Π_type.funext; intros x.
 apply EqStr.quasi_inv_comp_r.

 intros r.
 apply Π_type.funext; intros x.
 apply EqStr.quasi_inv_comp_l.
Defined.

Definition hott_4_2_11_l A B (f : A → B) (g : B → A) (η : g ◦ f ∼ id) :
  lcoh f g η ≃
  Π (y : B),
    fib_intro (f (g y)) (η (g y)) =
    fib_intro y (eq_refl (g y)).
Proof.
eapply quasi_inv.
set
  (p y := fib_intro (f (g y)) (η (g y)) = fib_intro y (eq_refl (g y)) : Type).
simpl in p.
change ((∀ y, p y) ≃ lcoh f g η).
assert (q : ∀ y, p y ≃ Σ (γ : f (g y) = y), ap g γ = η (g y)).
 intros y; unfold p.
 eapply equiv_compose; [ apply hott_4_2_5 | ].
 apply Σ_equiv; intros q.
 rewrite <- ru; apply eq_refl.

 unfold lcoh.
 apply pi_equiv_imp_equiv in q.
 eapply equiv_compose; [ apply q | ].
 transparent assert (ff :
   (Π (y : B), Σ (γ : f (g y) = y), ap g γ = η (g y))
   → Σ (ε : f ◦ g ∼ id), Π (y : B), ap g (ε y) = η (g y)).
  intros r.
  exists (λ y, Σ_pr₁ (r y)); intros y.
  destruct (r y) as (ε, t); apply t.

  exists ff; unfold ff; clear ff; simpl.
  apply qinv_isequiv.
  transparent assert (gg :
    (Σ (ε : f ◦ g ∼ id), Π (y : B), ap g (ε y) = η (g y))
    → Π (y : B), Σ (γ : f (g y) = y), ap g γ = η (g y)).
   intros r y.
   destruct r as (ε, r).
   exists (ε y); apply r.

   exists gg; unfold gg; clear gg; simpl.
   split.
    unfold "◦", "∼", id; simpl.
    intros (ε, r); apply eq_refl.

    unfold "◦", "∼", id; simpl.
    intros r.
    apply Π_type.funext; intros y.
    destruct (r y); apply eq_refl.
Defined.

Definition hott_4_2_11_r A B (f : A → B) (g : B → A) (ε : f ◦ g ∼ id) :
  rcoh f g ε ≃
  Π (x : A), fib_intro (g (f x)) (ε (f x)) = fib_intro x (eq_refl (f x)).
Proof.
eapply quasi_inv.
set
  (p x := fib_intro (g (f x)) (ε (f x)) = fib_intro x (eq_refl (f x)) : Type).
simpl in p.
change ((∀ y, p y) ≃ rcoh f g ε).
assert (q : ∀ x, p x ≃ Σ (γ : g (f x) = x), ap f γ = ε (f x)).
 intros x; unfold p.
 eapply equiv_compose; [ apply hott_4_2_5 | ].
 apply Σ_equiv; intros q.
 rewrite <- ru; apply eq_refl.

 unfold rcoh.
 apply pi_equiv_imp_equiv in q.
 eapply equiv_compose; [ apply q | ].
 transparent assert (ff :
   (Π (x : A), Σ (γ : g (f x) = x), ap f γ = ε (f x))
   → Σ (η : g ◦ f ∼ id), Π (x : A), ap f (η x) = ε (f x)).
  intros r.
  exists (λ x, Σ_pr₁ (r x)); intros x.
  destruct (r x) as (η, t); apply t.

  exists ff; unfold ff; clear ff; simpl.
  apply qinv_isequiv.
  transparent assert (gg :
    (Σ (η : g ◦ f ∼ id), Π (x : A), ap f (η x) = ε (f x))
    → Π (x : A), Σ (γ : g (f x) = x), ap f γ = ε (f x)).
   intros r x.
   destruct r as (η, r).
   exists (η x); apply r.

   exists gg; unfold gg; clear gg; simpl.
   split.
    unfold "◦", "∼", id; simpl.
    intros (η, r); apply eq_refl.

    unfold "◦", "∼", id; simpl; intros r.
    apply Π_type.funext; intros x.
    destruct (r x); apply eq_refl.
Defined.

(* "Lemma 4.2.12. If f is a half adjoint equivalence, then for any
    (g, ε) : rinv(f), the type rcoh_f(g, ε) is contractible." *)

Definition hott_4_2_12 A B (f : A → B) : ishae f
  → ∀ g ε, isContr (rcoh f g ε).
Proof.
intros p g ε.
eapply equiv_contr; [ eapply quasi_inv, hott_4_2_11_r | ].
apply hott_3_11_6; intros a.
apply hott_3_11_10.
apply isContr_isProp, hott_4_2_6, p.
Defined.

(* "Theorem 4.2.13. For any f : A → B, the type ishae(f) is a mere
    proposition." *)

Definition Σ_comm A B (P : A → B → Type) :
  (Σ (x : A), Σ (y : B), P x y) ≃
  (Σ (y : B), Σ (x : A), P x y).
Proof.
exists
  (λ (X : Σ (x : A), Σ (y : B), P x y),
   match X with
   | existT _ x (existT _ y p) => existT _ y (existT _ x p)
   end : Σ (y : B), Σ (x : A), P x y).
apply qinv_isequiv.
exists
  (λ (X : Σ (y : B), Σ (x : A), P x y),
   match X with
   | existT _ y (existT _ x p) => existT _ x (existT _ y p)
   end : Σ (x : A), Σ (y : B), P x y).
split; intros (y, (x, p)); apply eq_refl.
Defined.

Definition isContr_sigma A P :
  isContr A → (∀ x, isContr (P x)) → isContr (Σ (x : A), P x).
Proof.
intros p q.
unfold isContr.
destruct p as (a, p).
exists (existT _ a (Σ_pr₁ (q a))); intros (x, r).
apply (Σ_type.pair_eq (p x)).
destruct (p x); simpl.
destruct (q a) as (s, t); apply t.
Defined.

Definition hott_4_2_13 A B (f : A → B) : isProp (ishae f).
Proof.
apply (pr₁ (Σ_pr₂ (@ex_3_5 (ishae f)))); intros p.
assert (q : ishae f ≃ Σ (u : rinv f), rcoh f (Σ_pr₁ u) (Σ_pr₂ u)).
 eapply equiv_compose; [  | apply ex_2_10 ]; simpl.
 apply Σ_equiv; intros g.
 unfold rcoh; apply ua, Σ_comm.

 pose proof (hott_4_2_9 A B f (ishae_qinv A B f p)) as r.
 destruct r as (r, s).
 eapply equiv_contr; [ eapply quasi_inv, q |  ].
 apply isContr_sigma; [ apply r | intros t ].
 unfold isContr in r.
 destruct r as (a, r).
 apply hott_4_2_12, p.
Defined.

(* "4.3 Bi-invertible maps" *)

(* "Definition 4.3.1. We say f : A → B is bi-invertible if it has both
    a left inverse and a right inverse:
             biinv(f) :≡ linv(f) × rinv(f)." *)

Definition biinv {A B} (f : A → B) := (linv f * rinv f)%type.

Definition qinv_biinv A B (f : A → B) : qinv f ⇔ biinv f.
Proof.
split; intros p.
 unfold qinv in p; unfold biinv, linv, rinv.
 destruct p as (g, (ε, η)).
 split; exists g; [ apply η | apply ε ].

 unfold qinv; unfold biinv, linv, rinv in p.
 destruct p as ((g, p), (h, q)).
 exists g; split; [ | apply p ].
 pose proof EqStr.quasi_inv_l_eq_r f h g q p as H.
 intros y; unfold "∼" in H; unfold "◦".
 rewrite <- H; apply q.
Defined.

Definition isContr_prod A B : isContr A * isContr B → isContr (A * B).
Proof.
intros (p, q).
unfold isContr in p, q; unfold isContr.
destruct p as (a, p).
destruct q as (b, q).
exists (a, b); intros (x, y).
destruct (p x), (q y); apply eq_refl.
Defined.

(* "Theorem 4.3.2. For any f : A → B, the type biinv(f) is a mere
    proposition." *)

Definition hott_4_3_2 A B (f : A → B) : isProp (biinv f).
Proof.
eapply (Σ_pr₁ (pr₁ (Σ_pr₂ ex_3_5))); intros p.
apply qinv_biinv, hott_4_2_9 in p.
apply isContr_prod.
destruct p as (p, q).
split; [ apply q | apply p ].
Defined.

(* "Corollary 4.3.3. For any f : A → B we have biinv(f) ≃ ishae(f)." *)

Definition hott_4_3_3 A B (f : A → B) : biinv f ≃ ishae f.
Proof.
apply hott_3_3_3.
 apply hott_4_3_2.

 apply hott_4_2_13.

 intros q; apply hott_4_2_3, qinv_biinv, q.

 intros q; apply qinv_biinv, ishae_qinv, q.
Defined.

(* "4.4 Contractible fibers" *)

(* "Definition 4.4.1 (Contractible maps). A map f : A → B is
    contractible if for all y : B, the fiber fib_f(y) is
    contractible." *)

Definition isContrMap {A B} (f : A → B) := Π (y : B), isContr (fib f y).

Definition isContrMap_isContr {A} (f : A → True) : isContrMap f → isContr A.
Proof.
intros p.
unfold isContrMap in p.
pose proof p I as q.
simpl in q.
unfold isContr in q; unfold isContr.
destruct q as (y, q).
unfold fib in y.
exists (Σ_pr₁ y).
intros x.
assert (r : f x = I) by (destruct (f x); apply eq_refl).
pose proof q (existT _ x r) as s.
subst y; simpl.
apply eq_refl.
Defined.

(* "Theorem 4.4.3. For any f : A → B we have isContr(f) → ishae(f)." *)

Definition equiv_imp A B : A ≃ B → A → B.
Proof.
intros p q.
apply (Σ_pr₁ p), q.
Defined.

Definition hott_4_4_3 {A B} (f : A → B) : isContrMap f → ishae f.
Proof.
intros P.
set (g y := Σ_pr₁ (Σ_pr₁ (P y))).
set (ε := (λ y, Σ_pr₂ (Σ_pr₁ (P y))) : f ◦ g ∼ id); simpl in ε.
assert (p : rcoh f g ε).
 eapply equiv_imp; [ eapply quasi_inv, hott_4_2_11_r | ].
 intros x.
 set (fib₁ := fib_intro (g (f x)) (ε (f x))).
 set (fib₂ := fib_intro x (eq_refl (f x))).
 apply ((Σ_pr₂ (P (f x)) fib₁)⁻¹ • Σ_pr₂ (P (f x)) fib₂).

 destruct p as (η, p).
 exists g, η, ε; intros x; apply p.
Defined.

(* "Lemma 4.4.4. For any f, the type isContr(f) is a mere proposition." *)

Definition hott_4_4_4 {A B} (f : A → B) : isProp (isContrMap f).
Proof.
pose proof (λ y, hott_3_11_4 (fib f y)) as p.
apply ex_3_6_2 in p; apply p.
Defined.

(* "Theorem 4.4.5. For any f : A → B we have isContr(f) ≃ ishae(f)." *)

Definition ishae_isContrMap {A B} (f : A → B) : ishae f → isContrMap f.
Proof.
intros p y.
apply hott_4_2_6, p.
Defined.

Definition hott_4_4_5 {A B} (f : A → B) : isContrMap f ≃ ishae f.
Proof.
apply hott_3_3_3.
 apply hott_4_4_4.

 apply hott_4_2_13.

 apply hott_4_4_3.

 intros p y; apply hott_4_2_6, p.
Defined.

(* "Corollary 4.4.6. If f : A → B is such that B → isequiv(f), then f
    is an equivalence." *)

Definition hott_4_4_6 A B (f : A → B) : (B → isequiv f) → isequiv f.
Proof.
intros p.
apply qinv_isequiv, ishae_qinv, hott_4_4_5; intros y.
apply hott_4_2_6, hott_4_2_3, isequiv_qinv, p, y.
Defined.

(* "4.5 On the definition of equivalences" *)

(* "4.6 Surjections and embeddings" *)

(* "Definition 4.6.1. Let f : A → B.
    (i) We say f is *surjective* (or a *surjection*.) if for every b : B
        we have ∥fib_f(b)∥.
   (ii) We say f is an *embedding* if for every x, y : A the function
        ap_f : (x =_A y) → (f(x) =_B f(y)) is an equivalence." *)

(* "If A and B are sets, then by Lemma 3.3.3, f is an embedding just
    when
          Π (x, y : A), f(x) =_B f(y) → (x =_A y).       (4.6.2)
    In this case we say that f is *injective*, or an *injection*." *)

Definition isSurjective {A B} (f : A → B) :=
  Π (b : B), ∥(fib f b)∥.
Definition isInjective {A B} (f : A → B) :=
  (isSet A * isSet B * Π (x : A), Π (y : A), (f x = f y) → x = y)%type.

Definition isEmbedding {A B} (f : A → B) :=
  Π (x : A), Π (y : A), (x = y) ≃ (f x = f y).
Definition isSplitSurjection {A B} (f : A → B) :=
  Π (b : B), fib f b.

Definition hott_4_6_2 {A B} (f : A → B) : isInjective f → isEmbedding f.
Proof.
intros ((SA, SB), g) x y.
eapply hott_3_3_3; [ | | apply ap | apply g ]; intros p q; [ apply SA | ].
apply SB.
Defined.

(* "Theorem 4.6.3. A function f : A → B is an equivalence if and only
    if it is both surjective and an embedding." *)

Definition hott_4_6_3 {A B} (f : A → B) :
  isequiv f ⇔ (isSurjective f * isEmbedding f).
Proof.
split; intros p.
 split.
  intros y.
  apply hott_3_9_1.
   apply isContr_isProp, hott_4_2_6, hott_4_2_3, isequiv_qinv, p.

   destruct p as ((g, ε), p); exists (g y); apply ε.

  intros x x'; apply hott_2_11_1, p.

 destruct p as (p, q).
 unfold isSurjective in p.
 unfold isEmbedding in q.
 unfold isequiv.
 split.
(*
  assert (∀ b, isContr (Σ (x : A), (f x = b))).
   intros b.
   pose proof p b as r.
bbb.

   apply PT_elim in r.
    exists r; intros a.
    destruct a as (a, s).
    destruct r.

    destruct r as (a, r).
unfold isContr.

SearchAbout (isProp (fib _ _)).

SearchAbout (isContr (Σ (_ : _), _)).
apply isContr_sigma.
eapply hott_3_11_8.
*)
  assert (g : B → A).
   intros b.
   assert (isContr (Σ (x : A), (f x = b))).
    pose proof p b as r.
    assert (s : isProp (fib f b)).
     intros (x, p') (y, q').
     assert (Σ (r' : x = y), ap f r' = p' • q'⁻¹).

(* "Then since ap f is an equivalence, there exists r : x = y with
    ap_f(r) = p • q⁻¹." *)
assert (isequiv (@ap A B x y f)).
 split.

(* I don't manage to prove it; if it is proved, the proof of isProp works:
   see 'Focus 2' below *)
Abort. (*
  exists (Σ_pr₁ (pr₁ (Σ_pr₂ (q x y)))).
  unfold "◦", "∼", id; intros s.
destruct (q x y).
simpl.
destruct i.
simpl.
destruct s0.
simpl.
destruct x1.
simpl.
bbb.

pose proof (q x y).
set (H := p' • q'⁻¹).
     set (r' := Σ_pr₁ (pr₁ (Σ_pr₂ (q x y))) H).
exists r'.
destruct r'.
simpl.
bbb.

Focus 2.
destruct H as (r', H).
     apply (Σ_type.pair_eq r').
unfold ap in H.
unfold transport.
destruct r'.
unfold id.
destruct p'.
rewrite <- lu in H.
apply (ap invert) in H.
rewrite hott_2_1_4_iii in H.
apply H.
bbb.
*)

(* "Corollary 4.6.4. For any f : A → B we have
       isequiv(f) ≃ (isEmbedding(f) × isSurjective(f))." *)

(* cannot be done while I have not done 4.6.3 *)

Definition hott_4_6_4 {A B} (f : A → B) :
  isequiv f ≃ (isEmbedding f * isSurjective f).
Proof.
Abort.

(* "4.7 Closure properties of equivalences" *)

(* "Theorem 4.7.1 (The 2-out-of-3 property). Suppose f : A → B and g :
    B → C. If any two of f, g, and g ◦ f are equivalences, so is the
    third." *)

Definition composite_cancel_l A B C (f : B → C) (g h : A → B) :
  g ∼ h → f ◦ g ∼ f ◦ h.
Proof. intros p x; unfold "◦"; apply ap, p. Defined.

Definition composite_cancel_r A B C (f g : B → C) (h : A → B) :
  f ∼ g → f ◦ h ∼ g ◦ h.
Proof. intros p x; apply p. Defined.

Definition hott_4_7_1_i A B C (f : A → B) (g : B → C) :
  isequiv (g ◦ f) → isequiv g → isequiv f.
Proof.
intros p q.
(* "(g ◦ f)⁻¹ ◦ g is a quasi-inverse to f." *)
apply isequiv_qinv in p.
destruct p as (Igf, (p₁, p₂)).
apply isequiv_qinv in q.
destruct q as (Ig, (q₁, q₂)).
apply qinv_isequiv.
exists (Igf ◦ g).
split; [ | rewrite <- composite_assoc; apply p₂ ].
assert (H : f ◦ (Igf ◦ g) ∼ Ig ◦ g ◦ f ◦ Igf ◦ g).
 rewrite composite_assoc.
 do 2 apply composite_cancel_r.
 intros x; unfold "◦", "∼" in q₂; unfold "◦".
 rewrite q₂; apply eq_refl.

 transitivity (Ig ◦ g ◦ f ◦ Igf ◦ g); [ apply H | clear H ].
 transitivity (Ig ◦ (g ◦ f ◦ Igf) ◦ g).
  do 2 rewrite composite_assoc; reflexivity.

  intros x; unfold "◦", "∼", id in p₁; unfold "◦".
  rewrite p₁; apply q₂.
Defined.

Definition hott_4_7_1_ii A B C (f : A → B) (g : B → C) :
  isequiv (g ◦ f) → isequiv f → isequiv g.
Proof.
intros p q.
(* "f ◦ (g ◦ f)⁻¹ is a quasi-inverse to g." *)
apply isequiv_qinv in p.
destruct p as (Igf, (p₁, p₂)).
apply isequiv_qinv in q.
destruct q as (If, (q₁, q₂)).
apply qinv_isequiv.
exists (f ◦ Igf).
split; [ rewrite composite_assoc; apply p₁ | ].
assert (H : f ◦ Igf ◦ g ∼ f ◦ Igf ◦ g ◦ f ◦ If).
 do 4 rewrite <- composite_assoc.
 do 2 apply composite_cancel_l.
 intros y; unfold "◦", "∼" in q₁; unfold "◦".
 rewrite q₁; apply eq_refl.

 etransitivity; [ eapply H | clear H ].
 transitivity (f ◦ (Igf ◦ g ◦ f) ◦ If).
  do 2 rewrite composite_assoc; reflexivity.

  intros x; unfold "◦", "∼", id in p₂; unfold "◦".
  rewrite p₂; apply q₁.
Defined.

Definition hott_4_7_1_iii A B C (f : A → B) (g : B → C) :
  isequiv f → isequiv g → isequiv (g ◦ f).
Proof.
intros p q.
apply isequiv_qinv in p.
apply isequiv_qinv in q.
apply qinv_isequiv.
destruct p as (If, (p₁, p₂)).
destruct q as (Ig, (q₁, q₂)).
exists (If ◦ Ig).
split.
 transitivity (g ◦ (f ◦ If) ◦ Ig).
  do 2 rewrite composite_assoc; reflexivity.

  intros x; unfold "◦"; unfold "◦" in p₁; rewrite p₁; apply q₁.

 transitivity (If ◦ (Ig ◦ g) ◦ f).
  do 2 rewrite composite_assoc; reflexivity.

  intros x; unfold "◦"; unfold "◦" in q₂; rewrite q₂; apply p₂.
Defined.

(* "Definition 4.7.2. A function g : A → B is said to be a *retract*
    of a function f : X → Y if there is a diagram
             s      r
          A ---> X ---> A
          |      |      |
        g |    f |      | g
          v      v      v
          B ---> Y ---> B
             s'     r'
    for which there are
      (i) a homotopy R : r ◦ s ∼ id_A.
     (ii) a homotopy R' : r' ◦ s' ∼ id_B.
    (iii) a homotopy L : f ◦ s ∼ s' ◦ g.
     (iv) a homotopy K : g ◦ r ∼ r' ◦ f .
      (v) for every a : A, a path H(a) witnessing the commutativity of
          the square

                     K(s(a))
         g(r(s(a))) ========== r'(f(s(a)))
             ||                     ||
      g(R(a) ||                     || r'(L(a))
             ||                     ||
            g(a) ============= r'(s'(g(a)))
                   R'(g(a))⁻¹
   " *)

Record retract A B {X Y} (f : X → Y) :=
  retract_intro
  { rg : A → B;
    rs : A → X;
    rr : X → A;
    rs' : B → Y;
    rr' : Y → B;
    rR : rr ◦ rs ∼ id;
    rR' : rr' ◦ rs' ∼ id;
    rL : f ◦ rs ∼ rs' ◦ rg;
    rK : rg ◦ rr ∼ rr' ◦ f;
    rH (a : A) : rK (rs a) • ap rr' (rL a) = ap rg (rR a) • (rR' (rg a))⁻¹ }.

Arguments rg [A] [B] [X] [Y] [f] r a.
Arguments rs [A] [B] [X] [Y] [f] r a.
Arguments rr [A] [B] [X] [Y] [f] r a.
Arguments rs' [A] [B] [X] [Y] [f] r a.
Arguments rr' [A] [B] [X] [Y] [f] r a.
Arguments rR [A] [B] [X] [Y] [f] r x.
Arguments rR' [A] [B] [X] [Y] [f] r x.
Arguments rL [A] [B] [X] [Y] [f] r x.
Arguments rK [A] [B] [X] [Y] [f] r x.
Arguments rH [A] [B] [X] [Y] [f] r a.

Definition type_retract_fun_retract {A} (B : chap3.retract A) :
  retract (Σ_type.pr₁ B) ⊤ (λ _ : A, I).
Proof.
unfold chap3.retract, retraction in B.
destruct B as (B, (f, (g, p))); simpl.
assert
  (H : ∀ a : B,
       eq_refl I • ap id (eq_refl I) =
       ap (λ _ : B, I) (p a) • (homotopy_eq_refl id I)⁻¹).
 intros b; simpl; unfold "◦", id.
 rewrite <- ru; destruct (p b); apply eq_refl.
apply
  (retract_intro B ⊤ A ⊤ (λ _, I) (λ _, I) g f id id p (homotopy_eq_refl id)
     (λ _, eq_refl I) (λ _, eq_refl I) H).
Defined.

(* "Lemma 4.7.3. If a function g : A → B is a retract of a function f
    : X → Y, then fib_g(b) is a retract of fib_f(s'(b)) for every b :
    B, where s' : B → Y is as in Definition 4.7.2." *)

Definition hott_4_7_3 A B {X Y} (f : X → Y) (rt : retract A B f) (b : B)
    (g := rg rt) (s' := rs' rt) :
  retract (fib g b) ⊤ (λ _ : fib f (s' b), I).
Proof.
set (s := rs rt).
set (r := rr rt).
set (r' := rr' rt).
set (R := rR rt).
set (R' := rR' rt).
set (L := rL rt).
set (K := rK rt).
set (H := rH rt).
set
  (φ b (u : fib g b) :=
   let a := fib_a u in
   let p := fib_p u in
   fib_intro (s a) (L a • ap s' p)).
set
  (ψ b u :=
   let x := fib_a u in
   let q := fib_p u in
   fib_intro (r x) (K x • ap r' q • R' b) : fib g b).
assert
  (e : ∀ u,
   let a := fib_a u in
   let p := fib_p u in
   ψ b (φ b (fib_intro a p)) =
   fib_intro (r (s a)) (K (s a) • ap r' (L a • ap s' p) • R' b)).
 intros a p; apply eq_refl.

 assert
   (p : Π (b : B), Π (a : A), Π (p : g a = b),
    let u := fib_intro a p in
    ψ b (φ b u) = u).
  intros b₁ a₁ p₁; simpl.
  unfold φ, ψ; simpl; unfold id.
  unfold "◦", "∼", id in R.
  unfold composite; simpl.
  destruct p₁; simpl.
  apply
    (compose
       (y := fib_intro (r (s a₁)) (K (s a₁) • ap r' (L a₁) • R' (g a₁)))).
   apply (Σ_type.pair_eq (eq_refl _)); simpl; unfold id.
   apply dotr, dotl, ap, invert, ru.

   unfold id; rewrite H.
   apply (Σ_type.pair_eq (R a₁)).
   subst R; set (R := rR rt); unfold id.
   unfold "◦", "∼", id in R.
   destruct (R a₁); simpl; unfold id.
   apply compose_invert_l.

  assert (q : Π (b : B), Π (u : fib g b), ψ b (φ b u) = u).
   intros b₁ (a₁, p₁); apply p.

   assert
     (u :
       (∀ a : fib g b,
        eq_refl (((λ _ : fib g b, I) ◦ ψ b) (φ b a))
        • ap id (eq_refl (((λ _ : fib f (s' b), I) ◦ φ b) a)) =
        ap (λ _ : fib g b, I) (q b a) • (homotopy_eq_refl id I)⁻¹)).
    intros u; rewrite <- lu; simpl; unfold id.
    rewrite <- ru; destruct (q b u); apply eq_refl.

    apply
      (retract_intro (fib g b) ⊤ (fib f (s' b)) ⊤ (λ _, I) (λ _, I) (φ b)
         (ψ b) id id (q b) (homotopy_eq_refl id) (λ _, eq_refl _)
         (λ _, eq_refl _) u).
Defined.

(* "Theorem 4.7.4. If g is a retract of an equivalence f, then g is
    also an equivalence." *)

Definition hott_4_7_4 A B {X Y} (f : X → Y) (r : retract A B f)
    (g := rg r) : isequiv f → isequiv g.
Proof.
intros p.
apply isequiv_qinv in p.
pose proof (hott_4_2_3 X Y f p) as ishaef.
unfold qinv in p.
destruct p as (h, (ε, η)).
apply qinv_isequiv.
exists (λ b, rr r (h (rs' r b))).
split.
 unfold "◦", "∼", id; intros b.
 subst g; simpl.
 pose proof (rK r) as p.
 pose proof (rR' r) as q.
 unfold "◦", "∼", id in p, ε, q.
 rewrite p, ε; apply q.

 unfold "◦", "∼", id; intros a.
 assert (t : retraction (fib f (rs' r (g a))) (fib g (g a))).
  assert (q : retract (fib g (g a)) ⊤ (λ _ : fib f (rs' r (g a)), I)).
   apply hott_4_7_3.

   unfold retraction.
   exists (rr q), (rs q); intros y; apply (rR q).

  pose proof (hott_3_11_7 (fib f (rs' r (g a))) (fib g (g a)) t) as p.
  assert (cg : isContr (fib g (g a))) by apply p, hott_4_2_6, ishaef.
  assert (pg : g (rr r (h (rs' r (g a)))) = g a).
   pose proof (rL r) as L.
   pose proof (rR r) as R.
   unfold "◦", "∼", id in L, η, R.
   rewrite <- L, η, R.
   apply eq_refl.

   set (u := fib_intro a (eq_refl (g a))).
   set (v := fib_intro (rr r (h (rs' r (g a)))) pg).
   apply isContr_isProp in cg.
   pose proof (cg u v) as uv.
   subst u v.
   apply hott_4_2_5_dir in uv.
   destruct uv as (γ, _).
   apply invert, γ.
Defined.

(* "given two type families P, Q : A → U, we may refer to a function f
    : Π (x:A) (P(x) → Q(x)) as a *fiberwise map* or a *fiberwise
    transformation*. Such a map induces a function on total spaces:

    Definition 4.7.5. Given type families P, Q : A → U and a map
    f : Π (x:A) P(x) → Q(x), we define

      total (f) :≡ λ w.(pr₁ w, f(pr₁ w, pr₂ w)) : Σ (x:A) P(x) → Σ (x:A) Q(x)
   " *)

Definition total {A} {P Q : A → Type} (f : Π (x : A), P x → Q x)
  : (Σ (x : A), P x) → (Σ (x : A), Q x)
  := λ w, existT _ (Σ_pr₁ w) (f (Σ_pr₁ w) (Σ_pr₂ w)).

(* "Theorem 4.7.6. Suppose that f is a fiberwise transformation
    between families P and Q over a type A and let x : A and v :
    Q(x). Then we have an equivalence
         fib_{total(f)} ((x, v)) ≃ fib_{f(x)} (v)." *)

Definition hott_4_7_6 A (P Q : A → Type) (f : Π (x : A), P x → Q x) (x : A)
    (v : Q x) : fib (total f) (existT _ x v) ≃ fib (f x) v.
Proof.
apply
  (equiv_compose
     (B :=
      Σ (w : Σ (x : A), P x),
      existT _ (Σ_pr₁ w) (f (Σ_pr₁ w) (Σ_pr₂ w)) = existT _ x v)).
 apply eqv_eq_refl.

 eapply
   (equiv_compose
      (B := Σ (a : A), Σ (u : P a), existT _ a (f a u) = existT _ x v)).
  apply quasi_inv.
  apply
   (ex_2_10
      (C:=λ w, existT Q (Σ_pr₁ w) (f (Σ_pr₁ w) (Σ_pr₂ w)) = existT Q x v)).

  eapply
    (equiv_compose
       (B := Σ (a : A), Σ (u : P a), Σ (p : a = x), p⁎ (f a u) = v)).
   apply Σ_equiv; intros y; apply ua.
   apply Σ_equiv; intros q; apply ua.
   apply Σ_type.hott_2_7_2.

   eapply
     (equiv_compose
        (B := Σ (a : A), Σ (p : a = x), Σ (u : P a), p⁎ (f a u) = v)).
    apply Σ_equiv; intros y; apply ua, Σ_comm.

    eapply (equiv_compose (B := Σ (u : P x), f x u = v)).
     (* according to the manual, I was supposed to use
        3.11.8, 3.11.9 and exercise 2.20 here, but I did not
        manage to see how to use them; I proved this directly *)
     transparent assert (h :
      ({a : A & {p0 : a = x & {u : P a & transport Q p0 (f a u) = v}}}
       → {u : P x & f x u = v})).
      intros q.
      destruct q as (a, (q, (u, t))).
      destruct q; exists u; apply t.

      exists h; unfold h; clear h.
      apply qinv_isequiv.
      transparent assert (h :
       ({u : P x & f x u = v}
        → {a : A & {p0 : a = x & {u : P a & transport Q p0 (f a u) = v}}})).
       intros q.
       destruct q as (u, q).
       exists x, (eq_refl x), u; apply q.

       exists h; unfold h; clear h.
       unfold "◦", "∼", id; simpl.
       split; [ intros (u, q); apply eq_refl |  ].
       intros (a, (q, (u, t))); destruct q; apply eq_refl.

     apply eqv_eq_refl.
Defined.

(* "We say that a fiberwise transformation f : Π (x:A) P(x) → Q(x) is
    a *fiberwise equivalence* if each f(x) : P(x) → Q(x) is an
    equivalence." *)

Definition isFiberwiseEquivalence {A P Q} (f : Π (x : A), P x → Q x) :=
  Π (x : A), isequiv (f x).

(* "Theorem 4.7.7. Suppose that f is a fiberwise transformation
    between families P and Q over a type A. Then f is a fiberwise
    equivalence if and only if total(f) is an equivalence." *)

Definition hott_4_7_7 {A P Q} (f : Π (x : A), P x → Q x) :
  isFiberwiseEquivalence f ⇔ isequiv (total f).
Proof.
pose proof (hott_4_7_6 A P Q f) as p.
assert
 (q :
  ∀ (x : A) (v : Q x),
  isContr (fib (total f) (existT _ x v)) ⇔ isContr (fib (f x) v)).
 split; apply equiv_contr; [ apply p | apply quasi_inv, p ].

 assert
  (r :
   (∀ w : Σ (x : A), Q x, isContr (fib (total f) w))
   ⇔ (∀ x v, isContr (fib (f x) v))).
  split; intros r; [ intros x v; apply q, r | intros (a, s); apply q, r ].

  unfold isFiberwiseEquivalence.
  split.
   intros s.
   destruct r as (r₁, r₂).
   assert (hf : ∀ x, ishae (f x)).
    intros x.
    apply hott_4_2_3, isequiv_qinv, s.

    assert (cf : ∀ x v, isContr (fib (f x) v)).
     intros x; apply hott_4_2_6, hf.

     pose proof (r₂ cf) as ct.
     apply qinv_isequiv.
     unfold qinv.
     transparent assert ( g : (∀ x : A, Q x → P x) ).
      intros x qx; apply s, qx.

      simpl in g.
      exists (total g).
      unfold "◦", "∼", id.
      unfold total, g; simpl.
      split; intros (a, t); simpl.
       destruct (s a) as ((h, Hh), (i, Hi)); simpl.
       pose proof (EqStr.quasi_inv_l_eq_r (f a) h i Hh Hi) as H.
       unfold "∼" in H; rewrite <- H.
       unfold "◦" in Hh; rewrite Hh; apply eq_refl.

       destruct (s a) as ((h, Hh), (i, Hi)); simpl.
       unfold "◦" in Hi; rewrite Hi; apply eq_refl.

   intros s.
   destruct r as (r₁, r₂).
   assert (hf : ishae (total f)) by apply hott_4_2_3, isequiv_qinv, s.
   assert (cf : ∀ w, isContr (fib (total f) w)).
    intros x; apply hott_4_2_6, hf.

    pose proof (r₁ cf) as ct; intros a.
    apply qinv_isequiv.
    transparent assert (g : Q a → P a).
     intros qa.
     pose proof ct a qa as cta.
     unfold isContr, fib in cta.
     destruct cta as ((r, u), v); apply r.

     simpl in g; exists g; unfold g; clear g; simpl.
     unfold "◦", "∼", id.
     split; intros.
      destruct (ct a x) as ((u, v), cta); apply v.

      destruct (ct a (f a x)) as ((u, v), cta).
      unfold fib in cta.
      pose proof (cta (existT _ x (eq_refl _))).
      injection H; intros; assumption.
Defined.

(* "4.8 The object classifier" *)

(* "Lemma 4.8.1. For any type family B : A → U, the fiber of
    pr₁ : Σ (x:A) B(x) → A over a : A is equivalent to B(a):
          fib_pr₁(a) ≃ B(a)" *)

Definition hott_4_8_1 A (B : A → Type) (a : A) :
  fib (Σ_pr₁ (B := B)) a ≃ B a.
Proof.
(* their proof...
assert (p : fib (Σ_pr₁ (B := B)) a ≃ Σ (x : A), Σ (b : B x), x = a).
 eapply equiv_compose; [ eapply quasi_inv, ex_2_10 | apply eqv_eq_refl ].

 eapply equiv_compose; [ apply p | clear p ].
 assert (p : (Σ (x : A), Σ (b : B x), x = a) ≃ Σ (x : A), Σ (p : x = a), B x).
  exists
    (λ w, existT _ (Σ_pr₁ w) (existT _ (Σ_pr₂ (Σ_pr₂ w)) (Σ_pr₁ (Σ_pr₂ w)))).
  apply qinv_isequiv.
  exists
    (λ w, existT _ (Σ_pr₁ w) (existT _ (Σ_pr₂ (Σ_pr₂ w)) (Σ_pr₁ (Σ_pr₂ w)))).
  unfold "◦", "∼", id; simpl.
  split; intros (x, (p, q)); apply eq_refl.

  eapply equiv_compose; [ apply p | clear p ].
  transparent assert (f : (Σ (x : A), Σ (_ : x = a), B x) → B a).
   intros (x, (p, q)); destruct p; apply q.

   exists f; unfold f; clear f; simpl.
   apply qinv_isequiv.
   transparent assert (f : B a → (Σ (x : A), Σ (_ : x = a), B x)).
    intros p; apply (existT _ a (existT _ (eq_refl _) p)).

    exists f; unfold f; clear f; simpl.
    unfold "◦", "∼", id; simpl.
    split; [ apply eq_refl | ].
    intros (x, (p, q)); destruct p; apply eq_refl.
*)
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
  unfold "◦", "∼", id.
  split; [ apply eq_refl | ].
  intros ((x, p), q); simpl in q.
  destruct q; apply eq_refl.
Defined.

Definition hott_4_8_2 {A B} (f : A → B) : A ≃ Σ (b : B), fib f b.
Proof.
eapply equiv_compose; [ | apply (Σ_comm _ _ (λ a b, f a = b)) ].
exists (λ a, existT _ a (existT _ (f a) (eq_refl _))).
apply qinv_isequiv; exists Σ_pr₁.
unfold "◦", "∼", id; simpl.
split; [ | intros x; apply eq_refl ].
intros (a, (b, q)); simpl.
destruct q; apply eq_refl.
Defined.

(* "Theorem 4.8.3. For any type B there is an equivalence
       χ : (Σ (A : U) (A → B)) ≃ (B → U)." *)

Definition hott_4_8_3 {B} : (Σ (A : Type), A → B) ≃ (B → Type).
Proof.
set (χ (w : Σ (A : Type), A → B) b := fib (Σ_pr₂ w) b).
set (ψ P := existT _ (Σ (b : B), P b) Σ_pr₁ : Σ (A : Type), A → B).
simpl in ψ.
assert (f : χ ◦ ψ ∼ id).
 intros P; unfold χ, ψ; simpl.
 unfold "◦", "∼", id; simpl.
 apply Π_type.funext; intros b; apply ua.
 transparent assert (f : fib (@Σ_pr₁ _ P) b → P b).
  intros ((y, p), q); simpl in q; destruct q; apply p.

  exists f; unfold f; clear f; simpl; apply qinv_isequiv.
  transparent assert (f : P b → fib (@Σ_pr₁ _ P) b).
   intros p; exists (existT _ b p); apply eq_refl.

   exists f; unfold f; clear f.
   unfold "◦", "∼", id; simpl.
   split; [ intros; apply eq_refl | ].
   intros ((y, p), q); simpl in q; simpl.
   destruct q; apply eq_refl.

 assert (g : ψ ◦ χ ∼ id).
  clear f; intros (A, f).
  set (e := (hott_4_8_2 f)⁻⁻¹).
  assert (p : ∀ b a p, Σ_pr₁ e (existT _ b (existT _ a p)) = a).
   intros b a p; apply eq_refl.

   assert
     (q : ∀ a,
      Σ_pr₁ (fst (Σ_pr₂ e)) a = existT _ (f a) (existT _ a (eq_refl (f a)))).
    intros a; apply eq_refl.

    apply (Σ_type.pair_eq (ua e)).
    eapply compose; [ apply (@Π_type.hott_2_9_4 _ id _ _ _ (ua e)) | ].
    unfold id at 1.
    apply Π_type.funext; intros a.
    rewrite ua_pcr_inv; simpl.
    destruct (ua e); apply eq_refl.

  simpl.
  exists χ; apply qinv_isequiv; exists ψ.
  split; [ apply f | apply g ].
Defined.

(* "Theorem 4.8.4. Let f : A → B be a function. Then the diagram
                  θ_f
               A ----→ U•
               |       |
             f |       | pr₁
               ↓       ↓
               B ----→ U
                  χ_g

    is a pullback square (see Exercise 2.11). Here the function θ_f is
    defined by
          λa. (fib_f (f(a)), (a, refl_{f(a)}))." *)

Definition equiv_fib A B (f : A → B) : A ≃ Σ (b : B), fib f b.
Proof.
transparent assert (g : A → Σ (b : B), fib f b).
 intros a; exists (f a), a; apply eq_refl.

 exists g; unfold g; clear g; apply qinv_isequiv.
 transparent assert (g : (Σ (b : B), fib f b) → A).
  intros (b, (a, p)); apply a.

  exists g; unfold g; clear g.
  unfold "◦", "∼", id; simpl.
  split; [ | apply eq_refl ].
  intros (b, (a, p)); destruct p; apply eq_refl.
Defined.

Definition ΣΣΣ_fib A B (f : A → B) :
  A ≃ Σ (b : B), Σ (X : Type), Σ (p : fib f b = X), X.
Proof.
eapply equiv_compose; [ apply (equiv_fib A B f) | ].
apply Σ_equiv; intros b; apply ua.
transparent assert (g : fib f b → {X : Type & {_ : fib f b = X & X}}).
 intros p; exists (fib f b).
 exists (eq_refl _); apply p.

 exists g; unfold g; clear g; apply qinv_isequiv.
 transparent assert (g : {X : Type & {_ : fib f b = X & X}} → fib f b).
  intros (X, (p, x)); destruct p; apply x.

  exists g; unfold g; clear g.
  unfold "◦", "∼", id.
  split; [ | intros; apply eq_refl ].
  intros (X, (p, x)); destruct p; apply eq_refl.
Defined.

Definition ΣΣΣ_fib2 A B (f : A → B) :
  A ≃ Σ (b : B), Σ (X : Type), Σ (x : X), fib f b = X.
Proof.
eapply equiv_compose; [ apply (ΣΣΣ_fib A B f) | ].
apply Σ_equiv; intros b; apply ua.
apply Σ_equiv; intros X; apply ua.
transparent assert (g : {_ : fib f b = X & X} → {_ : X & fib f b = X}).
 intros (p, x); exists x; apply p.

 exists g; unfold g; clear g; apply qinv_isequiv.
 transparent assert (g : {_ : X & fib f b = X} → {_ : fib f b = X & X}).
  intros (x, p); exists p; apply x.

  exists g; unfold g; clear g.
  unfold "◦", "∼", id; simpl.
  split; [ intros (x, p); apply eq_refl | intros (p, x); apply eq_refl ].
Defined.

Definition ΣΣ_fib A B (f : A → B) :
   A ≃ Σ (b : B), Σ (Y : Σ (A : Type), A), fib f b = Σ_pr₁ Y.
Proof.
eapply equiv_compose; [ apply (ΣΣΣ_fib2 A B f) | ].
apply Σ_equiv; intros b; apply ua.
transparent assert
  (g : {X : Type & {_ : X & fib f b = X}}
   → {Y : {A0 : Type & A0} & fib f b = Σ_pr₁ Y}).
 intros (X, (x, p)); exists (existT _ X x); apply p.

 exists g; unfold g; clear g; apply qinv_isequiv.
 transparent assert
   (g : {Y : {A0 : Type & A0} & fib f b = Σ_pr₁ Y}
    → {X : Type & {_ : X & fib f b = X}}).
   intros ((X, x), p); simpl in p; exists X, x; apply p.

   exists g; unfold g; clear g; simpl.
   unfold "◦", "∼", id; simpl.
   split; [ intros ((X, x), p); apply eq_refl | ].
   intros (X, (x, p)); apply eq_refl.
Defined.

Definition hott_4_8_4 A B (f : A → B) :
  let theta (f : A → B) a :=
    existT _ (fib f (f a)) (fib_intro a (eq_refl (f a))) : Σ (B : Type), B
  in
  let khi (w : Σ (A : Type), A → B) b := fib (Σ_pr₂ w) b in
  (∀ x, Σ_pr₁ (theta f x) = khi (existT _ _ f) (f x)) *
  (∀ X, (X → A) ≃ (X → Σ (A : Type), A) * (X → B)).
Proof.
pose proof (ΣΣ_fib A B f) as p.
assert (q : A ≃ B * Σ (C : Type), C).
 eapply equiv_compose; [ apply p | clear p ].
 transparent assert
   (g : {b : B & {Y : {A0 : Type & A0} & fib f b = Σ_pr₁ Y}}
    → B * {C : Type & C}).
  intros (b, ((C, c), p)); simpl in p.
  split; [ apply b | exists C; apply c ].

  exists g; unfold g; clear g; simpl; apply qinv_isequiv.
  transparent assert
    (g : B * {C : Type & C} →
     {b : B & {Y : {A0 : Type & A0} & fib f b = Σ_pr₁ Y}}).
   intros (b, (C, c)).
   exists b, (existT _ B b); simpl.

(* impossible to conclude... something must be wrong somewhere, either
   in my understanding of their proof or... in their proof; there is
   much abuse of language in hott book... *)
Abort.

(* "4.9 Univalence implies function extensionality" *)

(* "Definition 4.9.1. The *weak function extensionality principle*
    asserts that there is a function
       (Π (x : A) isContr(P(x))) → isContr (Π (x : A) P x)
    for any family P : A → U of types over any type A." *)

Definition weak_funext A P :=
  (Π (x : A), isContr (P x)) → isContr (Π (x : A), P x).

(* "Lemma 4.9.2. Assuming U is univalent, for any A, B, X : U and any
    e : A ≃ B, there is an equivalence
          (X → A) ≃ (X → B)
    of which the underlying map is given by post-composition with the
    underlying function of e. *)

Definition hott_4_9_2 A B X (e : A ≃ B) : (X → A) ≃ (X → B).
Proof.
assert (p : Σ (p : A = B), e = idtoeqv p).
 exists (ua e); apply invert, idtoeqv_ua.

 destruct p as (p, ep).
 destruct p; apply eqv_eq_refl.
Defined.

(* "Corollary 4.9.3. Let P : A → U be a family of contractible types,
    i.e. Π (x:A) isContr(P(x)). Then the projection pr₁ : (∑ (x:A)
    P(x)) → A is an equivalence. Assuming U is univalent, it follows
    immediately that post-composition with pr₁ gives an equivalence
        α : (A → Σ (x : A) P(x)) ≃ (A → A)." *)

Definition pre_hott_4_9_3 A (P : A → Type) (p : Π (x : A), isContr (P x)) :
  (Σ (x : A), P x) ≃ A.
Proof.
exists (λ w, Σ_pr₁ w); apply qinv_isequiv.
transparent assert (f : A → (Σ (x : A), P x)).
 intros a; exists a; apply p.

 exists f; unfold f; clear f.
 unfold "◦", "∼", id; simpl.
 split; [ intros; apply eq_refl | ].
 intros (x, q); simpl.
 pose proof p x as r.
 unfold isContr in r.
 destruct r as (r, s).
 assert (t : (let (y, _) := p x in y) = q).
  apply (compose (y := r)); [ apply invert, s | apply s ].

  destruct t; apply eq_refl.
Defined.

Definition equiv_4_9_3 A P := (A → Σ (x : A), P x) ≃ (A → A).

Definition hott_4_9_3 A (P : A → Type) (p : Π (x : A), isContr (P x)) :
  equiv_4_9_3 A P.
Proof.
apply hott_4_9_2.
apply pre_hott_4_9_3, p.
Defined.

Definition hott_4_9_3' A (P : A → Type) (p : Π (x : A), isContr (P x)) :
  (A → Σ (x : A), P x) → (A → A).
Proof.
apply hott_4_9_2.
apply pre_hott_4_9_3, p.
Defined.

(* "Theorem 4.9.4. In a univalent universe U, suppose that P : A → U
    is a family of contractible types and let α be the function of
    Corollary 4.9.3. Then Π (x:A) P(x) is a retract of fib_α (id_A).
    [...]" *)

Definition hott_4_9_4 A (P : A → Type) (p : Π (x : A), isContr (P x))
   (α := hott_4_9_3' A P p) :
  (Π (x : A), P x) ≃ fib α (@id A).
Proof.
set
  (φ (f : Π (x : A), P x) :=
     (existT _ (λ x, existT _ x (f x)) (eq_refl (@id A)) :
      fib (λ (_ : A → {x : A & P x}) (x : A), x) (@id A))).
simpl in φ.
bbb.

set
  (φ (f : Π (x : A), P x) :=
     (existT _ (λ x, existT _ x (f x)) (eq_refl (@id A)) :
      fib  (λ (_ : A → {x : A & P x}) (x0 : A), x0) (@id A))).
simpl in φ.
bbb.

set
  (φ (f : Π (x : A), P x) :=
     (existT _ (λ x, existT _ x (f x)) (eq_refl (@id A)) : fib _ _)).
simpl in φ.
bbb.

transparent assert (φ : (Π (x : A), P x) → fib α (@id A)).
 intros f; exists (λ x, existT _ x (f x)).
 unfold α, hott_4_9_3'; simpl.
bbb.

Definition hott_4_9_4 A (P : A → Type) (p : Π (x : A), isContr (P x))
   (α := hott_4_9_3 A P p) :
  (Π (x : A), P x) ≃ fib (Σ_pr₁ α) (@id A).
Proof.
transparent assert (φ : (Π (x : A), P x) → fib (Σ_pr₁ α) (@id A)).
 intros f; exists (λ x, existT _ x (f x)).
 unfold α, hott_4_9_3; simpl.

bbb.

 unfold α, hott_4_9_3, hott_4_9_2; simpl.
 unfold idtoeqv_ua; simpl.
 destruct (ua (pre_hott_4_9_3 A P p)) at 2.

 unfold α, hott_4_9_3, hott_4_9_2, pre_hott_4_9_3; simpl.

 destruct α as (g, r); simpl.
bbb.

 exists (Σ_pr₁ α).

set (φ f := fib_intro (λ x, existT P x (f x)) (eq_refl (@id A))).
set
  (φ f :=
     (fib_intro (λ x, existT P x (f x)) (eq_refl (@id A)) :
      fib (Σ_pr₁ α) (@id A))).

The term "fib_intro (λ x0 : A, existT P x0 (x x0)) (eq_refl id)" has type
 "fib (λ (x : A → {x : A & P x}) (x0 : A), (let (a, _) := α in a) x x0) id"
while it is expected to have type "fib (Σ_pr₁ α) id" (cannot satisfy
constraint "(let (a, _) := α in a) (λ x : A, existT P x (f x)) x" ==
"x").

bbb.

Definition hott_4_9_4 A (P : A → Type) (p : Π (x : A), isContr (P x))
   (α : (A → Σ (x : A), P x) ≃ (A → A)) :
  (Π (x : A), P x) = chap3.retract (fib (Σ_pr₁ α) (@id A)).
Proof.
pose proof @ua (Π (x : A), P x) (chap3.retract (fib (Σ_pr₁ α) id)).

The term "chap3.retract (fib (Σ_pr₁ α) id)" has type
"Type@{chap3.477}" while it is expected to have type
"Type@{chap2.1031}" (universe inconsistency).

bbb.

apply ua.
pose proof (p a) as q.
apply isContr_isProp in q.
unfold isProp in q.

destruct q as (q, r).

unfold chap3.retract.
unfold retraction.

apply (p a).

Print weak_funext.

bbb.


(* "As a consequence, Π (x:A) P(x) is contractible. In other words,
    the univalence axiom implies the weak function extensionality
    principle." *)
