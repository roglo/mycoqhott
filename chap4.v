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
unfold "◦", "∼", id; simpl.
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
  apply Σ_equiv, Π_type.funext; intros x; apply ua.
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

(* "Lemma 4.2.5. For any f:A→B, y:B, and (x,p),(x',p') : fib_f(y),
    we have ((x,p) = (x',p')) ≃ (Σ (γ : x = x') f(γ) • p' = p)" *)

(* they say "The path lemmas in §2.5 yield the following
   characterization of paths in fibers", but it is not §2.5
   but §2.7! *)

Definition fib_intro {A B} (f : A → B) y x (p : f x = y) :=
  (existT (λ z, f z = y) x p : fib f y).

Definition hott_4_2_5_dir {A B} (f : A → B) y x x' p p' :
  (fib_intro f y x p = fib_intro f y x' p')
  → (Σ (γ : x = x'), ap f γ • p' = p).
Proof.
intros q.
apply Σ_type.pair_eq_if in q.
destruct q as (γ, q).
exists γ; destruct γ; simpl in q; destruct q; apply eq_refl.
Defined.

Definition hott_4_2_5_rev {A B} (f : A → B) y x x' p p' :
  (Σ (γ : x = x'), ap f γ • p' = p)
  → (fib_intro f y x p = fib_intro f y x' p').
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
Definition hott_4_2_5 A B (f : A → B) y x x' p p' :
  (fib_intro f y x p = fib_intro f y x' p')
  ≃ (Σ (γ : x = x'), ap f γ • p' = p).
Proof.
eapply equiv_compose; [ apply Σ_type.hott_2_7_2 | simpl ].
apply Σ_equiv, Π_type.funext; intros q.
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
exists (fib_intro f y (g y) (ε y)).
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
apply Σ_equiv, Π_type.funext; intros g; apply ua.
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
apply Σ_equiv, Π_type.funext; intros g; apply ua.
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
    fib_intro g (g y) (f (g y)) (η (g y)) =
    fib_intro g (g y) y (eq_refl (g y)).
Proof.
eapply quasi_inv.
set
  (p y := fib_intro g (g y) (f (g y)) (η (g y)) =
   fib_intro g (g y) y (eq_refl (g y)) : Type).
simpl in p.
change ((∀ y, p y) ≃ lcoh f g η).
assert (q : ∀ y, p y ≃ Σ (γ : f (g y) = y), ap g γ = η (g y)).
 intros y; unfold p.
 eapply equiv_compose; [ apply hott_4_2_5 | ].
 apply Σ_equiv, Π_type.funext; intros q.
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
  Π (x : A),
    fib_intro f (f x) (g (f x)) (ε (f x)) =
    fib_intro f (f x) x (eq_refl (f x)).
Proof.
eapply quasi_inv.
set
  (p x := fib_intro f (f x) (g (f x)) (ε (f x)) =
   fib_intro f (f x) x (eq_refl (f x)) : Type).
simpl in p.
change ((∀ y, p y) ≃ rcoh f g ε).
assert (q : ∀ x, p x ≃ Σ (γ : g (f x) = x), ap f γ = ε (f x)).
 intros x; unfold p.
 eapply equiv_compose; [ apply hott_4_2_5 | ].
 apply Σ_equiv, Π_type.funext; intros q.
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

Definition sigma_comm A B (P : A → B → Type) :
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
 apply Σ_equiv, Π_type.funext; intros g.
 unfold rcoh; apply ua, sigma_comm.

 pose proof (hott_4_2_9 A B f (ishae_qinv A B f p)) as r.
 destruct r as (r, s).
 eapply equiv_contr; [ eapply quasi_inv, q |  ].
 apply isContr_sigma; [ apply r | intros t ].
 unfold isContr in r.
 destruct r as (a, r).
 apply hott_4_2_12, p.
Defined.

bbb.

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
(* well, we must also suppose biinv(f) *)

Definition hott_4_3_2 A B (f : A → B) : biinv f → isProp (biinv f).
Proof.
intros p; unfold biinv.
apply qinv_biinv, hott_4_2_9 in p.
apply isContr_isProp, isContr_prod.
destruct p as (p, q).
split; [ apply q | apply p ].
Defined.

(* "Corollary 4.3.3. For any f : A → B we have biinv(f) ≃ ishae(f)." *)

Definition hott_4_3_3 A B (f : A → B) : biinv f → biinv f ≃ ishae f.
Proof.
intros p.
apply hott_3_3_3.
 apply hott_4_3_2, p.

SearchAbout (isProp (ishae _)).
bbb.
