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
assert (gx : ∀ x (p : a = x), g x = ╎p╎) by (intros; apply PT_eq).
assert (Sx : ∀ y, a = y → isSet (a = y)) by (intros; destruct H; apply Sa).
assert (Se : ∀ x y : A, isSet (x = y)).
 intros x y.
 assert (Ps : ∀ x, isProp (isSet (a = x))) by (intros; apply hott_3_3_5_ii).
 assert (s : ∀ x, a = x → isSet (a = x)) by (intros z p; apply Sx, p).
 set (Sxa x (_ : ∥(a = x)∥) := isSet (a = x)).
 pose proof (ex_3_17 (a = x) (Sxa x) (λ _, Ps x) (s x) (g x)) as ax.
 pose proof (ex_3_17 (a = y) (Sxa y) (λ _, Ps y) (s y) (g y)) as ay.
 subst Sxa; simpl in ax, ay.

 SearchAbout (isSet _ → isSet _).
bbb.

Check (λ x y, ex_3_17 (x = y) (λ u, isSet ∥(x = y)∥) (λ _, (Ps' x y)) (s x y)).
SearchAbout (isSet ∥_∥).
bbb.

Check ex_3_17.
   eapply compose.
    eapply compose; [ eapply invert | apply p ].
    pose proof gx x.
bbb.

   transitivity a.

 assert (xy : ∥(x = y)∥).
  assert (p : ∥((x = a) * (a = y))∥).
   apply PT_and_intro; [ apply PT_eq_sym, g | apply g ].

   eapply PT_imp; [ | apply p ].
   intros (u, v); etransitivity; [ apply u | apply v ].

   assert (Ps : isProp (isSet (x = y))) by (intros; apply hott_3_3_5_ii).
   assert (Pa : isProp (isSet (a = a))) by (intros; apply hott_3_3_5_ii).

(* ex_3_17
     : ∀ (A : Type) (B : ∥A∥ → Type),
       (∀ x : ∥A∥, isProp (B x)) → (∀ a : A, B ╎a╎) → ∀ x : ∥A∥, B x *)

Check ex_3_17.
bbb.

B ≡ λ _, isSet (x = y).
Check (ex_3_17 A (λ _, isSet (x = y)) (λ _, Ps)).

eapply ex_3_17.
bbb.

Check (ex_3_17 A (λ _, isSet (x = y)) (λ _, Ps)).
Check (isSet ∥(a = x)∥).

bbb.

 assert (p : a = x).

(*
set (B (x y : A) := isSet (x = y) : Type).

Check (λ (p : a = x), gz x p).
(* λ p : a = x, gz x p
     : ∀ p : a = x, g x = ╎p╎ *)
Check (λ (q : a = y), gz y q).
(* λ q : a = y, gz y q
     : ∀ q : a = y, g y = ╎q╎ *)
Check (λ (p : a = x) (q : a = y), p⁻¹ • q).
(* λ (p : a = x) (q : a = y), p⁻¹ • q
     : a = x → a = y → x = y *)
Check (λ (p : a = x) (q : a = y), (p, q⁻¹)).
(* λ (p : a = x) (q : a = y), (p, q⁻¹)
     : a = x → a = y → (a = x) * (y = a) *)

 assert (p : (x = y) ≃ (a = a)).
  exists (λ _, eq_refl _); apply qinv_isequiv.
  assert (gggg : (a = a) → (x = y)).
   intros r.
   eapply compose.
    eapply compose; [ eapply invert | apply r ].
    pose proof gz x.

   set (u := λ (p : a = x) (q : a = y), p⁻¹ • q); simpl in u.
   set (u := λ p, h p • (h' p)⁻¹); apply u; clear u.

 assert (f : ∀ y, a = y → isSet (a = y)) by (intros z h; subst z; apply Sa).
 pose proof (PT_rec (a = y) (isSet (a = y)) (f y) (Ps y)) as u.
 pose proof (PT_rec (a = x) (isSet (a = x)) (f x) (Ps x)) as v.
 destruct u as (h, u).
 destruct v as (i, v).
 pose proof (h (g y)) as uu.
 pose proof (i (g x)) as vv.
bbb.
*)

 admit. (* j'y arrive pas, même avec leurs explications *)

 set (B (x : A) := Σ (r : x = x), Π (s : a = x), (r = s⁻¹ • q • s) : Type).
 simpl in B.
 (* "We claim that B (x) is a mere proposition for each x : A." *)
 assert (u : ∀ x, isProp (B x)).
  (* "Since this claim is itself a mere proposition, ..." *)
  assert (v : isProp (∀ x, isProp (B x))).
   apply ex_3_6_2; intros x; apply hott_3_3_5_i.

   (* "... we may again apply induction on truncation and assume that
       g(x) = |p| for some p : a = x." *)
intros x.
Check (g x).
Check ex_3_17.
(* ex_3_17
     : ∀ (A : Type) (B : ∥A∥ → Type),
       (∀ x : ∥A∥, isProp (B x)) → (∀ a : A, B ╎a╎) → ∀ x : ∥A∥, B x *)
bbb.

Check (ex_3_17 (a = x)). (λ p : ∥(a = x)∥,

B₀ (x₀ : ∥A₀∥) ≡ (a = x)

bbb.
set (A₀ := A).
set (B₀ := ∥(a = x)∥).
set (f₀ := g).
Check (PT_rec A₀ B₀ f₀).
bbb.

set (B₀ (_ : ∥A∥) := ∀ x, isProp (B x)).

bbb.

   intros x (r, h) (r', h'); simpl.
   assert (r = r').
    set (u := λ p, h p • (h' p)⁻¹); apply u.

bbb.

set (B₀ := ∀ x, isProp (B x)) in v.
Check (PT_rec A B₀).
assert (f : A → B₀).
 intros x₀; subst B₀; intros y₀.
(*
  ============================
   isProp (B y₀)
*)

(* @ex_3_17
     : ∀ (A : Type) (B : ∥A∥ → Type),
       (∀ x : ∥A∥, isProp (B x)) → (∀ a : A, B ╎a╎) → ∀ x : ∥A∥, B x *)
Check (@ex_3_17 ∥A∥ B).
bbb.

  intros (r, p₀) (t, q₀).
  pose proof (Se x x r t) as u.
  unfold isSet in u.
bbb.

 pose proof (gz x) as p₀.
 pose proof (gz y) as q₀.
bbb.

(* hott_3_3_5_ii
     : ∀ A : Type, isProp (isSet A) *)
(* PT_rec
     : ∀ (A B : Type) (f : A → B),
       isProp B → {g : ∥A∥ → B & ∀ a : A, g ╎a╎ = f a} *)

 assert (u : ∀ z, isSet (a = z)).
  intros z.

 assert (u : ∀ a : isSet (a = y), isSet (x = y)).
  intros a₀.

set (A₀ := isSet (a = x)).
set (B₀ := λ p : ∥A₀∥, isSet (x = y)).
assert (f : ∀ p : ∥A₀∥, isProp (B₀ p)).
 intros p; subst A₀ B₀; apply hott_3_3_5_ii.

 assert (u : ∀ a : A₀, B₀ (PT_intro a)).
  intros a₀; subst A₀ B₀; simpl.

  Focus 2.
  pose proof (@ex_3_17 A₀ B₀ f u) as v.
  subst A₀ B₀; simpl in u, v.

  apply v, PT_intro.


assert (f : ∀ x : ∥A∥, isProp (B x)).
 intros z; subst B; apply hott_3_3_5_ii.

Check (@ex_3_17 A B f).
 simpl in f.
 assert (h : ∀ a : A, B (PT_intro a)).
  intros z; subst B; simpl.

bbb.
 assert (xya : ∀ x y : A, (x = y) ≃ (a = a)).
  intros x y.
  exists (λ _ , eq_refl _); apply qinv_isequiv.
  assert (gggg : (a = a) → (x = y)).
   intros p.

bbb.
intros Sa g Pc.
assert (Se : ∀ x y : A, isSet (x = y)).
 intros x y.
 assert (r : ∀ z, isSet ∥(a = z)∥) by (intros z; apply isProp_isSet, PT_eq).
 assert (f : ∀ z (p : ∥(a = z)∥), isProp (g z = p)).
  intros z p u v; apply r.

  assert (h : ∀ z (t : a = z), g z = PT_intro t) by (intros z t; apply PT_eq).
  assert ((x = y) ≃ (a = a)).
   exists (λ _, eq_refl _).
   apply qinv_isequiv.
   assert (gggg : (a = a) → (x = y)).
    intros p.
(* h x : ∀ t : a = x, g x = ╎t╎ *)
(* h y : ∀ t : a = y, g y = ╎t╎ *)
bbb.
