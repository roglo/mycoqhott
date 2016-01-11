(* experimentations on HoTT *)
(* requires coq 8.5 *)

Require Import Utf8 QArith NPeano.
Require Import chap1 chap2 chap3 chap4.
Remove Printing Let sigT.
Set Universe Polymorphism.

(* no default implicit without arguments *)
Arguments eq_refl [A] x.

Notation "⊥" := False.
Notation "⊤" := True.
Notation "★" := I.
Notation "'ℬ'" := (bool : Type).
Notation "A ⇔ B" := ((A → B) * (B → A))%type (at level 100).
Notation "( x , y ) '_{' P }" := (existT P x y)
  (at level 0, format "'[' ( x ,  y ) _{ P } ']'", only parsing).
Notation "f '~~' g" := (dt_homotopy f g) (at level 70).

Open Scope nat_scope.

(* "Chapter 5 - Induction" *)

(* "5.1 Introduction to inductive types" *)

(* "Theorem 5.1.1. Let f, g : Π (x:ℕ) E(x) be two functions
    which satisfy the recurrences
         e_z : E(0)     and     e_s : Π (n : ℕ) E(n) → E (succ(n))
    up to propositional equality, i.e., such that
         f(0) = e_z     and     g(0) = e z
    as well as
         Π (n : ℕ) f(succ(n)) = e_s(n, f(n)),
         Π (n : ℕ) g(succ(n)) = e_s(n, g(n)),
    Then f and g are equal." *)

Definition hott_5_1_1 E (f g : Π (x : ℕ), E x)
  (ez : E 0) (es : Π (n : ℕ), E n → E (S n)) :
  f 0 = ez → g 0 = ez
  → (Π (n : ℕ), f (S n) = es n (f n))
  → (Π (n : ℕ), g (S n) = es n (g n))
  → f = g.
Proof.
intros fz gz fs gs.
transparent assert (D : ∀ x, f x = g x).
 fix H 1; intros x.
  destruct x; [ eapply compose; [ apply fz | apply invert, gz ] | simpl ].
  eapply compose; [ apply fs | ].
  eapply compose; [ | eapply invert, gs ].
  destruct (H x); apply eq_refl.

 apply Π_type.funext, D.
Defined.

(* old version of the proof
apply Π_type.funext; intros n.
induction n; [ destruct fz, gz; apply eq_refl | ].
pose proof (fs n) as p.
pose proof (gs n) as q.
destruct IHn, p, q; apply eq_refl.
Defined.
*)

(* "5.2 Uniqueness of inductive types" *)

Module ℕ'.

Inductive ℕ' : Set := O' | S' : ℕ' → ℕ'.

Definition f : ℕ → ℕ' := nat_rec (λ n, ℕ') O' (λ n, S').
Definition g : ℕ' → ℕ := ℕ'_rec (λ n', ℕ) O (λ n', S).

Definition ℕ_gf : Π (n : ℕ), g (f n) = n.
Proof.
intros n.
change ((g ◦ f) n = id n); apply hap.
eapply hott_5_1_1; intros; try apply eq_refl.
Defined.

(* should use the  "primed" version of 5.1.1 as they say, but it can be
   proved (and ℕ_gf above also) directly *)
Definition ℕ'_fg : Π (n : ℕ'), f (g n) = n.
Proof.
intros n.
induction n; [ apply eq_refl | simpl; apply ap, IHn ].
Defined.

Definition equiv_ℕ_ℕ' : ℕ ≃ ℕ'.
Proof.
exists f; apply qinv_isequiv; exists g.
unfold "∼".
split; [ apply ℕ'_fg | apply ℕ_gf ].
Defined.

Definition double : ℕ → ℕ := nat_rec (λ _, ℕ) O (λ _ n, S (S n)).
(*
Eval compute in double 4.
*)

Definition double' := f ◦ double ◦ g.
(*
Eval compute in double' (S' (S' (S' (S' O')))).
*)

Definition double'₀ : ℕ' → ℕ' := ℕ'_rec (λ _, ℕ') O' (λ _ n, S' (S' n)).

Definition double'₀_double' : double' = double'₀.
Proof.
apply Π_type.funext; intros n.
induction n; [ apply eq_refl | simpl ].
destruct IHn; apply eq_refl.
Defined.

Definition double_prop : Π (n : nat), double (S n) = S (S (double n)).
Proof.
induction n; [ apply eq_refl | simpl ].
destruct IHn; apply eq_refl.
Defined.

(* "Consider, for instance, a simple lemma such as
       Π (n : ℕ') double'(succ'(n)) = succ'(succ'(double'(n))).
    Inserting the correct fs and gs is only a little easier than
    re-proving it by induction on n : N' directly." *)

Definition fs : ∀ n, S' (f n) = f (S n) := λ n, eq_refl (f (S n)).
Definition gs : ∀ n, S (g n) = g (S' n) := λ n, eq_refl (g (S' n)).

Definition double'_prop_tac : Π (n : ℕ'), double' (S' n) = S' (S' (double' n)).
Proof.
intros n.
unfold double', "◦".
destruct (gs n).
destruct (invert (double_prop (g n))).
destruct (invert (fs (double (g n)))).
destruct (invert (fs (S (double (g n))))).
apply eq_refl.
Defined.

Definition double'_prop : Π (n : ℕ'), double' (S' n) = S' (S' (double' n))
  := λ (n : ℕ'),
     match gs n with
     | eq_refl _ =>
         match double_prop (g n) with
         | eq_refl _ =>
             match fs (double (g n)) with
             | eq_refl _ =>
                 match fs (S (double (g n))) with
                 | eq_refl _ => eq_refl _
                 end
             end
         end
     end.

Inductive List_1 : Type :=
  | nil : List_1
  | cons : True → List_1 → List_1.

(* "The induction principle of List(1) says that for any E : List(1) →
    U together with recurrence data e_nil : E(nil) and e_cons : Π(u:1)
    Π(l:List(1)) E(l) → E(cons(u,l)), there exists f : Π (l:List(1))
    E(l) such that f(nil) ≡ e_nil and f(cons(u,l)) ≡ econs (u,l,f(l))." *)

Definition List_1_ind_princ :
  ∀ (E : List_1 → Type) (e_nil : E nil)
    (e_cons : Π (u : True), Π (l : List_1), E l → E (cons u l)),
    Σ (f : Π (l : List_1), E l),
    (f nil = e_nil) ∧ (∀ u l, f (cons u l) = e_cons u l (f l)).
Proof.
intros.
transparent assert (f : ∀ l, E l).
 induction l; [ apply e_nil | apply e_cons, IHl ].

 exists f; unfold f; clear f; simpl.
 split; intros; apply eq_refl.
Defined.

(* "Now suppose we define 0'' :≡ nil : List(1), and succ'' : List(1) →
    List(1) by succ''(l) :≡ cons(★,l). Then for any E : List(1) → U
    together with e₀ : E(0'') and e_s : Π (l:List(1)) E(l) →
    E(succ''(l)), we can define
         e_nil :≡ e0
         e_cons(★,l,x) :≡ e_s(l,x)." *)

Definition O'' := nil.
Definition succ'' l := cons I l.

Definition e_nil {E : List_1 → Type} (e₀ : E O'') := e₀.
Definition e_cons {E : List_1 → Type}
  (e_s : Π (l : List_1), E l → E (succ'' l)) (u : ⊤) l x := e_s l x.

(* "Now we can apply the induction principle of List(1), obtaining f :
    Π (l:List(1)) E(l) such that
                        f(0'') ≡ f(nil) ≡ e_nil ≡ e₀
        f(succ'' l) ≡ f(cons(★,l)) ≡ e_cons(★,l,f(l)) ≡ e_s(l,f(l))." *)

Definition List_1_ind_princ' {E : List_1 → Type} {e₀ : E O''}
    {e_s : Π (l : List_1), E l → E (succ'' l)} :
  Σ (f : Π (l : List_1), E l),
  f O'' = f nil ∧ f nil = e_nil e₀ ∧ e_nil e₀ = e₀ ∧
  ∀ l, f (succ'' l) = f (cons ★ l) ∧ f (cons ★ l) = e_cons e_s ★ l (f l) ∧
       e_cons e_s ★ l (f l) = e_s l (f l).
Proof.
transparent assert (p : ∀ l, E l).
 intros l.
 induction l; [ apply e₀ | ].
 destruct t; apply e_s, IHl.

 exists p.
 split; [ apply eq_refl | ].
 split; [ apply eq_refl | ].
 split; [ apply eq_refl | intros l ].
 split; [ apply eq_refl | ].
 split; [ apply eq_refl | ].
 apply eq_refl.
Defined.

End ℕ'.

(* "5.3 W-types" *)

Inductive W_type A B :=
  | sup : ∀ a : A, (B a → W_type A B) → W_type A B.
Arguments sup {A} {B} a f.

(* ℕ as W_type *)

Definition ℕarg := bool_rect (λ _, Type) True False.
Definition ℕW := W_type bool ℕarg.

Definition O_W : ℕW := @sup bool ℕarg false (False_rect ℕW).
Definition one_W : ℕW := @sup bool ℕarg true (λ x : True, O_W).
Definition succ_W (n : ℕW) : ℕW := @sup bool ℕarg true (λ _ : True, n).

Fixpoint ℕ2ℕW n :=
  match n with
  | O => O_W
  | S n' => succ_W (ℕ2ℕW n')
  end.

(* List X as W_type *)
(* List(X) :≡ W_(z:1+X) rec_(1+X) (U, 0, λx.1, z) *)

Definition List_arg X :=
  sum_rect (λ _, Type) (λ _ : True, False) (λ _ : X, True).
Definition List_W X := W_type (sum True X) (List_arg X).

Definition nil_W X :=
  @sup (sum True X) (List_arg X) (inl I) (False_rect (List_W X)).
Definition cons_W X (x : X) l :=
  @sup (sum True X) (List_arg X) (inr x) (λ _ : True, l).

(* why not doing this: *)
Definition List_arg2 := bool_rect (λ _, Type) True False.
Definition List_W2 := W_type bool List_arg2.
Definition nil_W2 := @sup bool List_arg2 false (False_rect List_W2).
Definition cons_W2 X (x : X) l := @sup bool List_arg2 true (λ _ : True, l).
(* ? *)

(* "When proving a statement E : (W (x:A) B(x)) → U about all elements
    of the W-type W (x:A) B(x), it suffices to prove it for sup(a, f),
    assuming it holds for all f(b) with b : B(a). In other words, it
    suffices to give a proof
     e : Π (a : A) Π (f : B(a)→W(x:A)B(x))
           Π (g:Π(b:B(a))E(f(b))) E(sup(a,f))" *)

Definition W_type_ind_princ A B (E : W_type A B → Type) :
  (Π (a : A), Π (f : B a → W_type A B),
   Π (g : Π (b : B a), E (f b)), E (sup a f))
  → ∀ x : W_type A B, E x.
Proof.
apply W_type_rect.
Defined.

(* "How would we define the function double on natural numbers encoded
    as a W-type? We would like to use the recursion principle of ℕ^W
    with a codomain of ℕ^W itself. We thus need to construct a
    suitable function
           e : Π (a:2) Π (f:B(a)→ℕ^W) Π (g:B(a)→ℕ^W) ℕ^W
    which will represent the recurrence for the double function; for
    simplicity we denote the type family rec₂(U,0,1) by B." *)

(* e is ℕW_double_rec *)
Definition ℕW_double_rec_tac :
  let B := bool_rect (λ _, Type) ⊤ ⊥ in
  Π (a : ℬ), Π (f : B a → ℕW), Π (g : B a → ℕW), ℕW.
Proof.
intros; simpl in B.
destruct a; simpl in f, g; [ | apply O_W ].
apply succ_W, succ_W, g, ★.
Defined.

Definition ℕW_double_rec :
  let B := bool_rect (λ _, Type) ⊤ ⊥ in
  Π (a : ℬ), Π (f : B a → ℕW), Π (g : B a → ℕW), ℕW
:=
  let B := bool_rect (λ _ : bool, Type) ⊤ ⊥ in
  λ (a : ℬ) (f g : B a → ℕW),
  (if a return ((B a → ℕW) → (B a → ℕW) → ℕW)
   then λ _ h : B true → ℕW, succ_W (succ_W (h ★))
   else λ _ _ : B false → ℕW, O_W) f g.

Definition double : ℕW → ℕW :=
  W_type_ind_princ ℬ ℕarg (λ _, ℕW) ℕW_double_rec.

(* "The associated computation rule for the function
    rec_{W(x:A)B(x)}(E,e) : Π(w:W(x:A) B(x)) E(w) is as follows.

    * For any a:A and f:B(a)→W(x:A) B(x) we have
        rec_{W:(x:A),B(x)}(E,e,sup(a,f))
        ≡ e(a,f,(λb.rec_{W(x:A),B(x)}(E,e,f(b))." *)

Definition W_type_comp_rule A B (a : A) (f : B a → W_type A B) E e :
  W_type_rect A B E e (sup a f)
  = e a f (λ b, W_type_rect A B E e (f b)).
Proof. apply eq_refl. Defined.

Definition double_ℕW_O : double O_W = O_W.
Proof. apply eq_refl. Defined.

Definition double_ℕW_1 : double one_W = succ_W (succ_W O_W).
Proof. apply eq_refl. Defined.

(* "Theorem 5.3.1. Let g, h : Π (w:W(x:A) B(x)) E(w) be two functions
    which satisfy the recurrence
          e : Π (a,f) (Π (b:B(a)) E(f(b))) → E(sup(a,f)),
    i.e., such that
          Π (a,f) g(sup(a,f)) = e(a,f,λb.g(f(b))),
          Π (a,f) h(sup(a,f)) = e(a,f,λb.h(f(b))).
    Then g and h are equal." *)

Definition hott_5_3_1 A B E (g h : Π (w : W_type A B), E w)
  (e :
   Π (a : A), Π (f : B a → W_type A B), (Π (b : B a), E (f b)) → E (sup a f)) :
    (Π (a : A), Π (f : B a → W_type A B), g (sup a f) = e a f (λ b, g (f b)))
  → (Π (a : A), Π (f : B a → W_type A B), h (sup a f) = e a f (λ b, h (f b)))
  → g = h.
Proof.
intros p q.
apply Π_type.funext; intros (a, f).
induction (sup a f) as [a' k Hk].
eapply compose; [ apply p | ].
eapply compose; [ | eapply invert, q ].
apply ap, Π_type.funext; intros w.
apply Hk.
Defined.

(* "5.4 Inductive types are initial algebras" *)

(* "Definition 5.4.1. A *ℕ-algebra* is a type C with two elements c₀ :
    C, c_s : C → C. The type of such algebras is
        ℕAlg :≡ Σ (C : U) C × (C → C)." *)

Inductive ℕAlg := ℕA : (Σ (C : Type), (C * (C → C))%type) → ℕAlg.

Definition ℕAlg_C (na : ℕAlg) : Type := match na with ℕA a => Σ_pr₁ a end.
Definition ℕAlg_c₀ (na : ℕAlg) : ℕAlg_C na :=
  match na with ℕA a => fst (Σ_pr₂ a) end.
Definition ℕAlg_cs (na : ℕAlg) : ℕAlg_C na → ℕAlg_C na :=
  match na with ℕA a => snd (Σ_pr₂ a) end.

(* "Definition 5.4.2. A *ℕ-homomorphism* between ℕ-algebras (C,c₀,cs)
    and (D,d₀,ds) is a function h : C → D such that h(c₀) = d₀ and
    h(cs(c)) = ds(h(c)) for all c : C. The type of such homomorphisms
    is
        ℕHom((C,c₀,cs),(D,d₀,ds)) :≡
          Σ (h:C→D) (h(c₀) = d₀) × Π(c:C) (h(cs(c)) = ds(h(c)))." *)

Definition ℕHom_def (Ca Da : ℕAlg) :=
  let C := ℕAlg_C Ca in
  let D := ℕAlg_C Da in
  let c₀ := ℕAlg_c₀ Ca in
  let d₀ := ℕAlg_c₀ Da in
  let cs := ℕAlg_cs Ca in
  let ds := ℕAlg_cs Da in
  Σ (h: C → D), ((h c₀ = d₀) * Π (c : C), (h (cs c) = ds (h c)))%type.

Inductive ℕHom (Ca Da : ℕAlg) := ℕH : ℕHom_def Ca Da → ℕHom Ca Da.

Definition ℕHom_fun {Ca Da} (f : ℕHom Ca Da) : ℕAlg_C Ca → ℕAlg_C Da :=
  match f with ℕH _ _ h => Σ_pr₁ h end.
Definition ℕHom_eq₀ {Ca Da} (f : ℕHom Ca Da)
  : ℕHom_fun f (ℕAlg_c₀ Ca) = ℕAlg_c₀ Da :=
  match f with ℕH _ _ h => fst (Σ_pr₂ h) end.
Definition ℕHom_eqs {Ca Da} (f : ℕHom Ca Da)
  : Π (c : ℕAlg_C Ca), ℕHom_fun f (ℕAlg_cs Ca c) = ℕAlg_cs Da (ℕHom_fun f c) :=
  match f with ℕH _ _ h => snd (Σ_pr₂ h) end.

(* "Definition 5.4.3. A ℕ-algebra I is called *homotopy-initial*, or
    *h-initial* for short, if for any other ℕ-algebra C, the type of
    ℕ-homomorphisms from I to C is contractible. Thus,
            isHinit_ℕ(I) :≡ Π (C : ℕAlg), isContr(ℕHom(I,C))." *)

Definition isHinit_ℕ I := Π (C : ℕAlg), isContr (ℕHom I C).

(* "Theorem 5.4.4. Any two h-initial ℕ-algebras are equal. [...]" *)

Definition hott_5_4_4_i I J : isHinit_ℕ I → isHinit_ℕ J → I = J.
Proof.
intros p q.
assert (cij : isContr (ℕHom I J)); [ apply p |  ].
assert (cji : isContr (ℕHom J I)); [ apply q |  ].
assert (cjj : isContr (ℕHom J J)); [ apply q |  ].
destruct cij as (f, cij).
destruct cji as (g, cji).
destruct cjj as (h, cjj).
assert (fg : ℕHom_fun f ◦ ℕHom_fun g = id).
 set
  (J₀ := ℕH J J (existT _ id (eq_refl _, λ c, eq_refl (ℕAlg_cs J (id c))))).
 unfold id in J₀; simpl in J₀.
 destruct f as ((f, (f₀, fs))).
 destruct g as ((g, (g₀, gs))); simpl.
 set (c := (ap f g₀ • f₀, λ w, ap f (gs w) • fs (g w))).
 set (u := ℕH _ _ (existT _ (f ◦ g) c) : ℕHom J J).
 pose proof (cjj u) as H1; unfold u in H1.
 pose proof (cjj J₀) as H2.
 apply invert in H2; destruct H2.
 unfold J₀ in H1; injection H1; intros H2.
 apply invert, H2.

 assert (gf : ℕHom_fun g ◦ ℕHom_fun f = id).
  assert (cii : isContr (ℕHom I I)) by apply p.
  destruct cii as (i, cii).
  set
   (I₀ := ℕH I I (existT _ id (eq_refl _, λ c, eq_refl (ℕAlg_cs I (id c))))).
  unfold id in I₀; simpl in I₀.
  destruct f as ((f, (f₀, fs))).
  destruct g as ((g, (g₀, gs))); simpl.
  set (c := (ap g f₀ • g₀, λ w, ap g (fs w) • gs (f w))).
  set (u := ℕH _ _ (existT _ (g ◦ f) c) : ℕHom I I).
  pose proof (cii u) as H1; unfold u in H1.
  pose proof (cii I₀) as H2.
  apply invert in H2; destruct H2.
  unfold I₀ in H1; injection H1; intros H2.
  apply invert, H2.

  set
   (H1 :=
    existT isequiv (ℕHom_fun f)
      (existT _ (ℕHom_fun g)
         match fg in (_ = y) return (ℕHom_fun f ◦ ℕHom_fun g ∼ y) with
         | eq_refl _ => homotopy_eq_refl (ℕHom_fun f ◦ ℕHom_fun g)
         end,
      existT _ (ℕHom_fun g)
        match gf in (_ = y) return (ℕHom_fun g ◦ ℕHom_fun f ∼ y) with
        | eq_refl _ => homotopy_eq_refl (ℕHom_fun g ◦ ℕHom_fun f)
        end)
    :
    ℕAlg_C I ≃ ℕAlg_C J).
  destruct I as ((C, (c₀, cs))).
  destruct J as ((D, (d₀, ds))); simpl in *.
  destruct f as ((f, (f₀, fs))); simpl in *.
  destruct g as ((g, (g₀, gs))); simpl in *; simpl.
  apply ap.
  clear cji f₀ cij fs.
  revert f g fg gf g₀ gs H1; clear; intros.
  (* perhaps a lemma from here... *)
  replace c₀ with (g d₀).
  replace cs with (λ c, g (ds (f c))).
   replace f with (Σ_pr₁ H1) by (unfold H1; apply eq_refl).
   replace g with (Σ_pr₁ (fst (Σ_pr₂ H1))) by (unfold H1; apply eq_refl).
   replace H1 with (idtoeqv (ua H1)) by apply idtoeqv_ua.
   destruct (ua H1); apply eq_refl.

   apply Π_type.funext; intros c.
   eapply compose; [ apply gs | apply ap ].
   change ((g ◦ f) c = id c); apply hap, gf.
Defined.

(* "[...] Thus, the type of h-initial ℕ-algebras is a mere
    proposition." *)

Definition hott_5_4_4_ii : isProp (Σ (A : ℕAlg), isHinit_ℕ A).
Proof.
intros (I, p) (J, q).
pose proof (hott_5_4_4_i I J p q) as H.
apply (Σ_type.pair_eq H).
unfold transport.
destruct H; unfold id.
assert (H : isProp (isHinit_ℕ I)); [ | apply H ].
apply ex_3_6_2; intros K; apply hott_3_11_4.
Defined.

(* "Theorem 5.4.5. The ℕ-algebra (ℕ,0,succ) is homotopy initial." *)

Definition isContr_Σ_prod A P Q :
  (Σ (a : Σ (x : A), (P x * Q x)%type), Π (x : Σ (x : A), (P x * Q x)%type),
   a = x)
  → isContr (Σ (x : A), (P x * Q x)%type).
Proof.
intros (p, q).
exists p; intros r.
apply q.
Defined.

Fixpoint ℕ2ℕAlg C (c₀ : C) cs n :=
  match n with 0 => c₀ | S n => cs (ℕ2ℕAlg C c₀ cs n) end.

Definition ℕ2ℕAlg_str (A : ℕAlg) n : ℕAlg_C A :=
  match A with
  | ℕA (existT _ C (c₀, cs)) => ℕ2ℕAlg C c₀ cs n
  end.

Definition hott_5_4_5 : isHinit_ℕ (ℕA (existT _ ℕ (0, S))).
Proof.
unfold isHinit_ℕ.
intros C.
set (na := ℕA (existT _ ℕ (0, S))); simpl in na.
set (f := ℕ2ℕAlg_str C).
transparent assert ( f₀ : (f 0 = ℕAlg_c₀ C) ).
 destruct C as ((C, (c₀, cs))); apply eq_refl.

 transparent assert ( fs : (∀ n, f (S n) = ℕAlg_cs C (f n)) ).
  destruct C as ((C, (c₀, cs))); intros; apply eq_refl.

  simpl in *.
  set (fh := ℕH na C (existT _ (ℕ2ℕAlg_str C) (f₀, fs))).
  simpl in fh.
  exists fh.
  destruct C as ((C, (c₀, cs))); simpl in *.
  intros gh.
  transparent assert ( fg : (ℕHom_fun fh = ℕHom_fun gh) ).
   apply
    (hott_5_1_1 (λ _, C) (ℕHom_fun fh) (ℕHom_fun gh) c₀ 
       (λ _, cs) (ℕHom_eq₀ fh) (ℕHom_eq₀ gh) (ℕHom_eqs fh) 
       (ℕHom_eqs gh)).

   unfold hott_5_1_1 in fg.
   simpl in fg.
   unfold id in fg.
   destruct gh as ((g, (g₀, gs))); simpl in *; simpl.
   unfold fh; simpl.
   apply ap, (Σ_type.pair_eq fg).
   eapply compose.
    apply (transport_pair (λ h, h 0 = c₀) (λ h, ∀ c, h (S c) = cs (h c))).

    unfold ℕ2ℕAlg_str in fg.

    unfold ℕ2ℕAlg_str in f; subst f.
    set (f := fun n => ℕ2ℕAlg C c₀ cs n) in *.
    set
     (h :=
      fix H (x : ℕ) : f x = g x :=
        match x as n return (f n = g n) with
        | 0 => g₀⁻¹
        | S x0 =>
            match H x0 in (_ = y) return (cs (f x0) = cs y) with
            | eq_refl _ => eq_refl (cs (f x0))
            end • (gs x0)⁻¹
        end) in fg.
    apply cartesian.pair_eq; split; simpl.
     replace g₀ with (Π_type.happly _ _ fg 0)⁻¹.
      Focus 2.
      unfold fg; simpl.
      eapply compose; [  | apply hott_2_1_4_iii ].
      apply ap.
      set (f0 := λ n : ℕ, ℕ2ℕAlg C c₀ cs n).
      apply (Π_type.funext_quasi_inverse_of_happly f0 g h 0).

      destruct fg; apply eq_refl.

     apply Π_type.funext; intros n.
bbb.

set (u := (Π_type.happly _ _ fg (S n))⁻¹).
unfold fg in u.
About Π_type.funext_quasi_inverse_of_happly.
set (v := Π_type.funext_quasi_inverse_of_happly f g h (S n)).
bbb.

set (u := λ n, (Π_type.happly _ _ fg (S n))⁻¹ • fs n).
bbb.

replace gs with (λ n, transport (λ f, g (S n) = cs (f n)) fg (u n)).
 destruct fg; simpl.
 unfold u; simpl; unfold id.
 apply cartesian.pair_eq; split; [ apply eq_refl | simpl ].
 apply Π_type.funext; intros; apply eq_refl.

 apply Π_type.funext; intros n.
 unfold u; simpl.
 destruct fg; simpl; unfold id.
bbb.

 replace gs with ...
bbb.
 destruct fg; simpl.
 unfold id, f₀.
bbb.

rewrite <- EqStr.hap_invert.
unfold fg; simpl.
simpl.

set (u := λ c, (hap fg (S c))⁻¹).
simpl in u.
bbb.

replace (f₀, fs) with (ℕHom_eq₀ fh, ℕHom_eqs fh) by apply eq_refl.
destruct fg; fold f.
replace (eq_refl f) with (eq_refl (ℕHom_fun fh)) by apply eq_refl.
bbb.
