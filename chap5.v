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
  (e_z : E 0) (e_s : Π (n : ℕ), E n → E (S n)) :
  f 0 = e_z → g 0 = e_z
  → (Π (n : ℕ), f (S n) = e_s n (f n))
  → (Π (n : ℕ), g (S n) = e_s n (g n))
  → f = g.
Proof.
intros fz gz fs gs.
apply Π_type.funext; intros n.
induction n; [ destruct fz, gz; apply eq_refl | ].
pose proof (fs n) as p.
pose proof (gs n) as q.
destruct IHn, p, q; apply eq_refl.
Defined.

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

Definition double'_prop2 : Π (n : ℕ'), double' (S' n) = S' (S' (double' n)).
Proof.
intros n.
pose proof ua equiv_ℕ_ℕ' as p.
(*
pose proof @transport Type _ _ _ p.
Check @transport Type.
set (toto := double' (S' n) = S' (S' (double' n)) : Type).
simpl in toto.
*)
Abort.

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
  → g ~~ h.
Proof.
intros p q (a, f).
eapply compose; [ apply p | ].
eapply compose; [ | eapply invert, q ].
pose proof W_type_comp_rule A B a f E e.
Abort. (* I don't know how to finish this proof; I see later, perhaps *)

(* "5.4 Inductive types are initial algebras" *)

(* "Definition 5.4.1. A *ℕ-algebra* is a type C with two elements c₀ :
    C, c_s : C → C. The type of such algebras is
        ℕAlg :≡ Σ (C : U) C × (C → C)." *)

Definition ℕAlg := Σ (C : Type), (C * (C → C))%type.

(* "Definition 5.4.2. A *ℕ-homomorphism* between ℕ-algebras (C,c₀,cs)
    and (D,d₀,ds) is a function h : C → D such that h(c₀) = d₀ and
    h(cs(c)) = ds(h(c)) for all c : C. The type of such homomorphisms
    is
        ℕHom((C,c₀,cs),(D,d₀,ds)) :≡
          Σ (h:C→D) (h(c₀) = d₀) × Π(c:C) (h(cs(c)) = ds(h(c)))." *)

Definition ℕHom (Ca Da : ℕAlg) :=
  match (Ca, Da) with
  | (existT _ C (c₀, cs), existT _ D (d₀, ds)) =>
       Σ (h: C → D), ((h c₀ = d₀) * Π (c : C), (h (cs c) = ds (h c)))%type
  end.

(* "Definition 5.4.3. A ℕ-algebra I is called *homotopy-initial*, or
    *h-initial* for short, if for any other ℕ-algebra C, the type of
    ℕ-homomorphisms from I to C is contractible. Thus,
            isHinit_ℕ(I) :≡ Π (C : ℕAlg), isContr(ℕHom(I,C))." *)

Definition isHinit_ℕ I := Π (C : ℕAlg), isContr (ℕHom I C).

(* "Theorem 5.4.4. Any two h-initial ℕ-algebras are equal. [...]" *)

Definition isContr_sigma A P :
  isContr (Σ (x : A), P x) → (Π (x : A), isContr (P x)) → isContr A.
Proof.
intros p q.
unfold isContr in p; unfold isContr.
destruct p as ((a, p), r).
exists a; intros a'.
assert (P a') as p' by apply q.
pose proof r (existT _ a' p') as s.
injection s; intros u v; apply v.
Defined.

Definition hott_5_4_4_i I J : isHinit_ℕ I → isHinit_ℕ J → I = J.
Proof.
intros p q.
assert (r : isContr (ℕHom I J)) by apply p.
assert (s : isContr (ℕHom J I)) by apply q.
destruct r as (f, r).
destruct s as (g, s).
(**)
transparent assert (gffg: (ℕHom I I * ℕHom J J)%type).
 unfold ℕHom in f, g; unfold ℕHom.
 destruct I as (C, (c₀, cs)).
 destruct J as (D, (d₀, ds)).
 destruct f as (f, (f₀, fs)).
 destruct g as (g, (g₀, gs)).
 split.
  exists (g ◦ f); unfold "◦".
  split; [ eapply compose; [ apply (ap g f₀) | apply g₀ ] | intros c ].
  eapply compose; [ apply (ap g (fs c)) | apply gs ].

  exists (f ◦ g); unfold "◦".
  split; [ eapply compose; [ apply (ap f g₀) | apply f₀ ] | intros d ].
  eapply compose; [ apply (ap f (gs d)) | apply fs ].

 assert (ci : isContr (ℕHom I I)) by apply p.
 assert (cj : isContr (ℕHom J J)) by apply q.
 destruct I as (C, (c₀, cs)).
 destruct J as (D, (d₀, ds)).
 assert (C = D).
  apply ua.
  destruct f as (f, (f₀, fs)).
  destruct g as (g, (g₀, gs)).
  set (gf := fst gffg).
  set (fg := snd gffg).
  unfold gffg in gf, fg; clear gffg; simpl in gf, fg.
  exists f; apply qinv_isequiv; exists g.
  set (U := ℕHom (existT _ C (c₀, cs)) (existT _ C (c₀, cs))) in ci, gf.
  set (V := ℕHom (existT _ D (d₀, ds)) (existT _ D (d₀, ds))) in cj, fg.
  unfold ℕHom in U, V.
  split.
unfold isHinit_ℕ in q.
pose proof isContr_sigma _ _ cj as H1.
simpl in H1.
assert (∀ x : D → D, isContr ((x d₀ = d₀) * (∀ c : D, x (ds c) = ds (x c)))).
 intros fd.
 apply isContr_prod; split.

Abort.
(* too complicated, I have to think of it but I am depressed therefore
   not motivated to continue; I see that later, when I feel better

SearchAbout (isContr (_ = _)).
bbb.

unfold isContr in H1.
destruct H1 as (fd, Hd).
assert (fd = f ◦ g) by apply Hd.
assert (fd = id) by apply Hd.
rewrite <- H, H0.
intros d; apply eq_refl.
bbb.

  exists f; apply qinv_isequiv; exists g.
  split; unfold "◦", "∼", id.
   intros d.
Print isHinit_ℕ.
   destruct gffg as ((h, (h₀, hs)), (i, (i₀, hi))).

bbb.
*)

(* "[...] Thus, the type of h-initial ℕ-algebras is a mere
    proposition." *)

Definition hott_5_4_4_ii I : isHinit_ℕ I → isProp (Σ_pr₁ I).
Proof.
Abort. (* need hott_5_4_4_i *)

(* "Theorem 5.4.5. The ℕ-algebra (ℕ,0,succ) is homotopy initial." *)

Fixpoint morph_of_ℕ C (c₀ : C) cs n :=
  match n with 0 => c₀ | S n => cs (morph_of_ℕ C c₀ cs n) end.

Definition ℕAlg_morph_of_ℕ (A : ℕAlg) n : Σ_pr₁ A :=
  match A with
  | existT _ C (c₀, cs) => morph_of_ℕ C c₀ cs n
  end.

Definition hott_5_4_5 : isHinit_ℕ (existT _ ℕ (0, S)).
Proof.
unfold isHinit_ℕ.
intros A.
unfold isContr.
transparent assert (φ : ℕHom (existT _ ℕ (0, S)) A).
 destruct A as (C, (c₀, cs)).
 exists (morph_of_ℕ C c₀ cs).
 split; [ apply eq_refl | intros n; apply eq_refl ].

 exists φ; unfold φ; clear φ.
 intros φ.
 destruct A as (C, (c₀, cs)).
 destruct φ as (f, (p, q)).
 assert (H : f = morph_of_ℕ C c₀ cs).
  apply Π_type.funext; intros n.
  induction n; [ apply p | simpl ].
  eapply compose; [ apply q | apply ap, IHn ].

  apply invert in H; destruct H.
  apply (Σ_type.pair_eq (eq_refl _)).
  unfold transport, id.
  simpl in p, q.
  apply cartesian.pair_eq; simpl; split.

bbb.
