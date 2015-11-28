(* experimentations on HoTT *)
(* requires coq 8.5 *)

Require Import Utf8 QArith NPeano.
Require Import chap1 chap2 chap3 chap4.
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

Print List_1_rect.

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

(*
Inductive W_type :=
  | WT_f : ∀ (WT_A : Type) (WT_B : WT_A → Type) (a : WT_A),
      (WT_B a → W_type) → W_type
  | WT_nil : W_type.
*)

(*
Inductive W_type (WT_A : Type) (WT_B : WT_A → Type) :=
  | WT_f : Π (a : WT_A), (WT_B a → W_type WT_A WT_B) → W_type WT_A WT_B
  | WT_nil : W_type WT_A WT_B.
*)

(*
Definition ℕ_W := W_type bool rec₂.
Check WT.
Check WT bool rec₂ false.
Set Printing All.
Check WT bool rec₂ false (λ (_ : False), existT _ false (rec₂ false)).

Toplevel input, characters 44-73:
Error:
In environment
f : False
The term "@existT bool (fun a : bool => rec₂ a) false (rec₂ false)" has type
 "@sigT bool (fun a : bool => rec₂ a)" while it is expected to have type
 "@sigT bool (fun a : bool => rec₂ a)" (cannot satisfy constraint
"Prop" == "(fun a : bool => rec₂ a) false").

Print W_type.

Inductive W_type :=
  | WT : ∀ (A : Type) (B : A → Type) (a : A), (B a → W_type) → W_type
  | WT_nil.

Notation "'W' ( x : A ) , B" :=
  (WT A B x) (at level 0, x at level 0, B at level 100).

Definition rec₂ b := if negb b then False else True.
Definition ℕ_W := WT bool rec₂.

Print ℕ_W.

Check ℕ_W false (λ _, WT_nil).
Check ℕ_W true (λ _, WT_nil).
*)

Inductive W_type A B :=
  | sup : ∀ a : A, (B a → W_type A B) → W_type A B.

(*
Notation "'W' ( a : A ) , B a" :=
  (W_type A (λ a, B a)) (at level 0, x at level 0, B at level 100).

Inductive W_type := W : Type → W_type.
Definition ℕ_W b := W (bool_rect (λ _, Type) False True b).

Print ℕ_W.
Check ℕ_W true.

About sum_rect.
Check
  (λ A,
   sum_rect (λ x : ⊤ + A, match x with inl _ => False | inr _ => True end)).
*)

Definition rec₂ b := if negb b then False else True.
Definition ℕ_W := sup bool rec₂.

Check False_rect.
(* False_rect
     : ∀ P : Type, ⊥ → P *)
Check ℕ_W.
(* ℕ_W
     : ∀ a : bool, (rec₂ a → W_type bool rec₂) → W_type bool rec₂ *)
Check sup bool.
(* sup bool
     : ∀ (B : bool → Type) (a : bool), (B a → W_type bool B) → W_type bool B *)

Check sup bool _ false.
(* sup bool ?T false
     : (?T false → W_type bool ?T) → W_type bool ?T *)
bbb.

Check sup bool _ false (λ x, False_rect

bbb.

Check (λ A, W (sum_rect (λ x : ⊤ + A, match x with inl _ => False | inr _ => True end))).

sum_rect :
∀ (A B : Type) (P : A + B → Type),
(∀ a : A, P (inl a)) → (∀ b : B, P (inr b)) → ∀ s : A + B, P s

sum_rect is not universe polymorphic
Arguments A, B are implicit
Argument scopes are [type_scope type_scope _ _ _ _]
sum_rect is transparent
Expands to: Constant Coq.Init.Datatypes.sum_rect

Definition List_W A := W (sum_rect ⊤ A).

bbb.

(*Check ℕ_W false.
Definition WT_nil A B := WT A B.
*)

Fixpoint B a := if negb a then (False : Type) else W_type bool B.

Check WT bool rec₂.
Check WT bool rec₂ false (λ _ : ⊥, ℕ_W).

bbb.
Definition ℕ_W := bool_rect (λ _, Type) False True.
Print ℕ_W.

Definition List_W A (x : ⊤ + A) := sum_rect (λ _, Type) (λ _, ⊥) (λ _, ⊤) x.
Print List_W.

Definition sup {A B} := (Π (a : A), B a → W (x : A), B x) → W (x : A), B x.

bbb.
