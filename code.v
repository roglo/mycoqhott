(* proving nat and list are hset *)

Set Universe Polymorphism.
Set Nested Proofs Allowed.

Require Import Utf8.

Definition isSet A := ∀ (x y : A) (p q : x = y), p = q.

Definition homotopy {A B} (f g : A → B) := ∀ x : A, f x = g x.
Definition composite {A B C} (f : A → B) (g : B → C) x := g (f x).

Definition isequiv {A B : Type} f :=
  ({ g : B → A & homotopy (composite g f) (@id _) } *
   { h : B → A & homotopy (composite f h) (@id _) })%type.

Definition equivalence (A B : Type) := { f : A → B & isequiv f }.

Definition transport {A} P {x y : A} (p : x = y) : P x → P y :=
  match p with
  | eq_refl _ => @id _
  end.

Definition ap {A B x y} (f : A → B) (p : x = y) : f x = f y :=
  match p with
  | eq_refl _ => eq_refl (f x)
  end.

Definition qinv {A B} (f : A → B) :=
  { g : B → A &
    (homotopy (composite g f) (@id _) *
     homotopy (composite f g) (@id _))%type }.

Definition qinv_isequiv {A B} (f : A → B) : qinv f → isequiv f.
Proof.
intros p.
destruct p as (g, (α, β)).
split; exists g; assumption.
Defined.

Theorem equiv_compose {A B C} :
  ∀ (f : equivalence A B) (g : equivalence B C), equivalence A C.
Proof.
intros eqf eqg.
destruct eqf as (f, ((f₁, eqf₁), (f₂, eqf₂))).
destruct eqg as (g, ((g₁, eqg₁), (g₂, eqg₂))).
unfold equivalence.
exists (composite f g).
split.
 exists (composite g₁ f₁).
 intros c; unfold composite; simpl.
 transitivity (g (g₁ c)); [ apply ap, eqf₁ | apply eqg₁ ].

 exists (composite g₂ f₂).
 intros a; unfold composite; simpl.
 transitivity (f₂ (f a)); [ apply ap, eqg₂ | apply eqf₂ ].
Defined.

Definition hott_2_3_10 {A B x y} :
    ∀ (f : A → B) (P : B → Type) (p : x = y) (u : P (f x)),
    transport (composite f P) p u = transport P (ap f p) u
 := λ f P p u,
    match p with
    | eq_refl _ => eq_refl (transport P (ap f (eq_refl x)) u)
    end.

(* proof nat is hset *)

Fixpoint nat_code m n : Type :=
  match (m, n) with
  | (0, 0) => True
  | (S m, 0) => False
  | (0, S n) => False
  | (S m, S n) => nat_code m n
  end.

Fixpoint nat_r n : nat_code n n :=
  match n with
  | 0 => I
  | S m => nat_r m
  end.

Definition nat_encode (m n : nat) : m = n → nat_code m n :=
  λ p, transport (nat_code m) p (nat_r m).

Definition nat_decode (m n : nat) : nat_code m n → m = n.
Proof.
revert m n.
fix IHn 1.
intros m n p.
destruct m.
 destruct n; [ reflexivity | refine (match p with end) ].

 destruct n; [ refine (match p with end) | simpl in p ].
 apply ap, IHn, p.
Defined.

Theorem nat_decode_encode {m n} : ∀ p, nat_decode m n (nat_encode m n p) = p.
Proof.
intros p.
destruct p; simpl; unfold id; simpl.
induction m; [ reflexivity | simpl ].
apply (ap (ap S)) in IHm; assumption.
Defined.

Theorem nat_encode_decode {m n} : ∀ c, nat_encode m n (nat_decode m n c) = c.
Proof.
intros c.
revert n c; induction m; intros.
 simpl in c.
 destruct n, c; reflexivity.

 simpl in c.
 destruct n; [ refine (match c with end) | simpl ].
 unfold nat_encode.
 rewrite <- (hott_2_3_10 S (nat_code (S m)) (nat_decode m n c)).
 apply IHm.
Defined.

Theorem equiv_eq_nat_code : ∀ m n, equivalence (m = n) (nat_code m n).
Proof.
intros.
exists (nat_encode m n); apply qinv_isequiv.
exists (nat_decode m n).
unfold composite, homotopy, id; simpl.
split; intros p; [ apply nat_encode_decode | apply nat_decode_encode ].
Defined.

Require Import Arith.

Definition nat_code_equiv_1_or_0 m n :
  (equivalence (nat_code m n) True) + (equivalence (nat_code m n) False).
Proof.
destruct (eq_nat_dec m n) as [H1| H1].
 left; subst m.
 exists (λ c, I); apply qinv_isequiv.
 exists (λ _, nat_r n).
 unfold composite, homotopy, id; simpl.
 split; [ intros u; destruct u; reflexivity | intros c ].
 induction n; [ destruct c; reflexivity | apply IHn ].

 right.
 exists (λ c, H1 (nat_decode m n c)); apply qinv_isequiv.
 exists (λ p : False, match p with end).
 unfold composite, homotopy, id.
 split; [ intros p; destruct p | ].
 intros c; destruct (H1 (nat_decode m n c)).
Defined.

Definition isSet_nat : isSet nat.
Proof.
intros m n p q.
pose proof equiv_eq_nat_code m n as r.
pose proof nat_code_equiv_1_or_0 m n as s.
destruct s as [s| s].
 eapply equiv_compose in s; [ | apply r ].
 destruct s as (f, ((g, Hg), (h, Hh))).
 unfold composite, homotopy, id in Hg, Hh.
 pose proof Hh p as Hp.
 pose proof Hh q as Hq.
 destruct (f p), (f q).
 subst p q; reflexivity.

 eapply equiv_compose in s; [ | apply r ].
 destruct s as (f, ((g, Hg), (h, Hh))).
 exfalso; apply f, p.
Defined.

(* proof bool is hset *)

Definition isSet_bool : isSet bool.
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

(* proof list is hset *)

Require Import List.
Import List.ListNotations.

(**)

Fixpoint list_code {A} (la lb : list A) : Type :=
  match (la, lb) with
  | ([], []) => True
  | (_ :: _, []) => False
  | ([], _ :: _) => False
  | (a :: la, b :: lb) => ((a = b) * list_code la lb)
  end.

Fixpoint list_r {A} (l : list A) : list_code l l :=
  match l with
  | [] => I
  | a :: l => (eq_refl, list_r l)
  end.

Definition list_encode {A} (la lb : list A) :
    la = lb → list_code la lb :=
  λ p, transport (list_code la) p (list_r la).

Definition list_decode {A} (la lb : list A) :
  list_code la lb → la = lb.
Proof.
revert la lb.
fix IHn 1.
intros la lb lc.
destruct la as [| a la]; [ now destruct lb | ].
destruct lb as [| b lb]; [ easy | ].
destruct lc as (p, lc).
destruct p.
specialize (IHn la lb lc) as H1.
now destruct H1.
Defined.


Theorem list_decode_encode {A} {la lb : list A} :
  ∀ lc, list_decode la lb (list_encode la lb lc) = lc.
Proof.
intros lc.
destruct lc; simpl; unfold id; simpl.
induction la; [ reflexivity | simpl ].
now rewrite IHla.
Defined.

Theorem list_encode_decode {A} {la lb : list A} :
  ∀ lc, list_encode la lb (list_decode la lb lc) = lc.
Proof.
intros.
revert lb lc.
induction la as [| a la]; intros. {
  destruct lb; [ now destruct lc | easy ].
}
destruct lb as [| b lb]; [ easy | ].
cbn in lc.
destruct lc as (p, lc).
destruct p.
specialize (IHla lb lc) as H1; simpl.
remember (list_decode la lb lc) as d eqn:Hd.
destruct d; cbn.
rewrite <- H1.
now unfold id.
Defined.

Theorem equiv_eq_list_code {A} : ∀ la lb : list A,
  equivalence (la = lb) (list_code la lb).
Proof.
intros.
exists (list_encode la lb); apply qinv_isequiv.
exists (list_decode la lb).
unfold composite, homotopy, id; simpl.
split; intros p; [ apply list_encode_decode | apply list_decode_encode ].
Defined.

Tactic Notation "transparent" "assert" "(" ident(H) ":" lconstr(type) ")" :=
  unshelve (refine (let H := (_ : type) in _)).

Definition list_code_equiv_1_or_0 {A}
    (eq_dec : ∀ a b : A, {a = b} + {a ≠ b}) :
  isSet A → ∀ (la lb : list A),
  equivalence (list_code la lb) True + equivalence (list_code la lb) False.
Proof.
intros HA *.
revert lb.
induction la as [| a la]; intros. {
  destruct lb as [| b lb]. {
    left; cbn.
    unfold equivalence, isequiv, homotopy, composite, id.
    exists id; unfold id.
    now split; exists id; unfold id.
  }
  right; cbn.
  unfold equivalence, isequiv, homotopy, composite, id.
  exists id; unfold id.
  now split; exists id; unfold id.
}
destruct lb as [| b lb]. {
  right; cbn.
  unfold equivalence, isequiv, homotopy, composite, id.
  exists id; unfold id.
  now split; exists id; unfold id.
}
cbn.
specialize (IHla lb) as H1.
unfold equivalence in H1 |-*.
destruct (eq_dec a b) as [p| p]. 2: {
  right.
  exists (λ X, match p (fst X) with end).
  apply qinv_isequiv.
  exists (λ H : False, match H with end).
  unfold homotopy, composite, id.
  split; [ now intros | ].
  now intros (q, Hq).
}
left.
transparent assert (f : (a = b) * list_code la lb → True). {
  intros (q, Hq).
  destruct H1 as [H1| H1]. {
    apply (projT1 H1), Hq.
  }
  now specialize (projT1 H1 Hq).
}
exists f; subst f; cbn.
apply qinv_isequiv.
unfold qinv.
destruct H1 as [H1| H1]. {
  specialize (projT2 H1) as H2; cbn in H2.
  unfold isequiv in H2.
  destruct H2 as ((g, Hg), (h, Hh)).
  move h before g.
  transparent assert (g' : True → (a = b) * list_code la lb). {
    intros H.
    split; [ apply p | apply g, H ].
  }
  exists g'; subst g'.
  unfold homotopy, composite, id; cbn.
  split. {
    intros H.
    now destruct (projT1 H1 (g H)), H.
  }
  intros (i, Hi).
  move i before p.
  destruct (HA _ _ p i).
  apply f_equal.
  unfold homotopy, composite, id in Hg, Hh; cbn in Hg, Hh.
  rewrite <- Hh.
  destruct H1.
  cbn in *.
...
destruct H1 as [H1| H1].
-destruct (eq_dec a b) as [p| p]. {
   destruct H1 as (f & Hf).
   destruct p.
...
   left.
   exists (λ X, f (snd X)).
   apply qinv_isequiv.
   unfold qinv.
   unfold homotopy, composite, id; cbn.
   transparent assert (g : True → (a = b) * list_code la lb). {
     intros _.
     split; [ easy | ].
     unfold isequiv in Hf.
     destruct Hf as ((g, Hg) & (h, Hh)).
     now apply g.
   }
   exists g; subst g; cbn.
   split. {
     intros x.
     destruct Hf as ((g, Hg) & (h, Hh)).
     now destruct (f (g I)), x.
   }
   intros (q, Hq).
   destruct Hf as ((g, Hg) & (h, Hh)).
   move h before g.
   unfold homotopy, composite, id in Hg, Hh.
   specialize (list_decode la lb Hq) as H1.
   destruct H1.
   assert (g I = Hq). {
Search list_code.
Print list_r.
...
   split; [ now intros; destruct x | ].
   intros (q, Hq).
   destruct Hf as ((g, Hg) & (h, Hh)).
...
   exists (λ _, I).
   apply qinv_isequiv.
   unfold qinv.
   unfold homotopy, composite, id; cbn.
   transparent assert (g : True → (a = b) * list_code la lb). {
     intros _.
     split; [ easy | ].
     unfold isequiv in Hf.
     destruct Hf as ((g, Hg) & (h, Hh)).
     now apply g.
   }
   exists g.

   subst g; cbn.
   split; [ now intros; destruct x | ].
   intros (q, Hq).
   destruct Hf as ((g, Hg) & (h, Hh)).
...
-destruct H1 as (f & (g, Hg) & (h, Hh)).
 move h before g.
Check list_decode.
Check list_encode.
...
destruct (eq_nat_dec m n) as [H1| H1].
 left; subst m.
 exists (λ c, I); apply qinv_isequiv.
 exists (λ _, nat_r n).
 unfold composite, homotopy, id; simpl.
 split; [ intros u; destruct u; reflexivity | intros c ].
 induction n; [ destruct c; reflexivity | apply IHn ].

 right.
 exists (λ c, H1 (nat_decode m n c)); apply qinv_isequiv.
 exists (λ p : False, match p with end).
 unfold composite, homotopy, id.
 split; [ intros p; destruct p | ].
 intros c; destruct (H1 (nat_decode m n c)).
Defined.

...

Definition isSet_list {A} : (∀ a b : A, {a = b} + {a ≠ b})
  → isSet (list A).
Proof.
intros eq_dec la lb p q.
specialize (equiv_eq_list_code la lb) as r.
specialize (list_code_equiv_1_or_0 eq_dec la lb) as s.
destruct s as [s| s].
-eapply equiv_compose in s; [ | apply r ].
 destruct s as (f, ((g, Hg), (h, Hh))).
 unfold composite, homotopy, id in Hg, Hh.
 pose proof Hh p as Hp.
 pose proof Hh q as Hq.
 destruct (f p), (f q).
 subst p q; reflexivity.
-eapply equiv_compose in s; [ | apply r ].
 destruct s as (f, ((g, Hg), (h, Hh))).
 exfalso; apply f, p.
Defined.

...

Fixpoint list_code {A} (eq_dec : ∀ a b : A, {a = b} + {a ≠ b})
         (la lb : list A) : Type :=
  match (la, lb) with
  | ([], []) => True
  | (_ :: _, []) => False
  | ([], _ :: _) => False
  | (a :: la, b :: lb) => if eq_dec a b then list_code eq_dec la lb else False
  end.

(*
Fixpoint list_r {A} eq_dec (l : list A) : list_code eq_dec l l :=
  match l with
  | [] => I
  | a :: l => list_r eq_dec l
  end.
*)

Fixpoint list_r {A} eq_dec (l : list A) : list_code eq_dec l l :=
  match l with
  | [] => I
  | a :: l =>
      let s := eq_dec a a in
      match
        s return (if s then list_code eq_dec l l else False)
      with
      | left _ => list_r eq_dec l
      | right H => match H eq_refl with end
      end
  end.

Definition list_encode {A} eq_dec (la lb : list A) :
    la = lb → list_code eq_dec la lb :=
  λ p, transport (list_code eq_dec la) p (list_r eq_dec la).

Definition list_decode {A} eq_dec (la lb : list A) :
  list_code eq_dec la lb → la = lb.
Proof.
revert la lb.
fix IHn 1.
intros m n p.
destruct m.
 destruct n; [ reflexivity | refine (match p with end) ].

 destruct n; [ refine (match p with end) | simpl in p ].
 destruct (eq_dec a a0); [ | easy ].
 destruct e.
 now destruct (IHn m n p).
Defined.

Theorem list_decode_encode {A} eq_dec {la lb : list A} :
  ∀ lc, list_decode eq_dec la lb (list_encode eq_dec la lb lc) = lc.
Proof.
intros lc.
destruct lc; simpl; unfold id; simpl.
induction la; [ reflexivity | simpl ].
destruct (eq_dec a a); [ | easy ].
rewrite IHla.
...
destruct e.

now rewrite IHla.
Defined.

Theorem list_encode_decode {A} {m n : list A} :
  ∀ c, list_encode m n (list_decode m n c) = c.
Proof.
intros c.
revert n c; induction m; intros.
 simpl in c.
 destruct n, c; reflexivity.

 simpl in c.
 destruct n; [ refine (match c with end) | ].
 simpl.
 destruct c as (pa, pl).
 destruct pa.
Check @hott_2_3_10.
...
 rewrite <- (hott_2_3_10 S (nat_code (S m)) (nat_decode m n c)).
 apply IHm.
Defined.
