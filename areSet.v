(* proving nat and list are hSets *)

Set Universe Polymorphism.
Set Nested Proofs Allowed.

Require Import Utf8.
Require Import h4c.

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
destruct H1 as [H1| H1].
-left.
 transparent assert (f : (a = b) * list_code la lb → True). {
   intros (q, Hq).
   apply (projT1 H1), Hq.
 }
 exists f; subst f; cbn.
 apply qinv_isequiv.
 unfold qinv.
 specialize (projT2 H1) as H2; cbn in H2.
 apply isequiv_qinv in H2; unfold qinv in H2.
 unfold homotopy, composite, id in H2.
 destruct H2 as (g & Hg1 & Hg2).
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
 apply f_equal, Hg2.
-right.
 transparent assert (f : (a = b) * list_code la lb → False). {
   intros (q, Hq).
   apply (projT1 H1), Hq.
 }
 exists f; subst f; cbn.
 apply qinv_isequiv.
 unfold qinv.
 specialize (projT2 H1) as H2; cbn in H2.
 apply isequiv_qinv in H2; unfold qinv in H2.
 unfold homotopy, composite, id in H2.
 destruct H2 as (g & Hg1 & Hg2).
 transparent assert (g' : False → (a = b) * list_code la lb). {
   now intros H.
 }
 exists g'; subst g'.
 unfold homotopy, composite, id; cbn.
 split; [ now intros H | ].
 intros (i, Hi).
 destruct (projT1 H1 Hi).
Defined.

Definition isSet_list {A} : (∀ a b : A, {a = b} + {a ≠ b}) →
  isSet A → isSet (list A).
Proof.
intros eq_dec HA la lb p q.
specialize (equiv_eq_list_code la lb) as r.
specialize (list_code_equiv_1_or_0 eq_dec HA la lb) as s.
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
