(* borrowed from ClassicalFacts.v in Coq library *)
(* and simplified *)

Require Import Utf8.

Definition prop_extensionality := ∀ A B : Prop, A ↔ B → A = B.
Definition proof_irrelevance := ∀ (A : Prop) (a1 a2 : A), a1 = a2.

Inductive boolP : Prop :=
  | trueP : boolP
  | falseP : boolP.

Record retract (A B : Prop) : Prop :=
  { f1 : A → B;
    f2 : B → A;
    f1_o_f2 : ∀ x : B, f1 (f2 x) = x }.

Record has_fixpoint (A : Prop) : Prop :=
  { F : (A → A) → A;
    Fix : ∀ f : A → A, F f = f (F f) }.

Theorem prop_ext_A_eq_A_imp_A :
  prop_extensionality → ∀ A : Prop, A → (A → A) = A.
Proof.
intros Ext A a.
apply (Ext (A -> A) A); split; [ exact (λ _, a) | exact (λ _ _, a) ].
Qed.

Theorem prop_ext_retract_A_A_imp_A :
  prop_extensionality → ∀ A : Prop, A → retract A (A → A).
Proof.
intros Ext A a.
rewrite (prop_ext_A_eq_A_imp_A Ext A a).
exists (λ x : A, x) (λ x : A, x).
reflexivity.
Qed.

Theorem ext_prop_fixpoint :
  prop_extensionality -> ∀ A : Prop, A -> has_fixpoint A.
Proof.
intros Ext A a.
case (prop_ext_retract_A_A_imp_A Ext A a); intros g1 g2 g1_o_g2.
exists (λ f, (λ x : A, f (g1 x x)) (g2 (λ x, f (g1 x x)))).
intro f.
pattern (g1 (g2 (λ x : A, f (g1 x x)))) at 1.
rewrite (g1_o_g2 (λ x : A, f (g1 x x))).
reflexivity.
Qed.

Theorem aux : prop_extensionality → trueP = falseP.
Proof.
intros * Ext.
assert (Ind : ∀ P : boolP → Prop, P trueP → P falseP → ∀ b, P b). {
  now intros; destruct b.
}
specialize (ext_prop_fixpoint Ext boolP trueP) as G.
destruct G as (G, Gfix).
set (neg := λ b : boolP, boolP_ind boolP falseP trueP b).
generalize (eq_refl (G neg)).
pattern (G neg) at 1.
apply Ind; intros Heq.
-change (trueP = neg trueP); rewrite Heq; apply Gfix.
-change (neg falseP = falseP); rewrite Heq; symmetry; apply Gfix.
Qed.

Theorem ext_prop_dep_proof_irrel : prop_extensionality → proof_irrelevance.
Proof.
intros * Ext A a1 a2.
set (f := λ b : boolP, boolP_ind A a1 a2 b).
change (f trueP = f falseP).
rewrite (aux Ext).
reflexivity.
Qed.
