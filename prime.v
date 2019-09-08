Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Notation "x ≤ y < z" := (x <= y ∧ y < z)%nat (at level 70, y at next level).
Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).

Fixpoint prime_test n d :=
  match d with
  | 0 | 1 => true
  | S d' =>
      match n mod d with
      | 0 => false
      | _ => prime_test n d'
      end
  end.

Definition is_prime n :=
  match n with
  | 0 | 1 => false
  | S n' => prime_test n n'
  end.

Theorem fold_mod_succ : ∀ n d, d - snd (Nat.divmod n d 0 d) = n mod (S d).
Proof. easy. Qed.

Theorem Nat_div_less_small : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a / b = n.
Proof.
intros * Hab.
assert (Hb : b ≠ 0). {
  now intros Hb; rewrite Hb, (Nat.mul_comm (n + 1)) in Hab.
}
replace a with (a - n * b + n * b) at 1 by now apply Nat.sub_add.
rewrite Nat.div_add; [ | easy ].
replace n with (0 + n) at 3 by easy; f_equal.
apply Nat.div_small.
apply Nat.add_lt_mono_r with (p := n * b).
rewrite Nat.add_comm in Hab; cbn in Hab.
now rewrite Nat.sub_add.
Qed.

Theorem not_prime_div : ∀ n d, 2 ≤ n → d < n →
  prime_test n d = false
  → ∃ m, is_prime m = true ∧ Nat.divide m n.
Proof.
intros * Hn Hd Hp.
revert n Hn Hd Hp.
induction d; intros; [ easy | ].
cbn in Hp.
rewrite fold_mod_succ in Hp.
destruct d; [ easy | ].
remember (n mod (S (S d))) as m eqn:Hm.
symmetry in Hm.
destruct m. {
  clear Hp.
  apply Nat.mod_divide in Hm; [ | easy ].
  remember (is_prime (S (S d))) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ now exists (S (S d)) | ].
  unfold is_prime in Hb.
  apply IHd in Hb; [ | flia | flia ].
  destruct Hb as (m & Hpm & Hmd).
  exists m.
  split; [ easy | ].
  now apply (Nat.divide_trans _ (S (S d))).
}
apply IHd in Hp; [ | easy | flia Hd ].
destruct Hp as (p & Hp & Hpn).
now exists p.
Qed.

Theorem not_prime : ∀ n, 2 ≤ n →
  is_prime n = false → ∃ d, is_prime d = true ∧ Nat.divide d n.
Proof.
intros * Hn Hp.
destruct n; [ flia Hn | ].
destruct n; [ flia Hn | ].
clear Hn.
unfold is_prime in Hp.
apply (not_prime_div _ (S n)); [ flia | flia | easy ].
Qed.

Theorem Nat_gcd_le_l : ∀ a b, a ≠ 0 → Nat.gcd a b ≤ a.
Proof.
intros * Ha.
specialize (Nat.gcd_divide_l a b) as (c, Hc).
rewrite <- Nat.mul_1_l at 1.
rewrite Hc at 2.
apply Nat.mul_le_mono_pos_r.
-apply Nat.neq_0_lt_0.
 intros H.
 now apply Nat.gcd_eq_0_l in H.
-destruct c; [ easy | ].
 apply -> Nat.succ_le_mono.
 apply Nat.le_0_l.
Qed.

Theorem Nat_gcd_le_r : ∀ a b, b ≠ 0 → Nat.gcd a b ≤ b.
Proof.
intros * Hb.
rewrite Nat.gcd_comm.
now apply Nat_gcd_le_l.
Qed.

Theorem Nat_fact_succ : ∀ n, fact (S n) = S n * fact n.
Proof. easy. Qed.

Theorem Nat_fact_1 : fact 1 = 1.
Proof. easy. Qed.

Theorem Nat_divide_fact_fact : ∀ n d, Nat.divide (fact (n - d)) (fact n).
Proof.
intros *.
revert n.
induction d; intros; [ rewrite Nat.sub_0_r; apply Nat.divide_refl | ].
destruct n; [ apply Nat.divide_refl | ].
rewrite Nat.sub_succ.
apply (Nat.divide_trans _ (fact n)); [ apply IHd | ].
rewrite Nat_fact_succ.
now exists (S n).
Qed.

Theorem Nat_divide_fact_le : ∀ n d, d ≤ n → Nat.divide (fact d) (fact n).
Proof.
intros * Hdn.
replace d with (n - (n - d)) by flia Hdn.
apply Nat_divide_fact_fact.
Qed.

Theorem Nat_eq_fact_mod_0 : ∀ n d, d ≤ n → fact n mod fact d = 0.
Proof.
intros * Hdn.
apply Nat.mod_divide; [ apply fact_neq_0 | ].
now apply Nat_divide_fact_le.
Qed.

Theorem Nat_fact_mul_div : ∀ n d, d ≤ n → fact n = fact d * (fact n / fact d).
Proof.
intros * Hdn.
specialize (Nat.div_mod (fact n) (fact d) (fact_neq_0 _)) as H1.
rewrite Nat_eq_fact_mod_0 in H1; [ | easy ].
now rewrite Nat.add_0_r in H1.
Qed.

Theorem Nat_gcd_fact : ∀ n d, 1 ≤ d ≤ n → Nat.gcd (fact n) d = d.
Proof.
intros * (Hd, Hdn).
rewrite Nat.gcd_comm.
apply Nat.divide_gcd_iff'.
exists (fact (d - 1) * (fact n / fact d)).
rewrite Nat.mul_shuffle0.
replace (fact (d - 1) * d) with (fact d). 2: {
  destruct d; [ easy | cbn ].
  rewrite Nat.sub_0_r, Nat.mul_succ_r; flia.
}
now apply Nat_fact_mul_div.
Qed.

Theorem Nat_div_gcd_fact : ∀ n d, 1 ≤ d ≤ n → d / Nat.gcd (fact n) d = 1.
Proof.
intros * (Hd, Hdn).
apply Nat_div_less_small.
rewrite Nat.mul_1_l.
split; [ apply Nat_gcd_le_r; flia Hd | ].
apply (lt_le_trans _ (2 * d)); [ flia Hd | ].
apply Nat.mul_le_mono_l.
now rewrite Nat_gcd_fact.
Qed.

Theorem Nat_fact_divides_small : ∀ n d,
  1 ≤ d ≤ n
  → fact n = fact n / d * d.
Proof.
intros * (Hd, Hdn).
replace d with (Nat.gcd (fact n) d) at 1. 2: {
  now apply Nat_gcd_fact.
}
rewrite Nat.gcd_div_swap.
replace (d / Nat.gcd (fact n) d) with 1. 2: {
  symmetry.
  now apply Nat_div_gcd_fact.
}
symmetry; apply Nat.mul_1_r.
Qed.

Theorem infinite_primes : ∀ n, ∃ m, m > n ∧ is_prime m = true.
Proof.
intros.
set (fn := fact n + 1).
remember (is_prime fn) as pfn eqn:Hpfn.
symmetry in Hpfn.
destruct pfn.
-exists fn.
 split; [ | easy ].
 subst fn; clear Hpfn.
 induction n; [ flia | cbn ].
 rewrite <- (Nat.add_1_r n).
 apply Nat.add_lt_mono_r.
 destruct n; [ cbn; flia | ].
 apply (lt_le_trans _ (fact (S n) + 1)). {
   cbn.
   rewrite <- Nat.add_1_r.
   apply Nat.add_lt_mono_r.
   cbn in IHn; flia IHn.
 }
 apply Nat.add_le_mono_l; cbn.
 specialize (fact_neq_0 n) as H.
 remember (fact n) as m eqn:Hm.
 destruct m; [ easy | flia ].
-destruct n; [ now subst fn | ].
 apply not_prime in Hpfn. 2: {
   clear Hpfn; subst fn; cbn.
   specialize (fact_neq_0 n) as H1.
   flia H1.
 }
 destruct Hpfn as (d & Hd & Hdn).
 exists d.
 split; [ | easy ].
 destruct Hdn as (z & Hz).
 subst fn.
 destruct (lt_dec (S n) d) as [Hnd| Hnd]; [ easy | ].
 apply Nat.nlt_ge in Hnd; exfalso.
 assert (Ht : Nat.divide d (fact (S n))). {
   exists (fact (S n) / d).
   apply Nat_fact_divides_small.
   split; [ | easy ].
   destruct d; [ easy | flia ].
 }
 destruct Ht as (t, Ht).
 rewrite Ht in Hz.
 apply Nat.add_sub_eq_l in Hz.
 rewrite <- Nat.mul_sub_distr_r in Hz.
 apply Nat.eq_mul_1 in Hz.
 now destruct Hz as (Hz, H); subst d.
Qed.
