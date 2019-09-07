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

Theorem Nat_eq_div_1 : ∀ a b, b ≤ a < 2 * b → a / b = 1.
Proof.
intros * (Hba, Ha).
replace a with (a - b + 1 * b) by flia Hba.
rewrite Nat.div_add by (intros H; subst b; flia Ha).
replace 1 with (0 + 1) at 2 by easy.
apply Nat.add_cancel_r.
apply Nat.div_small.
flia Ha.
Qed.

Theorem div_gcd_fact : ∀ n d,
  1 ≤ d ≤ n
  → d / Nat.gcd (fact n) d = 1.
Proof.
intros * (Hd, Hdn).
apply Nat_eq_div_1.
split.
Search (Nat.gcd _ _ * _).
...
-apply Nat.gcd_le_r.
...
intros * (Hd, Hdn).
revert n Hdn.
induction d; intros; [ flia Hd | clear Hd ].
destruct d; [ now rewrite Nat.gcd_1_r | ].
assert (H : 1 ≤ S d) by flia.
specialize (IHd H); clear H.
destruct n; [ flia Hdn | ].
apply Nat.succ_le_mono in Hdn.
specialize (IHd _ Hdn).
Search (_ / _ = 1).
cbn.
,,,

Theorem fact_divides_small : ∀ n d,
  2 ≤ d ≤ n
  → fact n = fact n / d * d.
Proof.
intros * (Hd, Hdn).
replace d with (Nat.gcd (fact n) d) at 1. 2: {
  admit.
}
rewrite Nat.gcd_div_swap.
replace (d / Nat.gcd (fact n) d) with 1. 2: {
  symmetry.
...
  revert d Hd Hdn.
  induction n; intros; [ flia Hd Hdn | ].
Search (Nat.gcd (_ + _)).

...
  revert d Hd Hdn.
  induction n; intros; [ flia Hd Hdn | ].
  replace (fact (S n)) with (S n * fact n) by easy.
  destruct d; [ flia Hd | ].
  apply Nat.succ_le_mono in Hdn.
...


Search (_ / _ * _).

revert d Hd Hdn.
induction n; intros; [ flia Hd Hdn | ].
remember Nat.div as f; cbn; subst f.
destruct d; [ flia Hd | ].
apply Nat.succ_le_mono in Hdn.
destruct (lt_dec d 2) as [Hd2| Hd2]. {
  destruct d; [ flia Hd | ].
  destruct d; [ | flia Hd2 ].
  destruct n; [ flia Hdn | clear Hdn ].
  destruct n; [ easy | ].
  clear Hd Hd2.
  specialize (IHn 2 (le_refl _)).
  assert (H : 2 ≤ S (S n)) by flia.
  specialize (IHn H); clear H.

...

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
   destruct d; [ easy | ].
   destruct d; [ easy | ].
   clear - Hnd.
   assert (Hd : 2 ≤ S (S d)) by flia.
   assert (Hn : 1 ≤ S n) by flia.
   remember (S (S d)) as e.
   remember (S n) as m.
   clear n d Heqe Heqm.
   rename m into n; rename e into d.
...
   revert n Hnd.
   induction d; intros. {
     admit.
   }
   destruct n; [ flia Hnd | ].
   apply Nat.succ_le_mono in Hnd.
   specialize (IHd _ Hnd) as H1.
   remember (S n) as m.
   remember Nat.div as f; cbn; subst f m.

...
 destruct d; [ easy | ].
 destruct d; [ easy | ].
 destruct z; [ flia Hz | ].
 destruct z. {
   rewrite Nat.mul_1_l, <- (Nat.add_1_r (S d)) in Hz.
   assert (H : fact (S n) = S d) by flia Hz.
   clear Hz; rename H into Hz.
   apply -> Nat.succ_lt_mono.
   rewrite <- Hz.
...
