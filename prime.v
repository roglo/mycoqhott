Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

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
 destruct z; [ flia Hz | ].
 apply (Nat.mul_lt_mono_pos_l (S z)); [ flia | ].
 rewrite <- Hz.
...
