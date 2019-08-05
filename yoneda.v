(* Yoneda lemma *)

Set Universe Polymorphism.
Require Import Utf8.
Require Import category.

(*
  Let F be an arbitrary functor from C to SetCat. Then Yoneda's lemma
  says that: (h^A being the cov_hom_functor defined in category.v)

  For each object A of C, the natural transformations from h^A to F
  are in one-to-one correspondence with the elements of F(A). That is,
     Nat (h^A, F) ≅ F (A)

  [...]

  (wikipedia)
*)

Definition Yoneda_NT_FA {C} (F : functor C SetCat) (A : Ob C) :
  natural_transformation (cov_hom_functor A) F → st_type (f_obj F A) :=
  λ Φ, nt_component Φ A (idc A) : st_type (f_obj F A).

Definition Yoneda_FA_NT {C} (F : functor C SetCat) (A : Ob C) :
  st_type (f_obj F A) → natural_transformation (cov_hom_functor A) F.
Proof.
intros u.
set (ϑ := λ (X : Ob C) (f : Hom A X), f_hom F f u).
assert (Hϑ :
  ∀ (X Y : Ob C) (f : Hom X Y),
  (λ g : Hom A X, ϑ Y (f ◦ g)) =
  (λ g : Hom A X, f_hom F f (ϑ X g))). {
  intros.
  apply fun_ext; intros g.
  unfold ϑ; cbn.
  now rewrite f_comp_prop.
}
apply (existT _ ϑ Hϑ).
Defined.

Lemma Yoneda {C} (F : functor C SetCat) (A : Ob C) :
  let NT := natural_transformation (cov_hom_functor A) F in
  let FA := st_type (f_obj F A) in
  ∃ f : NT → FA, ∃ g : FA → NT,
  (∀ x : NT, g (f x) = x) ∧ (∀ y : FA, f (g y) = y).
Proof.
intros.
exists (Yoneda_NT_FA F A).
exists (Yoneda_FA_NT F A).
split.
-intros (η, Hη); cbn.
 apply eq_existT_uncurried.
 assert (p : (λ X f, f_hom F f (η A (idc A))) = η). {
   apply fun_ext; intros X.
   apply fun_ext; intros f.
   specialize (Hη A X f) as H1; cbn in H1.
   specialize (@h4c.happly _ _ _ _ H1 (idc A)) as H2.
   cbn in H2.
   now rewrite unit_l in H2.
 }
 exists p.
 apply fun_ext; intros X.
 apply fun_ext; intros Y.
 apply fun_ext; intros f.
 apply h4c.isSet_forall.
 intros g.
 apply st_is_set.
-intros u; cbn.
 now rewrite f_id_prop; cbn.
Qed.

(*
  [...]

     Nat (h^A, F) ≅ F (A)

  Moreover this isomorphism is natural in A and F when both sides are
  regarded as functors from Set^C x C to Set. (Here the notation Set^C
  denotes the category of functors from C to Set.)
*)

Definition SetC_C (C : category) := cat_prod (FunCat C SetCat) C.

Definition functor_SetC_C_Set1_map_hom {C} (D := SetC_C C) (X Y : Ob D)
  (f : Hom X Y) : Hom (f_obj (fst X) (snd X)) (f_obj (fst Y) (snd Y)).
Proof.
cbn in X, Y, f.
intros T.
destruct X as (F, A).
destruct Y as (G, B).
destruct f as (f, g).
now apply f, (f_hom F g).
Defined.

Theorem functor_SetC_C_Set1_comp_prop {C} (D := SetC_C C) (X Y Z : Ob D)
  (f : Hom X Y) (g : Hom Y Z) :
  functor_SetC_C_Set1_map_hom X Z (g ◦ f) =
  functor_SetC_C_Set1_map_hom Y Z g ◦ functor_SetC_C_Set1_map_hom X Y f.
Proof.
cbn in *.
destruct X as (F, X).
destruct Y as (G, Y).
destruct Z as (H, Z); cbn in *.
destruct f as (η, f).
destruct g as (η', g).
move η' before η; cbn.
apply fun_ext; intros T; cbn.
rewrite f_comp_prop; cbn.
destruct η' as (η', η'_prop).
destruct η as (η, η_prop).
cbn in *.
apply f_equal.
specialize (η_prop Y Z g) as H1.
now specialize (@h4c.happly _ _ _ _ H1 (f_hom F f T)) as H2.
Qed.

Theorem functor_SetC_C_Set1_id_prop {C} (D := SetC_C C) (X : Ob D) :
  functor_SetC_C_Set1_map_hom X X (idc X) = idc (f_obj (fst X) (snd X)).
Proof.
cbn in *.
destruct X as (F, X); cbn.
apply fun_ext; intros T; cbn.
now rewrite f_id_prop.
Qed.

Definition functor_SetC_C_Set1 C : functor (SetC_C C) SetCat :=
  {| f_obj (X : Ob (SetC_C C)) := f_obj (fst X) (snd X);
     f_hom := functor_SetC_C_Set1_map_hom;
     f_comp_prop := functor_SetC_C_Set1_comp_prop;
     f_id_prop := functor_SetC_C_Set1_id_prop |}.

Definition functor_SetC_C_Set2_map_obj {C} (A : Ob (SetC_C C)) : Ob SetCat.
Proof.
exists (natural_transformation (cov_hom_functor (snd A)) (fst A)).
apply Fun_Hom_set.
Defined.

Definition functor_SetC_C_Set2_map_hom {C} (X Y : Ob (SetC_C C))
    (f : Hom X Y) :
  Hom (functor_SetC_C_Set2_map_obj X) (functor_SetC_C_Set2_map_obj Y).
Proof.
cbn; intros η.
set (ϑ := λ A g, projT1 (fst f) A (projT1 η A (g ◦ snd f))).
exists ϑ.
intros Z T h.
apply fun_ext; intros g; cbn; cbn in h, ϑ.
specialize (ϑ T (comp g h)) as H1.
unfold ϑ.
destruct X as (F, X).
destruct Y as (G, Y).
move G before F.
cbn in *.
destruct f as (η', f).
move η after η'.
move Z before Y; move T before Z.
move g before f; move h before g.
cbn in *.
specialize @nat_transf_comp_nt_commute as H2.
specialize (H2 C SetCat (cov_hom_functor X) F G η η' Z T h).
cbn in H2.
unfold nt_component in H2.
specialize (@h4c.happly _ _ _ _ H2 (g ◦ f)) as H3.
cbn in H3.
etransitivity; [ | apply H3 ].
do 2 apply f_equal.
apply assoc.
Defined.

Theorem functor_SetC_C_Set2_comp_prop {C} (X Y Z : Ob (SetC_C C))
    (f : Hom X Y) (g : Hom Y Z) :
  functor_SetC_C_Set2_map_hom X Z (g ◦ f) =
  functor_SetC_C_Set2_map_hom Y Z g ◦ functor_SetC_C_Set2_map_hom X Y f.
Proof.
apply fun_ext; intros η.
unfold functor_SetC_C_Set2_map_hom; cbn.
apply eq_existT_uncurried.
destruct f as (η', f).
destruct g as (η'', g); cbn in η, η', η'', f, g |-*.
move η after η'; move η'' before η'.
destruct X as (F, X).
destruct Y as (G, Y).
destruct Z as (H, Z).
move Y before X; move Z before Y; move g before f.
move G before F; move H before G.
cbn in *.
unfold nt_component.
assert (p
  : (λ (A : Ob C) (g0 : Hom Z A),
       projT1 η'' A (projT1 η' A (projT1 η A (g0 ◦ (g ◦ f))))) =
    (λ (A : Ob C) (g0 : Hom Z A),
       projT1 η'' A (projT1 η' A (projT1 η A (g0 ◦ g ◦ f))))). {
  apply fun_ext; intros A.
  apply fun_ext; intros h.
  do 3 apply f_equal.
  symmetry; apply assoc.
}
exists p; cbn.
apply fun_ext; intros A.
apply fun_ext; intros B.
apply fun_ext; intros h.
apply h4c.isSet_forall.
intros i.
now destruct (f_obj H B).
Qed.

Theorem functor_SetC_C_Set2_id_prop {C} (X : Ob (SetC_C C)) :
  functor_SetC_C_Set2_map_hom X X (idc X) = idc (functor_SetC_C_Set2_map_obj X).
Proof.
apply fun_ext; intros η; cbn.
destruct η as (η, Hη); cbn in *.
unfold functor_SetC_C_Set2_map_hom; cbn.
apply eq_existT_uncurried; cbn.
assert (p : (λ (A : Ob C) (g : Hom (snd X) A), η A (g ◦ idc (snd X))) = η). {
  apply fun_ext; intros A.
  apply fun_ext; intros f.
  now rewrite unit_l.
}
exists p; cbn.
apply fun_ext; intros Y.
apply fun_ext; intros Z.
apply fun_ext; intros f.
apply h4c.isSet_forall.
intros i.
now destruct (f_obj (fst X) Z).
Qed.

Definition functor_SetC_C_Set2 C : functor (SetC_C C) SetCat :=
  {| f_obj := functor_SetC_C_Set2_map_obj;
     f_hom := functor_SetC_C_Set2_map_hom;
     f_comp_prop := functor_SetC_C_Set2_comp_prop;
     f_id_prop := functor_SetC_C_Set2_id_prop |}.

Theorem Yoneda_natural {C} :
  natural_transformation (functor_SetC_C_Set1 C) (functor_SetC_C_Set2 C).
Proof.
unfold natural_transformation; cbn.
set (ϑ :=
  λ F : functor C SetCat * Ob C,
  let (F, A) as p
    return
      (st_type (f_obj (fst p) (snd p))
      → natural_transformation (cov_hom_functor (snd p)) (fst p)) := F
  in
  λ T : st_type (f_obj F A),
  let ϑ := λ (X : Ob C) (f : Hom A X), f_hom F f T in
  existT _ ϑ
    (λ (X Y : Ob C) (f : Hom X Y),
     fun_ext _
       (λ _ : Hom A X, st_type (f_obj F Y)) (λ HA : Hom A X, ϑ Y (f ◦ HA))
       (λ HA : Hom A X, f_hom F f (ϑ X HA))
       (λ g : Hom A X,
        eq_ind_r
          (λ h : Hom (f_obj F A) (f_obj F Y),
           h T = f_hom F f (f_hom F g T))
          eq_refl (f_comp_prop g f)))).
exists ϑ.
intros F G η.
apply fun_ext; intros T.
unfold ϑ; cbn.
destruct F as (F, A).
destruct G as (G, B).
unfold functor_SetC_C_Set2_map_hom; cbn.
apply eq_existT_uncurried; cbn.
assert (p :
   (λ (X : Ob C) (f1 : Hom B X),
    f_hom G f1 (let (f2, g) := η in (projT1 f2) B (f_hom F g T))) =
   (λ (A : Ob C) (g : Hom B A),
    projT1 (fst η) A (f_hom F (g ◦ snd η) T))). {
  apply fun_ext; intros X.
  apply fun_ext; intros f.
  destruct η as (η, g); cbn in *.
  destruct η as (η, Hη); cbn.
  rewrite f_comp_prop; cbn.
  specialize (Hη B X f) as H1; cbn in H1.
  specialize (@h4c.happly _ _ _ _ H1) as H2; cbn in H2.
  symmetry; apply H2.
}
exists p.
cbn.
apply fun_ext; intros X.
apply fun_ext; intros Y.
apply fun_ext; intros g.
apply h4c.isSet_forall.
intros h.
now destruct (f_obj G Y).
Qed.
