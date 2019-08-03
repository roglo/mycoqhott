(* categories: adjunction *)

Set Universe Polymorphism.
Require Import Utf8.
Require Import category.

(* left whiskering *)

Definition left_whiskering_nt_component {C D E} {G H : functor D E}
  (α : natural_transformation G H) (F : functor C D) X :=
  nt_component α (f_map_obj F X).

Definition left_whiskering_nt_commute {C D E} {G H : functor D E}
  (α : natural_transformation G H) (F : functor C D) X Y f :
    left_whiskering_nt_component α F Y ◦ f_map_hom G (f_map_hom F f) =
    f_map_hom H (f_map_hom F f) ◦ left_whiskering_nt_component α F X :=
  nt_commute α (f_map_obj F X) (f_map_obj F Y) (f_map_hom F f).

Definition left_whiskering {C D E} {G H : functor D E} :
  natural_transformation G H → ∀ (F : functor C D),
  natural_transformation (functor_comp F G) (functor_comp F H) :=
  λ α F,
  existT _
    (left_whiskering_nt_component α F)
    (left_whiskering_nt_commute α F).

(* right whiskering *)

Definition right_whiskering_nt_component {D E F} {G H : functor D E}
  (I : functor E F) (α : natural_transformation G H) Y :=
  f_map_hom I (nt_component α Y).

Definition right_whiskering_nt_commute {D E F} {G H : functor D E}
  (I : functor E F) (α : natural_transformation G H) X Y f :
    right_whiskering_nt_component I α Y ◦ f_map_hom (functor_comp G I) f =
    f_map_hom (functor_comp H I) f ◦ right_whiskering_nt_component I α X.
Proof.
unfold right_whiskering_nt_component, nt_component; cbn.
do 2 rewrite <- f_comp_prop.
now destruct (nt_commute α X Y f).
(* formula not symmetric with left_whiskering_nt_commute; is it normal? *)
Defined.

Definition right_whiskering {D E F} {G H : functor D E} :
  ∀ (I : functor E F) (α : natural_transformation G H),
  natural_transformation (functor_comp G I) (functor_comp H I) :=
  λ I α,
  existT _
    (right_whiskering_nt_component I α)
    (right_whiskering_nt_commute I α).

(*
   adjunction: 1st definition

   An adjunction between categories C and D is a pair of functors
   (assumed to be covariant)
      R : D → C and L : C → D
   and, for all objects X in C and Y in D a bijection between
   the respective morphism sets
      Hom_C (R Y, X) ≅ Hom_D (Y, L X)
   such that this family of bijections is natural in X and Y.
   (Wikipedia)
*)

Definition adjunction {C D} (R : functor C D) (L : functor D C)
  (ϑ :
    natural_transformation
      (hom_functor D ◦ (fop R × 1 D))%Fun
      (hom_functor C ◦ (1 (op C) × L))%Fun) :=
  is_natural_isomorphism ϑ.

Definition are_adjoint {C D} (R : functor C D) (L : functor D C) :=
  { ϑ & adjunction R L ϑ }.

Definition is_right_adjoint {C D} (R : functor C D) :=
  { L & are_adjoint R L }.

Definition is_left_adjoint {C D} (L : functor D C) :=
  { R & are_adjoint R L }.

Notation "L ⊣ R" := (are_adjoint R L) (at level 70).

(* adjunction: 2nd definition *)

Definition adjunction2 {C D} (R : functor C D) (L : functor D C)
    (η : natural_transformation (1 C) (L ◦ R))
    (ε : natural_transformation (R ◦ L) (1 D)) :=
  (right_whiskering L ε ◦ left_whiskering η L = nat_transf_id L)%NT ∧
  (left_whiskering ε R ◦ right_whiskering R η = nat_transf_id R)%NT.

Definition are_adjoint2 {C D} (R : functor C D) (L : functor D C) :=
  { η & { ε & adjunction2 R L η ε }}.

Definition is_right_adjoint2 {C D} (R : functor C D) :=
  ∃ L η ε, adjunction2 R L η ε.

Definition is_left_adjoint2 {C D} (L : functor D C) :=
  ∃ R η ε, adjunction2 R L η ε.

(**)

Definition fc_map_obj_map_obj {A B C} (F : functor (A × B) C)
  (X : Ob A) (Y : Ob B) : Ob C.
Proof.
now apply F.
Defined.

Definition fc_map_obj_map_hom {A B C} (F : functor (A × B) C)
  (X : Ob A) {Y Y' : Ob B} (f : Hom Y Y') :
  Hom (fc_map_obj_map_obj F X Y) (fc_map_obj_map_obj F X Y').
Proof.
apply f_map_hom; cbn.
split; [ apply idc | easy ].
Defined.

Theorem fc_map_obj_comp_prop {A B C} (F : functor (A × B) C)
  (X : Ob A) {Y Y' Y'' : Ob B} (f : Hom Y Y') (g : Hom Y' Y'') :
  fc_map_obj_map_hom F X (g ◦ f) =
  fc_map_obj_map_hom F X g ◦ fc_map_obj_map_hom F X f.
Proof.
specialize (@f_comp_prop _ _ F (X, Y) (X, Y') (X, Y'')) as H1.
specialize (H1 (idc _, f) (idc _, g)); cbn in H1.
now rewrite unit_l in H1.
Qed.

Theorem fc_map_obj_id_prop {A B C} (F : functor (A × B) C)
  (X : Ob A) (Y : Ob B) :
  fc_map_obj_map_hom F X (idc Y) = idc (fc_map_obj_map_obj F X Y).
Proof.
apply (@f_id_prop _ _ F (X, Y)).
Qed.

Definition fc_map_obj {A B C} (F : functor (A × B) C) (X : Ob A) :
  Ob (FunCat B C) :=
  {| f_map_obj := fc_map_obj_map_obj F X;
     f_map_hom _ _ := fc_map_obj_map_hom F X;
     f_comp_prop _ _ _ := fc_map_obj_comp_prop F X;
     f_id_prop := fc_map_obj_id_prop F X |}.

Definition fc_map_hom {A B C} (F : functor (A × B) C) {X X' : Ob A}
  (f : Hom X X') :
  Hom (fc_map_obj F X) (fc_map_obj F X').
Proof.
transparent assert
  (ϑ : ∀ Y, Hom (fc_map_obj_map_obj F X Y) (fc_map_obj_map_obj F X' Y)). {
  intros.
  apply f_map_hom.
  split; [ easy | apply idc ].
}
exists ϑ; unfold ϑ; cbn.
intros Y Y' g.
unfold fc_map_obj_map_hom; cbn.
unfold fc_map_obj_map_obj.
specialize (@f_comp_prop _ _ F (X, Y) (X', Y) (X', Y')) as H1; cbn in H1.
specialize (H1 (f, idc _) (idc _, g)); cbn in H1.
specialize (@ f_comp_prop _ _ F (X, Y) (X, Y') (X', Y')) as H2; cbn in H2.
specialize (H2 (idc _, g) (f, idc _)); cbn in H2.
etransitivity.
-symmetry; apply H2.
-etransitivity; [ | apply H1 ].
 apply f_equal; f_equal.
 +etransitivity; [ apply unit_l | ].
  symmetry; apply unit_r.
 +etransitivity; [ apply unit_r | ].
  symmetry; apply unit_l.
Defined.

Theorem fc_comp_prop {A B C} (F : functor (A × B) C)
  {X X' X'' : Ob A} (f : Hom X X') (g : Hom X' X'') :
  fc_map_hom F (g ◦ f) = fc_map_hom F g ◦ fc_map_hom F f.
Proof.
apply eq_existT_uncurried.
assert
 (p :
  (λ Y, @f_map_hom _ _ F (X, Y) (X'', Y) (g ◦ f, idc Y)) =
  (λ Y,
   @f_map_hom _ _ F (X', Y) (X'', Y)
     (g, idc Y) ◦ @f_map_hom _ _ F (X, Y) (X', Y) (f, idc Y))). {
  apply fun_ext; intros Y.
  specialize (@f_comp_prop _ _ F (X, Y) (X', Y) (X'', Y)) as H1; cbn in H1.
  specialize (H1 (f, idc _) (g, idc _)); cbn in H1.
  now rewrite unit_l in H1.
}
exists p; cbn.
apply fun_ext; intros Y.
apply fun_ext; intros Y'.
apply fun_ext; intros h.
apply Hom_set.
Qed.

Theorem fc_id_prop {A B C} (F : functor (A × B) C) (X : Ob A) :
  fc_map_hom F (idc X) = idc (fc_map_obj F X).
Proof.
apply eq_existT_uncurried; cbn.
assert
  (p :
     (λ Y, @f_map_hom _ _ F (X, Y) (X, Y) (idc X, idc Y)) =
     (λ Y, idc (fc_map_obj_map_obj F X Y))). {
  apply fun_ext; intros Y.
  apply (@f_id_prop _ _ F).
}
exists p; cbn.
apply fun_ext; intros Y.
apply fun_ext; intros Y'.
apply fun_ext; intros f.
apply Hom_set.
Qed.

Definition functor_curry {A B C} (F : functor (A × B) C) :
  functor A (FunCat B C) :=
  {| f_map_obj := fc_map_obj F;
     f_map_hom _ _ := fc_map_hom F;
     f_comp_prop _ _ _ := fc_comp_prop F;
     f_id_prop := fc_id_prop F |}.

(* equivalence between both definitions of adjunction *)

(**)
Theorem adj_adj {C D} (R : functor C D) (L : functor D C) :
  (are_adjoint R L → are_adjoint2 R L) *
  (are_adjoint2 R L → are_adjoint R L).
Proof.
split.
-intros Ha.
 unfold are_adjoint, adjunction in Ha.
 unfold are_adjoint2, adjunction2.
 destruct Ha as (ϑ, Hiso).
 assert (η : natural_transformation (1 C) (L ◦ R)). {
   transparent assert
      (α : ∀ x : Ob C, Hom (f_map_obj (1 C) x) (f_map_obj (L ◦ R) x)). {
     intros X; cbn.
     apply (nt_component ϑ (X, f_map_obj R X)), idc.
   }
   exists α; cbn in α.
   intros X X' f; cbn; cbn in α.
   subst α; cbn.
   destruct ϑ as (ϑ, Hϑ).
   cbn in ϑ, Hϑ |-*.
   specialize (Hϑ (X', f_map_obj R X') (X, f_map_obj R X')) as H; cbn in H.
   specialize (H (f, idc _)); cbn in H.
   specialize (@h4c.happly _ _ _ _ H) as H1; cbn in H1; clear H.
   specialize (H1 (idc _)); cbn in H1.
   specialize (Hϑ (X, f_map_obj R X) (X, f_map_obj R X')) as H; cbn in H.
   specialize (H (idc _, f_map_hom R f)); cbn in H.
   specialize (@h4c.happly _ _ _ _ H) as H2; cbn in H2; clear H.
   specialize (H2 (idc _)); cbn in H2.
   unfold hom_functor_map_hom in H1, H2; cbn in H1, H2.
   do 2 rewrite assoc in H1.
   remember
     (@comp _ _ _ (f_map_obj L (f_map_obj R X')) f
              (ϑ (X', f_map_obj R X') (idc (f_map_obj R X'))))
     as g eqn:Hg.
   assert (H :
     f_map_hom L (idc (f_map_obj R X')) ◦ g =
     f_map_hom L (idc (f_map_obj R X')) ◦
     f_map_hom L (f_map_hom R f) ◦
     ϑ (X, f_map_obj R X) (idc (f_map_obj R X))). {
     rewrite <- H1.
...
   unfold is_natural_isomorphism in Hiso; cbn in Hiso.
   unfold is_isomorphism in Hiso; cbn in Hiso.
...
