(* categories *)
(* http://angg.twu.net/tmp/2016-optativa/awodey__category_theory.pdf *)

Set Universe Polymorphism.
Require Import Utf8.
Require ClassicalFacts.
Require h4c.
Set Nested Proofs Allowed.

Definition isSet := h4c.isSet.
(*
Definition isProp := h4c.isProp.

Definition hProp := { A : Type & isProp A }.
*)

Axiom fun_ext : ∀ A B (f g : ∀ x : A, B x), (∀ x, f x = g x) → f = g.
(*
Axiom prop_ext : ∀ A B, (A ↔ B) → A = B.

Theorem proof_irrel : isSet Prop.
intros a1 a2.
apply (ClassicalFacts.ext_prop_dep_proof_irrel_cic prop_ext).
Qed.
*)

Declare Scope category_scope.
Declare Scope functor_scope.
Declare Scope nat_transf_scope.
Delimit Scope category_scope with Cat.
Delimit Scope functor_scope with Fun.
Delimit Scope nat_transf_scope with NT.

Class category :=
  { Ob : Type;
    Hom : Ob → Ob → Type;
    comp : ∀ {A B C}, Hom A B → Hom B C → Hom A C;
    idc : ∀ A, Hom A A;
    unit_l : ∀ {A B} (f : Hom A B), comp (idc A) f = f;
    unit_r : ∀ {A B} (f : Hom A B), comp f (idc B) = f;
    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D),
      comp f (comp g h) = comp (comp f g) h;
    Hom_set x y : isSet (Hom x y) }.

Arguments Ob : clear implicits.
Arguments Ob C%Cat : rename.
Arguments Hom [_%Cat].

Notation "g '◦' f" := (comp f g) (at level 40, left associativity).

Definition dom {C : category} {O1 O2 : Ob C} (f : Hom O1 O2) := O1.
Definition cod {C : category} {O1 O2 : Ob C} (f : Hom O1 O2) := O2.

(* The opposite (or “dual”) category C^op of a category C has the same
   objects as C, and an arrow f : C → D in C^op is an arrow f : D → C
   in C. That is C^op is just C with all of the arrows formally turned
   around. *)

Definition op C :=
  {| Ob := Ob C;
     Hom c d := Hom d c;
     comp _ _ _ f g := f ◦ g;
     idc := @idc C;
     unit_l _ _ f := unit_r f;
     unit_r _ _ f := unit_l f;
     assoc _ _ _ _ f g h := eq_sym (assoc h g f);
     Hom_set x y := Hom_set y x |}.

Notation "C ⁰" := (op C) (at level 8, left associativity, format "C ⁰").

(* initial & final *)

Definition is_initial {C : category} (c : Ob C) :=
  ∀ d, ∃ f : Hom c d, ∀ g : Hom c d, f = g.
Definition is_terminal {C : category} (c : Ob C) :=
  ∀ d, ∃ f : Hom d c, ∀ g : Hom d c, f = g.

(* functors *)

Class functor (C D : category) :=
  { f_map_obj : Ob C → Ob D;
    f_map_hom {a b} : Hom a b → Hom (f_map_obj a) (f_map_obj b);
    f_comp_prop {a b c} (f : Hom a b) (g : Hom b c) :
      f_map_hom (g ◦ f) = f_map_hom g ◦ f_map_hom f;
    f_id_prop {a} : @f_map_hom a _ (idc a) = idc (f_map_obj a) }.

Arguments functor C%Cat D%Cat.
Arguments f_map_obj [_] [_] _%Fun.
Arguments f_map_hom {_%Cat} {_%Cat} _ {_} {_}.

Definition fop {C D} : functor C D → functor C⁰ D⁰ :=
  λ F,
  {| f_map_obj (x : Ob C⁰) := (@f_map_obj C D F x : Ob D⁰);
     f_map_hom _ _ f := f_map_hom F f;
     f_comp_prop _ _ _ f g := @f_comp_prop _ _ F _ _ _ g f;
     f_id_prop a := @f_id_prop _ _ F a |}.

Definition is_isomorphism {C : category} {A B : Ob C} (f : Hom A B) :=
  { g : Hom B A & ((g ◦ f = idc A) * (f ◦ g = idc B))%type }.

Theorem functor_comp_id_prop {C D E} {F : functor C D} {G : functor D E} :
  ∀ x : Ob C,
   f_map_hom G (f_map_hom F (idc x)) = idc (f_map_obj G (f_map_obj F x)).
Proof.
intros.
etransitivity; [ | apply f_id_prop ].
apply f_equal, f_id_prop.
Defined.

Theorem functor_comp_prop {C D E} {F : functor C D} {G : functor D E} :
   ∀ (a b c : Ob C) (f : Hom a b) (g : Hom b c),
   f_map_hom G (f_map_hom F (g ◦ f)) =
   f_map_hom G (f_map_hom F g) ◦ f_map_hom G (f_map_hom F f).
Proof.
intros.
etransitivity; [ | apply f_comp_prop ].
apply f_equal, f_comp_prop.
Defined.

Definition functor_comp {C D E} : functor C D → functor D E → functor C E :=
  λ F G,
  {| f_map_obj x := f_map_obj G (f_map_obj F x);
     f_map_hom x y f := f_map_hom G (f_map_hom F f);
     f_comp_prop := functor_comp_prop;
     f_id_prop := functor_comp_id_prop |}.

Definition functor_id C : functor C C :=
  {| f_map_obj x := x;
     f_map_hom x y f := f;
     f_comp_prop _ _ _ _ _ := eq_refl;
     f_id_prop _ := eq_refl |}.

Notation "g '◦' f" := (functor_comp f g) (at level 40, left associativity) :
  functor_scope.
Notation "1 C" := (functor_id C) (at level 10) :
  functor_scope.

(* *)

Theorem eq_eq_eq_pair {A B} {x y : A} {z t : B} :
  ∀ (p : x = y) (q : z = t), (x, z) = (y, t).
Proof.
intros.
now destruct p, q.
Defined.

Definition transport2 {C D} {F : functor C D} {G : functor D C}
  (GF : ∀ x : Ob C, f_map_obj G (f_map_obj F x) = x) x y :=
  h4c.transport (λ '(x, y), Hom x y)
    (eq_eq_eq_pair (eq_sym (GF x)) (eq_sym (GF y))).

(* faithfulness & fullness *)

Definition is_faithful_functor {C D} (F : functor C D) :=
  ∀ (A B : Ob C) (f g : Hom A B), f_map_hom F f = f_map_hom F g → f = g.

Definition is_full_functor {C D} (F : functor C D) :=
  ∀ A B (g : Hom (f_map_obj F A) (f_map_obj F B)), ∃ f, f_map_hom F f = g.

Definition is_functor_injective_on_objects {C D} (F : functor C D) :=
  ∀ (A B : Ob C), f_map_obj F A = f_map_obj F B → A = B.

Definition is_functor_injective_on_arrows {C D} (F : functor C D) :=
  is_functor_injective_on_objects F ∧ is_faithful_functor F.

(* *)

Definition is_equiv_betw_cat {C D} (F : functor C D) :=
  { G : functor D C &
    functor_comp F G = functor_id C &
    functor_comp G F = functor_id D }.

Definition are_equivalent_categories (C D : category) :=
  { F : functor C D & is_equiv_betw_cat F }.

Arguments are_equivalent_categories C%Cat D%Cat.

(* natural transformation *)

Definition natural_transformation {C D} (F : functor C D) (G : functor C D) :=
  { ϑ : ∀ x, Hom (f_map_obj F x) (f_map_obj G x) &
    ∀ x y (f : Hom x y), ϑ y ◦ f_map_hom F f = f_map_hom G f ◦ ϑ x }.

Arguments natural_transformation {_} {_} F%Fun G%Fun.

Definition nt_component {C D} {F G : functor C D}
  (η : natural_transformation F G) := projT1 η.
Definition nt_commute {C D} {F G : functor C D}
  (η : natural_transformation F G) := projT2 η.

Definition nat_transf_id {C D} (F : functor C D) :
  natural_transformation F F.
exists (λ X, idc (f_map_obj F X)).
intros X Y f.
etransitivity.
apply unit_r.
symmetry; apply unit_l.
Defined.

Theorem nat_transf_comp_nt_commute {C D} {F G H : functor C D} :
  ∀ (η : natural_transformation F G) (η' : natural_transformation G H),
  ∀ (x y : Ob C) (f : Hom x y),
  nt_component η' y ◦ nt_component η y ◦ f_map_hom F f =
  f_map_hom H f ◦ (nt_component η' x ◦ nt_component η x).
Proof.
intros.
rewrite assoc, (nt_commute η).
do 2 rewrite <- assoc.
apply f_equal, (nt_commute η').
Defined.

Definition nat_transf_comp {C D} {F G H : functor C D} :
    natural_transformation F G → natural_transformation G H →
    natural_transformation F H :=
  λ η η',
  existT _ (λ x, nt_component η' x ◦ nt_component η x)
    (nat_transf_comp_nt_commute η η').

(* natural isomorphism *)

(*
  If, for every object X in C, the morphism ηX is an isomorphism in D,
  then η is said to be a natural isomorphism (or sometimes natural
  equivalence or isomorphism of functors). Two functors F and G are
  called naturally isomorphic or simply isomorphic if there exists a
  natural isomorphism from F to G.
*)

Definition is_natural_isomorphism {C D} {F G : functor C D}
  (η : natural_transformation F G) :=
  ∀ X, is_isomorphism (nt_component η X).

(* category of functors *)
(* noted [C, D] or D^C *)

Theorem Fun_unit_l {C D} (F G : functor C D) :
  ∀ (f : natural_transformation F G), nat_transf_comp (nat_transf_id F) f = f.
Proof.
intros.
destruct f as (f, Hf).
unfold nat_transf_comp; cbn.
apply eq_existT_uncurried.
assert (p : (λ x : Ob C, f x ◦ idc (f_map_obj F x)) = f). {
  apply fun_ext.
  intros c.
  apply unit_l.
}
exists p.
apply fun_ext; intros x.
apply fun_ext; intros y.
apply fun_ext; intros g.
apply Hom_set.
Qed.

Theorem Fun_unit_r {C D} (F G : functor C D) :
  ∀ (f : natural_transformation F G), nat_transf_comp f (nat_transf_id G) = f.
Proof.
intros.
destruct f as (f, Hf).
unfold nat_transf_comp; cbn.
apply eq_existT_uncurried.
assert (p : (λ x : Ob C, idc (f_map_obj G x) ◦ f x) = f). {
  apply fun_ext.
  intros c.
  apply unit_r.
}
exists p.
apply fun_ext; intros x.
apply fun_ext; intros y.
apply fun_ext; intros g.
apply Hom_set.
Qed.

Theorem Fun_assoc {C D} (F G H I : functor C D) :
  ∀ (η : natural_transformation F G) (η' : natural_transformation G H)
     (η'' : natural_transformation H I),
  nat_transf_comp η (nat_transf_comp η' η'') =
  nat_transf_comp (nat_transf_comp η η') η''.
Proof.
intros.
unfold nat_transf_comp; cbn.
apply eq_existT_uncurried.
assert
 (p :
    (λ x, nt_component η'' x ◦ nt_component η' x ◦ nt_component η x) =
    (λ x, nt_component η'' x ◦ (nt_component η' x ◦ nt_component η x))). {
  apply fun_ext; intros; apply assoc.
}
exists p.
apply fun_ext; intros x.
apply fun_ext; intros y.
apply fun_ext; intros z.
apply Hom_set.
Qed.

Theorem Fun_Hom_set {C D} : ∀ F G : functor C D,
  isSet (natural_transformation F G).
Proof.
intros.
intros a b c d.
apply h4c.is_set_is_set_sigT. {
  intros ϑ f g.
  apply fun_ext; intros x.
  apply fun_ext; intros y.
  apply fun_ext; intros h.
  apply Hom_set.
}
apply h4c.isSet_forall.
intros x.
apply Hom_set.
Qed.

Definition FunCat C D :=
  {| Ob := functor C D;
     Hom := natural_transformation;
     comp _ _ _ := nat_transf_comp;
     idc := nat_transf_id;
     unit_l := Fun_unit_l;
     unit_r := Fun_unit_r;
     assoc := Fun_assoc;
     Hom_set := Fun_Hom_set |}.

Notation "g '◦' f" := (nat_transf_comp f g) (at level 40, left associativity) :
  nat_transf_scope.

(* isomorphism between functors *)

Definition is_iso_betw_fun {C D} {F G : functor C D}
  (α : natural_transformation F G) :=
  { β : natural_transformation G F &
    nat_transf_comp α β = nat_transf_id F &
    nat_transf_comp β α = nat_transf_id G }.

Definition are_isomorphic_functors {C D} (F G : functor C D) :=
  { α : natural_transformation F G & is_iso_betw_fun α }.

(* according to Léonard, this definition below is equivalent to
   is_equiv_betw_cat_allioux, one direction being easy, but the
   other way around requires univalence *)

Definition is_equiv_betw_cat_guetta {C D} (F : functor C D) :=
  { G : functor D C &
    are_isomorphic_functors (functor_comp F G) (functor_id C) &
    are_isomorphic_functors (functor_comp G F) (functor_id D) }.

(* Guetta & Allioux pretend the following to be equivalent to
   is_equiv_betw_cat above, but testing the latter to CoConeCat
   and CoConeCat2 does not seem to work *)

Definition is_iso_betw_cat {C D} (F : functor C D) :=
  { G : functor D C &
    { GF : ∀ x : Ob C, f_map_obj G (f_map_obj F x) = x &
      { FG : ∀ y : Ob D, f_map_obj F (f_map_obj G y) = y &
        ((∀ (x y : Ob C) (f : Hom x y),
          f_map_hom G (f_map_hom F f) = transport2 GF x y f) *
         (∀ (x y : Ob D) (g : Hom x y),
          f_map_hom F (f_map_hom G g) = transport2 FG x y g))%type }}}.

Definition are_isomorphic_categories (C D : category) :=
  { F : functor C D & is_iso_betw_cat F }.

(* product of categories *)

Definition pair_unit_l {C1 C2} (X Y : Ob C1 * Ob C2)
     (f : Hom (fst X) (fst Y) * Hom (snd X) (snd Y)) :
  (fst f ◦ fst (idc (fst X), idc (snd X)),
   snd f ◦ snd (idc (fst X), idc (snd X))) = f.
Proof.
destruct f as (f1, f2); cbn.
now do 2 rewrite unit_l.
Qed.

Definition pair_unit_r {C1 C2} (X Y : Ob C1 * Ob C2)
     (f : Hom (fst X) (fst Y) * Hom (snd X) (snd Y)) :
  (fst (idc (fst Y), idc (snd Y)) ◦ fst f,
   snd (idc (fst Y), idc (snd Y)) ◦ snd f) = f.
Proof.
destruct f as (f1, f2); cbn.
now do 2 rewrite unit_r.
Qed.

Definition pair_assoc {C1 C2} (X Y Z T : Ob C1 * Ob C2)
  (f : Hom (fst X) (fst Y) * Hom (snd X) (snd Y))
  (g : Hom (fst Y) (fst Z) * Hom (snd Y) (snd Z))
  (h : Hom (fst Z) (fst T) * Hom (snd Z) (snd T)) :
  (fst (fst h ◦ fst g, snd h ◦ snd g) ◦ fst f,
   snd (fst h ◦ fst g, snd h ◦ snd g) ◦ snd f) =
  (fst h ◦ fst (fst g ◦ fst f, snd g ◦ snd f),
   snd h ◦ snd (fst g ◦ fst f, snd g ◦ snd f)).
Proof.
destruct f as (f1, f2).
destruct g as (g1, g2).
destruct h as (h1, h2); cbn.
now do 2 rewrite assoc.
Qed.

Definition pair_isSet {C1 C2} (X Y : Ob C1 * Ob C2) :
  isSet (Hom (fst X) (fst Y) * Hom (snd X) (snd Y)).
Proof.
apply h4c.isSet_pair; apply Hom_set.
Qed.

Definition cat_prod (C1 C2 : category) : category :=
  {| Ob := Ob C1 * Ob C2;
     Hom X Y := (Hom (fst X) (fst Y) * Hom (snd X) (snd Y))%type;
     comp _ _ _ f g := (fst g ◦ fst f, snd g ◦ snd f);
     idc X := (idc (fst X), idc (snd X));
     unit_l := pair_unit_l;
     unit_r := pair_unit_r;
     assoc := pair_assoc;
     Hom_set := pair_isSet |}.

Notation "C × D" := (cat_prod C D) (at level 40) : category_scope.

(* product of functors *)

Theorem functor_prod_comp_prop {C C' D D'}
    {F : functor C D} {F' : functor C' D'}
    (X Y Z : Ob (cat_prod C C')) (f : Hom X Y) (g : Hom Y Z) :
  (f_map_hom F (fst (g ◦ f)), f_map_hom F' (snd (g ◦ f))) =
  @comp (cat_prod D D')
        (f_map_obj F (fst X), f_map_obj F' (snd X))
        (f_map_obj F (fst Y), f_map_obj F' (snd Y))
        (f_map_obj F (fst Z), f_map_obj F' (snd Z))
     (f_map_hom F (fst f), f_map_hom F' (snd f))
     (f_map_hom F (fst g), f_map_hom F' (snd g)).
Proof.
now cbn; do 2 rewrite f_comp_prop.
Defined.

Theorem functor_prod_id_prop {C C' D D'}
    {F : functor C D} {F' : functor C' D'}
    (X : Ob (cat_prod C C')) :
  (f_map_hom F (fst (idc X)), f_map_hom F' (snd (idc X))) =
  @idc (cat_prod D D') (f_map_obj F (fst X), f_map_obj F' (snd X)).
Proof.
now cbn; do 2 rewrite f_id_prop.
Defined.

Definition functor_prod {C C' D D'} (F : functor C D) (F' : functor C' D') :
  functor (cat_prod C C') (cat_prod D D') :=
  {| f_map_obj (X : Ob (cat_prod C C')) :=
       (f_map_obj F (fst X), f_map_obj F' (snd X)) : Ob (cat_prod D D');
     f_map_hom _ _ f :=
       (f_map_hom F (fst f), f_map_hom F' (snd f));
     f_comp_prop :=
       functor_prod_comp_prop;
     f_id_prop :=
       functor_prod_id_prop |}.

Arguments functor_prod _ _ _ _ F%Fun F'%Fun.
Notation "C × D" := (functor_prod C D) (at level 40) : functor_scope.

(* category of sets *)

Definition Set_type := { A : Type & isSet A }.

Definition st_type (st : Set_type) := projT1 st.
Definition st_is_set (st : Set_type) := projT2 st.

Theorem Set_Hom_set : ∀ x y : Set_type, isSet (st_type x → st_type y).
Proof.
intros (A, HA) (B, HB).
move B before A; cbn.
apply h4c.isSet_forall.
now intros a.
Qed.

Definition SetCat :=
  {| Ob := Set_type;
     Hom A B := st_type A → st_type B;
     comp A B C f g x := g (f x);
     idc _ A := A;
     unit_l _ _ _ := eq_refl;
     unit_r _ _ _ := eq_refl;
     assoc _ _ _ _ _ _ _ := eq_refl;
     Hom_set := Set_Hom_set |}.

(* Hom functors covariant and contravariant *)

(*
  Hom(A,–) : C → Set
  This is a covariant functor given by:
    Hom(A,–) maps each object X in C to the set of morphisms, Hom(A, X)
    Hom(A,–) maps each morphism f : X → Y to the function
        Hom(A, f) : Hom(A, X) → Hom(A, Y) given by
        g ↦ f ∘ g for each g in Hom(A, X).
*)

Theorem cov_hom_functor_comp_prop {C} {A : Ob C} :
  ∀ (B B' B'' : Ob C) (f : Hom B B') (g : Hom B' B''),
  (λ h, g ◦ f ◦ h) =
  (@comp SetCat (existT isSet (Hom A B) (Hom_set A B))
         (existT isSet (Hom A B') (Hom_set A B'))
         (existT isSet (Hom A B'') (Hom_set A B''))
         (λ h, f ◦ h) (λ h, g ◦ h)).
Proof.
intros.
apply fun_ext; intros h.
apply assoc.
Qed.

Theorem cov_hom_functor_id_prop {C} {A : Ob C} :
  ∀ B : Ob C,
  (λ h, idc B ◦ h) = (@idc SetCat (existT isSet (Hom A B) (Hom_set A B))).
Proof.
intros.
apply fun_ext; intros h; cbn.
apply unit_r.
Qed.

Definition cov_hom_functor {C} (A : Ob C) : functor C SetCat :=
  {| f_map_obj (X : Ob C) := existT isSet (Hom A X) (Hom_set A X) : Ob SetCat;
     f_map_hom X Y (F : Hom X Y) (G : Hom A X) := F ◦ G;
     f_comp_prop := cov_hom_functor_comp_prop;
     f_id_prop := cov_hom_functor_id_prop |}.

(*
  Hom(-,B) : C → Set
  This is a contravariant functor given by:
    Hom(-,B) maps each object X in C to the set of morphisms, Hom(X, B)
    Hom(-,B) maps each morphism h : X → Y to the function
        Hom(h, B) : Hom(Y, B) → Hom(X, B) given by
        g ↦ g ∘ h for each g in Hom(Y, B).
*)

Definition con_hom_functor {C} (B : Ob C) : functor (op C) SetCat :=
  {| f_map_obj (X : Ob (op C)) :=
       existT isSet (@Hom C X B) (@Hom_set C X B) : Ob SetCat;
     f_map_hom (X Y : Ob C) (H : @Hom C Y X) (G : @Hom C X B) := G ◦ H;
     f_comp_prop := @cov_hom_functor_comp_prop (op C) B;
     f_id_prop := @cov_hom_functor_id_prop (op C) B |}.

Theorem con_hom_functor_is_cov_hom_functor_op {C} {A : Ob C} :
  con_hom_functor A = @cov_hom_functor (op C) A.
Proof. easy. Qed.

(* Hom functor: bifunctor of covariant and contravariant *)

Definition hom_functor_map_obj {C} (X : Ob (op C × C)) : Ob SetCat :=
  existT isSet (@Hom C (fst X) (snd X)) (@Hom_set C (fst X) (snd X)).

Definition hom_functor_map_hom {C} {X Y : Ob (op C × C)} (f : Hom X Y) :
  Hom (@hom_functor_map_obj C X) (@hom_functor_map_obj C Y) :=
  λ g,
  (@comp C (fst Y) (fst X) (snd Y) (fst f)
     (@comp C (fst X) (snd X) (snd Y) g (snd f))).

Theorem hom_functor_comp_prop {C} {X Y Z : Ob (op C × C)}
  (f : Hom X Y) (g : Hom Y Z) :
  hom_functor_map_hom (g ◦ f) = hom_functor_map_hom g ◦ hom_functor_map_hom f.
Proof.
unfold hom_functor_map_hom; cbn.
apply fun_ext; intros h.
now do 5 rewrite assoc.
Defined.

Theorem hom_functor_id_prop {C} (X : Ob (op C × C)) :
  hom_functor_map_hom (idc X) = idc (hom_functor_map_obj X).
Proof.
unfold hom_functor_map_hom; cbn.
apply fun_ext; intros f.
now rewrite unit_l, unit_r.
Defined.

Definition hom_functor C : functor (op C × C) SetCat :=
  {| f_map_obj := hom_functor_map_obj;
     f_map_hom _ _ := hom_functor_map_hom;
     f_comp_prop _ _ _ := hom_functor_comp_prop;
     f_id_prop := hom_functor_id_prop |}.

(*

(* representable functors *)

Definition is_representable_functor {C} (F : functor C SetCat) :=
  { X : Ob C & are_isomorphic_functors F (cov_hom_functor X) }.

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

(* equivalence between both definitions of adjunction *)

(*
Definition curry {A B C} (f : A * B → C) (X : A) (Y : B) := f (X, Y).

Definition functor_curry {A B C} (F : functor (A × B) C) :
  Ob A → functor B C.
Proof.
intros X.
apply
  {| f_map_obj (Y : Ob B) := f_map_obj F (X, Y) : Ob C;
     f_map_hom (Y Y' : Ob B) (f : Hom Y Y') :=
       @f_map_hom (A × B) _ _ (X, Y) (X, Y') (idc X, f) |}.
...
*)

Theorem adj_adj {C D} (R : functor C D) (L : functor D C) :
  (are_adjoint R L → are_adjoint2 R L) *
  (are_adjoint2 R L → are_adjoint R L).
Proof.
split.
-intros Ha.
 unfold are_adjoint, adjunction in Ha.
 unfold are_adjoint2, adjunction2.
 destruct Ha as (ϑ, Hiso).
(*
 assert (α : ∀ X, Hom (f_map_obj (1 C) X) (f_map_obj (L ◦ R) X)). {
   intros; cbn.
   now specialize (nt_component ϑ (X, f_map_obj R X) (idc _)) as f.
 }
*)
 set (α := λ X, nt_component ϑ (X, f_map_obj R X) (f_map_hom R (idc X))).
(*
 set (α := λ X, nt_component ϑ (X, f_map_obj R X) (idc (f_map_obj R X))).
*)
 cbn in α.
 assert (Hα : ∀ X Y (f : Hom X Y),
   α Y ◦ f_map_hom (1 C)%Fun f = f_map_hom (L ◦ R)%Fun f ◦ α X). {
   intros X Y f; cbn.
   unfold α; cbn.
   specialize (α X) as fX; cbn in fX.
   specialize (α Y) as fY; cbn in fY.
   do 2 rewrite f_id_prop.
Check (nt_component ϑ).
...
   destruct ϑ as (ϑ & Hϑ).
   cbn in ϑ, Hiso, α; cbn.
   specialize (Hϑ (Y, f_map_obj R Y) (X, f_map_obj R Y)) as H1.
   specialize (H1 (f, idc _)); cbn in H1.
   specialize (@h4c.happly _ _ _ _ H1) as H2; cbn in H2; clear H1.
   specialize (H2 (idc _)).
   unfold hom_functor_map_hom in H2; cbn in H2.
   rewrite <- f_id_prop in H2.
...
   specialize (α X) as fX; cbn in fX.
   specialize (α Y) as fY; cbn in fY.
   specialize (Hiso (X, f_map_obj R X)) as H1.
   destruct H1 as (g & Hg1 & Hg2).
   cbn in g, Hg1, Hg2.
   specialize (@h4c.happly _ _ _ _ Hg1) as H1; cbn in H1; clear Hg1.
   specialize (@h4c.happly _ _ _ _ Hg2) as H2; cbn in H2; clear Hg2.
   specialize (H2 fX).
...
 }
...
 exists (existT _ α Hα).
...
   specialize (Hiso (X, f_map_obj R Y)) as H1.
   destruct H1 as (g & Hg1 & Hg2).
   cbn in g, Hg1, Hg2.
   specialize (@h4c.happly _ _ _ _ Hg1) as H1; cbn in H1; clear Hg1.
   specialize (@h4c.happly _ _ _ _ Hg2) as H2; cbn in H2; clear Hg2.
...
   destruct ϑ as (ϑ, Hϑ); cbn in *.
   specialize (Hϑ (Y, f_map_obj R Y) (X, f_map_obj R Y)) as H1.
   unfold hom_functor_map_hom in H1; cbn in H1.
   specialize (H1 (f, idc _)).
   specialize (@h4c.happly _ _ _ _ H1) as H2; clear H1; cbn in H2.
   specialize (H2 (idc _)).
   rewrite <- f_id_prop in H2.
...
 }
 exists (existT _ α Hα).
...
  ηC : c → RLc
faire C^op→[C,Set] à la place C^op×C→Set
...
-intros Ha.
 unfold are_adjoint2, adjunction2 in Ha.
 unfold are_adjoint, adjunction.
 destruct Ha as (η & ε & Hr & Hl).
...

(* cone image by a functor *)

Definition cone_image_fam {J C D} {X : functor J C} {cn : cone X}
    (F : functor C D) (j : Ob J) :
    Hom (f_map_obj F (cn_top cn)) (f_map_obj (F ◦ X) j) :=
  f_map_hom F (cn_fam cn j).

Theorem cone_image_commute {J C D} {X : functor J C} (F : functor C D)
    {cn : cone X} (i j : Ob J) (f : Hom i j) :
  f_map_hom F (cn_fam cn j) =
  f_map_hom (F ◦ X)%Fun f ◦ f_map_hom F (cn_fam cn i).
Proof.
cbn.
rewrite (cn_commute cn i j f).
apply f_comp_prop.
Qed.

Definition cone_image {J C D} {X : functor J C} (F : functor C D) :
    cone X → cone (F ◦ X) :=
  λ cn,
  {| cn_top := f_map_obj F (cn_top cn);
     cn_fam := cone_image_fam F;
     cn_commute := cone_image_commute F |}.

(* hom-functor preserves limits *)
(* https://ncatlab.org/nlab/show/hom-functor+preserves+limits *)

(* failed to understand and prove id

(*
   let X• : ℐ⟶𝒞 be a diagram. Then:
   1. If the limit lim_←i Xi exists in 𝒞 then for all Y ∈ 𝒞
      there is a natural isomorphism
        Hom_𝒞(Y,lim_←i Xi) ≃ lim_←i (Hom_𝒞(Y,Xi)),
      where on the right we have the limit over the diagram of
      hom-sets given by
        Hom_𝒞(Y,−) ∘ X : ℐ −(X)→ 𝒞 −(Hom_𝒞(Y,−))→ Set.
*)

(* this "hom_functor Y (cn_top c)", a functor is supposed to be isomorphic
   to .... something *)
Check
  (λ J C (X_ : functor J C) (Y : Ob C) (c : cone X_) (p : is_limit c),
   hom_functor Y (cn_top c)).
(* → functor (op C × C) SetCat *)
(* ... to? *)
Check
  (λ J C (X_ : functor J C) (Y : Ob C),
   (cov_hom_functor Y ◦ X_)%Fun).
(* → functor J SetCat *)

(* functors not of the same type! *)

Check @is_natural_isomorphism.

Theorem hom_functor_preserves_limit {C} :
  ∀ J (X_ : functor J C) (lim_i_Xi : cone X_),
  is_limit lim_i_Xi →
  ∀ (Y : Ob C) lim_i_Hom_C_Y_Xi,
  @is_natural_isomorphism _ _
    (hom_functor Y (cn_top lim_i_Xi))
    (cov_hom_functor Y ◦ X_)%Fun.
...
  ∀ Y (cn' : cone (cov_hom_functor Y ◦ X_)), is_limit cn'.
Proof.
intros * Hlim *.
(* "First observe that, by the very definition of limiting cones,
    maps out of some Y into them are in natural bijection with
    the set Cones(Y,X•) of cones over the diagram X• with tip Y:
       Hom(Y,lim⟵i Xi)≃Cones(Y,X•).
   " *)
(* ah bon *)
...

Theorem hom_functor_preserves_limit {C} (A B : Ob C)
    (F := hom_functor A B) :
  ∀ J (X : functor J (op C × C)) (cn : cone X),
  is_limit cn → is_limit (cone_image F cn).
...

(* RAPL : Right Adjoint Preserves Limit *)
(* https://ncatlab.org/nlab/show/adjoints+preserve+%28co-%29limits *)

Theorem RAPL {C D} (L : functor C D) (R : functor D C) :
  L ⊣ R →
  ∀ J (X : functor J D) (cn : cone X),
  is_limit cn → is_limit (cone_image R cn).
Proof.
intros HLR * Hlim.
unfold is_limit, is_terminal in Hlim |-*.
cbn in Hlim |-*.
intros cn'; move cn' before cn.
specialize (Hlim cn) as H1.
destruct H1 as (cn1 & Hcn1).
destruct HLR as (η & ε & H1 & H2).
...
Check @hom_functor.
Print cone.

Theorem lim_hom_fun {J C D} (E : functor J C) (F : functor C D) (X : Ob C) (j : Ob J) (cn : cone E) :
  hom_functor X (cn_fam cn j).
...
*)

(* category of finite sets *)

Definition isInj {A B} (f : A → B) := ∀ x y : A, f x = f y → x = y.
Definition isFin T := { f : T → nat & isInj f }.

Definition FinSet_type := { S : Type & (isSet S * isFin S)%type }.

Definition fs_type (FS : FinSet_type) := projT1 FS.
Definition fs_is_set (FS : FinSet_type) := fst (projT2 FS).
Definition fs_finite (FS : FinSet_type) := snd (projT2 FS).

Definition FinSet_Hom_set (A B : FinSet_type) : isSet (fs_type A → fs_type B).
Proof.
apply h4c.isSet_forall.
intros a.
apply fs_is_set.
Qed.

Definition FinSetCat :=
  {| Ob := FinSet_type;
     Hom A B := fs_type A → fs_type B;
     comp A B C f g x := g (f x);
     idc _ A := A;
     unit_l _ _ _ := eq_refl;
     unit_r _ _ _ := eq_refl;
     assoc _ _ _ _ _ _ _ := eq_refl;
     Hom_set := FinSet_Hom_set |}.

(* category Pos of partially ordered sets (posets) *)

Record Pos_type :=
  { ps_type : Set_type;
    ps_le : st_type ps_type → st_type ps_type → Type;
(*
    These properties are not needed in Pos category:
    ps_refl : ∀ a : st_type ps_type, ps_le a a;
    ps_trans : ∀ a b c, ps_le a b → ps_le b c → ps_le a c;
    ps_antisym : ∀ a b, ps_le a b → ps_le b a → a = b;
*)
    ps_prop : ∀ a b, isProp (ps_le a b) }.

Arguments ps_le {_}.

Definition ps_stype A := st_type (ps_type A).

Definition is_monotone {A B} (f : ps_stype A → ps_stype B) :=
  ∀ a a' : ps_stype A, ps_le a a' → ps_le (f a) (f a').

Definition Pos_Hom A B := { f : ps_stype A → ps_stype B & is_monotone f }.

Definition Pos_comp {A B C} (f : Pos_Hom A B) (g : Pos_Hom B C) :
  Pos_Hom A C.
Proof.
exists (λ a, projT1 g (projT1 f a)).
intros a a' Hle.
now apply (projT2 g), (projT2 f).
Defined.

Definition Pos_id A : Pos_Hom A A.
Proof.
now exists (λ a, a).
Defined.

Theorem Pos_unit_l A B (f : Pos_Hom A B) : Pos_comp (Pos_id A) f = f.
Proof.
unfold Pos_comp, Pos_id; cbn.
destruct f as (f & Hf); cbn.
apply eq_existT_uncurried.
assert (p : (λ a, f a) = f). {
  apply fun_ext.
  now intros.
}
exists p; cbn.
apply fun_ext; intros a.
apply fun_ext; intros a'.
apply fun_ext; intros g.
apply ps_prop.
Qed.

Theorem Pos_unit_r A B (f : Pos_Hom A B) : Pos_comp f (Pos_id B) = f.
unfold Pos_comp, Pos_id; cbn.
destruct f as (f & Hf); cbn.
apply eq_existT_uncurried.
assert (p : (λ a, f a) = f). {
  apply fun_ext.
  now intros.
}
exists p; cbn.
apply fun_ext; intros a.
apply fun_ext; intros a'.
apply fun_ext; intros g.
apply ps_prop.
Qed.

Theorem Pos_assoc A B C D (f : Pos_Hom A B) (g : Pos_Hom B C)
  (h : Pos_Hom C D) :
  Pos_comp f (Pos_comp g h) = Pos_comp (Pos_comp f g) h.
Proof.
apply eq_existT_uncurried.
now exists eq_refl.
Defined.

Theorem Pos_Hom_set A B : isSet (Pos_Hom A B).
Proof.
apply h4c.is_set_is_set_sigT. {
  intros f.
  unfold is_monotone.
  intros g h.
  apply fun_ext; intros a.
  apply fun_ext; intros a'.
  apply fun_ext; intros p.
  apply ps_prop.
}
apply h4c.isSet_forall.
intros a.
unfold ps_stype; cbn.
apply st_is_set.
Defined.

Definition PosCat :=
  {| Ob := Pos_type;
     Hom := Pos_Hom;
     comp _ _ _ := Pos_comp;
     idc := Pos_id;
     unit_l := Pos_unit_l;
     unit_r := Pos_unit_r;
     assoc := Pos_assoc;
     Hom_set := Pos_Hom_set |}.

(* category Rel *)

(* http://angg.twu.net/tmp/2016-optativa/awodey__category_theory.pdf *)
(* The objects of Rel are sets, and an arrow f : A → B is a relation from A
   to B, that is, f ⊆ A × B. The identity relation {<a,a> ∈ A × A| a ∈ A}
   is the identity arrow on a set A. Composition in Rel is to be given by
      g ◦ f = {<a,c> ∈ A × C | ∃b (<a,b> ∈ f & <b,c> ∈ g)}
   for f ⊆ A × B and g ⊆ B × C.
*)

Definition Rel_Hom A B := st_type A → st_type B → Prop.

Definition Rel_comp {A B C} (f : Rel_Hom A B) (g : Rel_Hom B C) :
  Rel_Hom A C.
Proof.
intros a c.
apply (∃ b, f a b ∧ g b c).
Defined.

Definition Rel_id (A : Set_type) : Rel_Hom A A.
Proof.
intros a1 a2.
apply (a1 = a2).
Defined.

Theorem Rel_unit_l A B (f : Rel_Hom A B) : Rel_comp (Rel_id A) f = f.
Proof.
apply fun_ext; intros a.
apply fun_ext; intros b.
apply prop_ext.
unfold Rel_comp, Rel_id; cbn.
split; intros H.
-destruct H as (a' & Ha & Hf).
 now subst a'.
-now exists a.
Defined.

Theorem Rel_unit_r A B (f : Rel_Hom A B) : Rel_comp f (Rel_id B) = f.
Proof.
apply fun_ext; intros a.
apply fun_ext; intros b.
apply prop_ext.
unfold Rel_comp, Rel_id; cbn.
split; intros H.
-destruct H as (b' & Hb & Hf).
 now subst b'.
-now exists b.
Defined.

Theorem Rel_assoc {A B C D} (f : Rel_Hom A B) (g : Rel_Hom B C)
  (h : Rel_Hom C D) :
  Rel_comp f (Rel_comp g h) = Rel_comp (Rel_comp f g) h.
Proof.
apply fun_ext; intros a.
apply fun_ext; intros b.
apply prop_ext.
unfold Rel_comp.
split.
-intros (b' & Hb & c & Hg & Hh).
 exists c.
 split; [ | easy ].
 now exists b'.
-intros (c & (b' & Hf & Hg) & Hh).
 exists b'.
 split; [ easy | ].
 now exists c.
Defined.

Theorem Rel_Hom_set A B : isSet (Rel_Hom A B).
Proof.
unfold Rel_Hom.
apply h4c.isSet_forall; intros a.
apply h4c.isSet_forall; intros b.
apply proof_irrel.
Defined.

Definition RelCat :=
  {| Ob := Set_type;
     Hom := Rel_Hom;
     comp _ _ _ := Rel_comp;
     idc := Rel_id;
     unit_l := Rel_unit_l;
     unit_r := Rel_unit_r;
     assoc _ _ _ _ := Rel_assoc;
     Hom_set := Rel_Hom_set |}.

(* *)

Print adjunction2.
Print natural_transformation.
*)
