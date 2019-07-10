(* categories *)
(* http://angg.twu.net/tmp/2016-optativa/awodey__category_theory.pdf *)

Set Universe Polymorphism.
Require Import Utf8.
Require hott4cat.
Set Nested Proofs Allowed.

Axiom extensionality : ∀ A B (f g : ∀ x : A, B x), (∀ x, f x = g x) → f = g.

Definition isSet (A : Type) := ∀ (a b : A) (p q : a = b), p = q.

Class category :=
  { Obj : Type;
    Hom : Obj → Obj → Type;
    comp : ∀ {A B C}, Hom A B → Hom B C → Hom A C;
    idc : ∀ A, Hom A A;
    unit_l : ∀ {A B} (f : Hom A B), comp (idc A) f = f;
    unit_r : ∀ {A B} (f : Hom A B), comp f (idc B) = f;
    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D),
      comp f (comp g h) = comp (comp f g) h;
    Hom_set x y : isSet (Hom x y) }.

Arguments Obj : clear implicits.
Arguments Hom [_].
Notation "g '◦' f" := (comp f g) (at level 40, left associativity).

Definition dom {C : category} {O1 O2 : Obj C} (f : Hom O1 O2) := O1.
Definition cod {C : category} {O1 O2 : Obj C} (f : Hom O1 O2) := O2.

(* The opposite (or “dual”) category C^op of a category C has the same
   objects as C, and an arrow f : C → D in C^op is an arrow f : D → C
   in C. That is C^op is just C with all of the arrows formally turned
   around. *)

Definition op C :=
  {| Obj := Obj C;
     Hom c d := Hom d c;
     comp _ _ _ f g := f ◦ g;
     idc := @idc C;
     unit_l _ _ f := unit_r f;
     unit_r _ _ f := unit_l f;
     assoc _ _ _ _ f g h := eq_sym (assoc h g f);
     Hom_set x y := Hom_set y x |}.

Definition is_initial {C : category} (c : Obj C) :=
  ∀ d, ∃ f : Hom c d, ∀ g : Hom c d, f = g.
Definition is_terminal {C : category} (c : Obj C) :=
  ∀ d, ∃ f : Hom d c, ∀ g : Hom d c, f = g.

Class functor (C D : category) :=
  { f_map_obj : Obj C → Obj D;
    f_map_hom {a b} : Hom a b → Hom (f_map_obj a) (f_map_obj b);
    f_comp_prop {a b c} (f : Hom a b) (g : Hom b c) :
      f_map_hom (g ◦ f) = f_map_hom g ◦ f_map_hom f;
    f_id_prop {a} : @f_map_hom a _ (idc a) = idc (f_map_obj a) }.

Arguments f_map_obj [_] [_] _.
Arguments f_map_hom [_] [_] _ [_] [_].

Definition fop {C D} : functor C D → functor (op C) (op D) :=
  λ F,
  {| f_map_obj (x : Obj (op C)) := (@f_map_obj C D F x : Obj (op D));
     f_map_hom _ _ f := f_map_hom F f;
     f_comp_prop _ _ _ f g := @f_comp_prop _ _ F _ _ _ g f;
     f_id_prop a := @f_id_prop _ _ F a |}.

Definition is_isomorphism {C : category} {A B : Obj C} (f : Hom A B) :=
  ∃ g : Hom B A, g ◦ f = idc A ∧ f ◦ g = idc B.

Theorem functor_comp_id_prop {C D E} {F : functor C D} {G : functor D E} :
  ∀ x : Obj C,
   f_map_hom G (f_map_hom F (idc x)) = idc (f_map_obj G (f_map_obj F x)).
Proof.
intros.
etransitivity; [ | apply f_id_prop ].
apply f_equal, f_id_prop.
Defined.

Theorem functor_comp_prop {C D E} {F : functor C D} {G : functor D E} :
   ∀ (a b c : Obj C) (f : Hom a b) (g : Hom b c),
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

Definition is_equiv_betw_cat {C D} (F : functor C D) :=
  { G : functor D C &
    functor_comp F G = functor_id C &
    functor_comp G F = functor_id D }.

Definition are_equivalent_categories (C D : category) :=
  { F : functor C D & is_equiv_betw_cat F }.

(* A cone to a functor D(J,C) consists of an object c in C and a
   family of arrows in C : cj : c → Dj one for each object j ∈ J, such
   that for each arrow α : i → j in J, the following triangle
   commutes. *)

Record cone {J C} (D : functor J C) :=
  { cn_top : Obj C;
    cn_fam : ∀ j, Hom cn_top (f_map_obj D j);
    cn_commute : ∀ i j (α : Hom i j), cn_fam j = f_map_hom D α ◦ cn_fam i }.

Record co_cone {J C} (D : functor J C) :=
  { cc_top : Obj C;
    cc_fam : ∀ j, Hom (f_map_obj D j) cc_top;
    cc_commute : ∀ i j (α : Hom i j), cc_fam i = cc_fam j ◦ f_map_hom D α }.

Arguments cn_top [_] [_] [_].
Arguments cn_fam [_] [_] [_].
Arguments cc_top [_] [_] [_].
Arguments cc_fam [_] [_] [_].

(* category of cones & co-cones *)

Definition Cone_Hom {J C} {D : functor J C} (cn cn' : cone D) :=
  { ϑ : Hom (cn_top cn) (cn_top cn') & ∀ j, cn_fam cn j = cn_fam cn' j ◦ ϑ }.

Definition CoCone_Hom {J C} {D : functor J C} (cc cc' : co_cone D) :=
  { ϑ : Hom (cc_top cc) (cc_top cc') & ∀ j, cc_fam cc' j = ϑ ◦ cc_fam cc j }.

Definition cnh_hom {J C} {D : functor J C} {cn cn'}
  (cnh : Cone_Hom cn cn') := projT1 cnh.
Definition cnh_commute {J C} {D : functor J C} {cn cn'}
  (cnh : Cone_Hom cn cn') := projT2 cnh.
Definition cch_hom {J C} {D : functor J C} {cc cc'}
  (cch : CoCone_Hom cc cc') := projT1 cch.
Definition cch_commute {J C} {D : functor J C} {cc cc'}
  (cch : CoCone_Hom cc cc') := projT2 cch.

Definition Cone_comp {J C} {D : functor J C} (c c' c'' : cone D)
  (f : Cone_Hom c c') (g : Cone_Hom c' c'') : Cone_Hom c c''.
Proof.
exists (cnh_hom g ◦ cnh_hom f).
intros j.
etransitivity.
-apply (cnh_commute f j).
-etransitivity; [ | apply assoc ].
 f_equal.
 apply (cnh_commute g j).
Defined.

Definition CoCone_comp {J C} {D : functor J C} (c c' c'' : co_cone D)
  (f : CoCone_Hom c c') (g : CoCone_Hom c' c'') : CoCone_Hom c c''.
Proof.
exists (cch_hom g ◦ cch_hom f).
intros j.
etransitivity.
-apply (cch_commute g j).
-etransitivity; [ | symmetry; apply assoc ].
 f_equal.
 apply (cch_commute f j).
Defined.

Definition Cone_id {J C} {D : functor J C} (c : cone D) : Cone_Hom c c :=
   existT (λ ϑ, ∀ j, cn_fam c j = cn_fam c j ◦ ϑ) (idc (cn_top c))
     (λ j, eq_sym (unit_l (cn_fam c j))).

Definition CoCone_id {J C} {D : functor J C} (c : co_cone D) : CoCone_Hom c c :=
   existT (λ ϑ, ∀ j, cc_fam c j = ϑ ◦ cc_fam c j) (idc (cc_top c))
     (λ j, eq_sym (unit_r (cc_fam c j))).

Theorem Cone_unit_l {J C} {D : functor J C} :
  ∀ (c c' : cone D) (f : Cone_Hom c c'),
  Cone_comp c c c' (Cone_id c) f = f.
Proof.
intros.
unfold Cone_comp; cbn.
destruct f as (f & Hf); cbn.
apply eq_existT_uncurried.
exists (unit_l _).
apply extensionality.
intros j.
apply Hom_set.
Defined.

Theorem CoCone_unit_l {J C} {D : functor J C} :
  ∀ (c c' : co_cone D) (f : CoCone_Hom c c'),
  CoCone_comp c c c' (CoCone_id c) f = f.
Proof.
intros.
unfold CoCone_comp; cbn.
destruct f as (f & Hf); cbn.
apply eq_existT_uncurried.
exists (unit_l _).
apply extensionality.
intros j.
apply Hom_set.
Defined.

Theorem Cone_unit_r {J C} {D : functor J C} :
  ∀ (c c' : cone D) (f : Cone_Hom c c'),
  Cone_comp c c' c' f (Cone_id c') = f.
Proof.
intros.
unfold Cone_comp; cbn.
destruct f as (f & Hf); cbn.
apply eq_existT_uncurried.
exists (unit_r _).
apply extensionality.
intros j.
apply Hom_set.
Defined.

Theorem CoCone_unit_r {J C} {D : functor J C} :
  ∀ (c c' : co_cone D) (f : CoCone_Hom c c'),
  CoCone_comp c c' c' f (CoCone_id c') = f.
Proof.
intros.
destruct f as (f & Hf); cbn.
apply eq_existT_uncurried.
exists (unit_r _).
apply extensionality.
intros j.
apply Hom_set.
Defined.

Theorem Cone_assoc {J C} {D : functor J C} :
  ∀ (c c' c'' c''' : cone D) (f : Cone_Hom c c') (g : Cone_Hom c' c'')
    (h : Cone_Hom c'' c'''),
    Cone_comp c c' c''' f (Cone_comp c' c'' c''' g h) =
    Cone_comp c c'' c''' (Cone_comp c c' c'' f g) h.
Proof.
intros.
unfold Cone_comp; cbn.
apply eq_existT_uncurried.
exists (assoc _ _ _).
apply extensionality.
intros j.
apply Hom_set.
Defined.

Theorem CoCone_assoc {J C} {D : functor J C} :
  ∀ (c c' c'' c''' : co_cone D) (f : CoCone_Hom c c') (g : CoCone_Hom c' c'')
    (h : CoCone_Hom c'' c'''),
    CoCone_comp c c' c''' f (CoCone_comp c' c'' c''' g h) =
    CoCone_comp c c'' c''' (CoCone_comp c c' c'' f g) h.
Proof.
intros.
apply eq_existT_uncurried.
exists (assoc _ _ _).
apply extensionality.
intros j.
apply Hom_set.
Defined.

Theorem Cone_Hom_set {J C} {D : functor J C} :
  ∀ c c' : cone D, isSet (Cone_Hom c c').
Proof.
intros.
unfold Cone_Hom.
apply hott4cat.is_set_is_set_sigT; [ | apply Hom_set ].
intros f.
intros p q.
apply extensionality.
intros x.
apply Hom_set.
Qed.

Theorem CoCone_Hom_set {J C} {D : functor J C} :
  ∀ c c' : co_cone D, isSet (CoCone_Hom c c').
Proof.
intros.
unfold CoCone_Hom.
apply hott4cat.is_set_is_set_sigT; [ | apply Hom_set ].
intros f.
intros p q.
apply extensionality.
intros x.
apply Hom_set.
Qed.

Definition ConeCat {J C} (D : functor J C) :=
  {| Obj := cone D;
     Hom := Cone_Hom;
     comp := Cone_comp;
     idc := Cone_id;
     unit_l := Cone_unit_l;
     unit_r := Cone_unit_r;
     assoc := Cone_assoc;
     Hom_set := Cone_Hom_set |}.

Definition CoConeCat {J C} (D : functor J C) :=
  {| Obj := co_cone D;
     Hom := CoCone_Hom;
     comp := CoCone_comp;
     idc := CoCone_id;
     unit_l := CoCone_unit_l;
     unit_r := CoCone_unit_r;
     assoc := CoCone_assoc;
     Hom_set := CoCone_Hom_set |}.

(* A limit for a functor D : J → C is a terminal object in Cone(D)
   and a colimit an initial object in CoCone(D) *)

Definition is_limit {J C} {D : functor J C} (cn : cone D) :=
  @is_terminal (ConeCat D) cn.

Definition is_colimit {J C} {D : functor J C} (cc : co_cone D) :=
  @is_initial (CoConeCat D) cc.

(* Spelling out the definition, the limit of a diagram D has the
   following UMP: given any cone (C, cj) to D, there is a unique
   arrow u : C → lim←−j Dj such that for all j,
     pj ◦ u = cj .
*)

Theorem limit_UMP {J C} {D : functor J C} :
  ∀ l : cone D, is_limit l →
  ∀ c : cone D, exists! u, ∀ j, cn_fam l j ◦ u = cn_fam c j.
Proof.
intros * Hlim c.
unfold unique.
unfold is_limit in Hlim.
unfold is_terminal in Hlim.
specialize (Hlim c) as H1.
destruct H1 as (f, H1).
exists (cnh_hom f).
split. {
  intros j.
  destruct f as (f, Hf).
  now symmetry.
}
intros h Hh.
assert (Hh' : ∀ j : Obj J, cn_fam c j = cn_fam l j ◦ h). {
  intros j; specialize (Hh j).
  now symmetry.
}
remember
  (existT
     (λ ϑ : Hom (cn_top c) (cn_top l),
      ∀ j : Obj J, cn_fam c j = cn_fam l j ◦ ϑ) h Hh') as hh.
now rewrite (H1 hh); subst hh.
Qed.

(* another definition of category of co-cones *)

Definition CoConeCat2 {J C} (D : functor J C) := op (ConeCat (fop D)).

Definition cone_fop_of_co_cone {J C} {D : functor J C} :
    co_cone D → cone (fop D) :=
  λ cc,
  {| cn_top := cc_top cc : Obj (op C);
     cn_fam j := cc_fam cc j : @Hom (op C) (cc_top cc) (f_map_obj (fop D) j);
     cn_commute i j := cc_commute D cc j i |}.

Definition co_cone_of_cone_fop {J C} {D : functor J C} :
    cone (fop D) → co_cone D :=
  λ cn,
  {| cc_top := cn_top cn : Obj C;
     cc_fam j := cn_fam cn j : @Hom (op C) (cn_top cn) (f_map_obj D j);
     cc_commute i j := cn_commute (fop D) cn j i |}.

Definition F_CoConeCat_CoConeCat2_comp_prop {J C} {D : functor J C}
  {x y z : Obj (CoConeCat D)} :
  ∀ (f : Hom x y) (g : Hom y z),
   g ◦ f =
   @comp (CoConeCat2 D) (cone_fop_of_co_cone x) (cone_fop_of_co_cone y)
       (cone_fop_of_co_cone z) f g.
Proof.
intros; cbn.
apply eq_existT_uncurried; cbn.
exists eq_refl; cbn.
apply extensionality.
intros j.
apply Hom_set.
Defined.

Definition F_CoConeCat2_CoConeCat_comp_prop {J C} {D : functor J C}
  {x y z : Obj (CoConeCat2 D)} :
  ∀ (f : Hom x y) (g : Hom y z),
  g ◦ f =
  @comp (CoConeCat D) (co_cone_of_cone_fop x) (co_cone_of_cone_fop y)
        (co_cone_of_cone_fop z) f g.
Proof.
intros; cbn.
apply eq_existT_uncurried; cbn.
exists eq_refl; cbn.
apply extensionality.
intros j.
apply Hom_set.
Defined.

Definition F_CoConeCat_CoConeCat2 {J C} {D : functor J C} :
    functor (CoConeCat D) (CoConeCat2 D) :=
  {| f_map_obj :=
       cone_fop_of_co_cone : Obj (CoConeCat D) → Obj (CoConeCat2 D);
     f_map_hom _ _ f := f;
     f_comp_prop _ _ _ := F_CoConeCat_CoConeCat2_comp_prop;
     f_id_prop _ := eq_refl |}.

Definition F_CoConeCat2_CoConeCat {J C} {D : functor J C} :
    functor (CoConeCat2 D) (CoConeCat D) :=
  {| f_map_obj :=
       co_cone_of_cone_fop : Obj (CoConeCat2 D) → Obj (CoConeCat D);
     f_map_hom _ _ f := f;
     f_comp_prop _ _ _ := F_CoConeCat2_CoConeCat_comp_prop;
     f_id_prop _ := eq_refl |}.

Theorem F_CoConeCat_CoConeCat2_id {J C} {D : functor J C} :
  ∀ cc,
  f_map_obj F_CoConeCat2_CoConeCat (f_map_obj F_CoConeCat_CoConeCat2 cc) = cc.
Proof. now intros; destruct cc. Defined.

Theorem F_CoConeCat2_CoConeCat_id {J C} {D : functor J C} :
  ∀ cc,
  f_map_obj F_CoConeCat_CoConeCat2 (f_map_obj F_CoConeCat2_CoConeCat cc) = cc.
Proof. now intros; destruct cc. Defined.

Theorem eq_eq_eq_pair {A B} {x y : A} {z t : B} :
  ∀ (p : x = y) (q : z = t), (x, z) = (y, t).
Proof.
intros.
now destruct p, q.
Defined.

Definition transport2 {C D} {F : functor C D} {G : functor D C}
  (GF : ∀ x : Obj C, f_map_obj G (f_map_obj F x) = x) x y :=
  hott4cat.transport (λ '(x, y), Hom x y)
    (eq_eq_eq_pair (eq_sym (GF x)) (eq_sym (GF y))).

(* Guetta & Allioux pretend the following to be equivalent to
   is_equiv_betw_cat above, but testing the latter to CoConeCat
   and CoConeCat2 does not seem to work *)

Definition is_iso_betw_cat {C D} (F : functor C D) :=
  { G : functor D C &
    { GF : ∀ x : Obj C, f_map_obj G (f_map_obj F x) = x &
      { FG : ∀ y : Obj D, f_map_obj F (f_map_obj G y) = y &
        ((∀ (x y : Obj C) (f : Hom x y),
          f_map_hom G (f_map_hom F f) = transport2 GF x y f) *
         (∀ (x y : Obj D) (g : Hom x y),
          f_map_hom F (f_map_hom G g) = transport2 FG x y g))%type }}}.

Definition are_isomorphic_categories (C D : category) :=
  { F : functor C D & is_iso_betw_cat F }.

Theorem CoConeCat_CoConeCat2_iso J C {D : functor J C} :
  are_isomorphic_categories (CoConeCat D) (CoConeCat2 D).
Proof.
exists F_CoConeCat_CoConeCat2.
exists F_CoConeCat2_CoConeCat.
exists F_CoConeCat_CoConeCat2_id.
exists F_CoConeCat2_CoConeCat_id.
split.
-now intros; destruct x, y.
-now intros; destruct x, y.
Qed.

(* natural transformation *)

Definition natural_transformation {C D} (F : functor C D) (G : functor C D) :=
  { ϑ : ∀ x, Hom (f_map_obj F x) (f_map_obj G x) &
    ∀ x y (f : Hom x y), ϑ y ◦ f_map_hom F f = f_map_hom G f ◦ ϑ x }.

Definition nt_hom {C D} {F G : functor C D}
  (η : natural_transformation F G) := projT1 η.
Definition nt_commute {C D} {F G : functor C D}
  (η : natural_transformation F G) := projT2 η.

(* category of functors *)

Theorem FunCat_comp_nt_commute {C D} {F G H : functor C D} :
  ∀ (η : natural_transformation F G) (η' : natural_transformation G H),
  ∀ (x y : Obj C) (f : Hom x y),
  nt_hom η' y ◦ nt_hom η y ◦ f_map_hom F f =
  f_map_hom H f ◦ (nt_hom η' x ◦ nt_hom η x).
Proof.
intros.
rewrite assoc, (nt_commute η).
do 2 rewrite <- assoc.
apply f_equal, (nt_commute η').
Defined.

Definition FunCat_comp {C D} (F G H : functor C D) :
    natural_transformation F G → natural_transformation G H →
    natural_transformation F H :=
  λ η η',
  existT _ (λ x, nt_hom η' x ◦ nt_hom η x) (FunCat_comp_nt_commute η η').

Definition FunCat_id {C D} (F : functor C D) : natural_transformation F F.
Proof.
unfold natural_transformation.
exists (λ z, f_map_hom F (idc z)).
intros x y f.
etransitivity; [ apply f_equal, f_id_prop | ].
etransitivity; [ apply unit_r | ].
symmetry.
etransitivity; [ | apply unit_l ].
now destruct (@f_id_prop C D F x).
Defined.

Theorem FunCat_unit_l {C D} (F G : functor C D) :
  ∀ (f : natural_transformation F G), FunCat_comp F F G (FunCat_id F) f = f.
Proof.
intros.
destruct f as (f, Hf).
unfold FunCat_comp; cbn.
apply eq_existT_uncurried.
assert (p : (λ x : Obj C, f x ◦ f_map_hom F (idc x)) = f). {
  apply extensionality.
  intros c.
  rewrite f_id_prop.
  apply unit_l.
}
exists p.
apply extensionality; intros x.
apply extensionality; intros y.
apply extensionality; intros g.
apply Hom_set.
Qed.

Theorem FunCat_unit_r {C D} (F G : functor C D) :
  ∀ (f : natural_transformation F G), FunCat_comp F G G f (FunCat_id G) = f.
Proof.
intros.
destruct f as (f, Hf).
unfold FunCat_comp; cbn.
apply eq_existT_uncurried.
assert (p : (λ x : Obj C, f_map_hom G (idc x) ◦ f x) = f). {
  apply extensionality.
  intros c.
  rewrite f_id_prop.
  apply unit_r.
}
exists p.
apply extensionality; intros x.
apply extensionality; intros y.
apply extensionality; intros g.
apply Hom_set.
Qed.

Theorem FunCat_assoc {C D} (F G H I : functor C D) :
  ∀ (η : natural_transformation F G) (η' : natural_transformation G H)
     (η'' : natural_transformation H I),
  FunCat_comp F G I η (FunCat_comp G H I η' η'') =
  FunCat_comp F H I (FunCat_comp F G H η η') η''.
Proof.
intros.
unfold FunCat_comp; cbn.
apply eq_existT_uncurried.
assert
 (p :
    (λ x : Obj C, nt_hom η'' x ◦ nt_hom η' x ◦ nt_hom η x) =
    (λ x : Obj C, nt_hom η'' x ◦ (nt_hom η' x ◦ nt_hom η x))). {
  apply extensionality; intros; apply assoc.
}
exists p.
apply extensionality; intros x.
apply extensionality; intros y.
apply extensionality; intros z.
apply Hom_set.
Qed.

Theorem FunCat_Hom_set {C D} : ∀ F G : functor C D,
  isSet (natural_transformation F G).
Proof.
intros.
intros a b c d.
apply hott4cat.is_set_is_set_sigT. {
  intros ϑ f g.
  apply extensionality; intros x.
  apply extensionality; intros y.
  apply extensionality; intros h.
  apply Hom_set.
}
apply hott4cat.ex_3_1_6.
intros x.
apply Hom_set.
Qed.

Definition FunCat C D :=
  {| Obj := functor C D;
     Hom := natural_transformation;
     comp := FunCat_comp;
     idc := FunCat_id;
     unit_l := FunCat_unit_l;
     unit_r := FunCat_unit_r;
     assoc := FunCat_assoc;
     Hom_set := FunCat_Hom_set |}.

(* category of categories *)

Theorem CatCat_comp_prop {C C' C'' : category}
  {F : functor C C'} {G : functor C' C''} :
  ∀ (X Y Z : Obj C) (f : Hom X Y) (g : Hom Y Z),
  f_map_hom G (f_map_hom F (g ◦ f)) =
  f_map_hom G (f_map_hom F g) ◦ f_map_hom G (f_map_hom F f).
Proof.
intros.
etransitivity; [ | apply f_comp_prop ].
apply f_equal, f_comp_prop.
Defined.

Theorem CatCat_id_prop {C C' C'' : category}
  {F : functor C C'} {G : functor C' C''} :
  ∀ X : Obj C,
  f_map_hom G (f_map_hom F (idc X)) = idc (f_map_obj G (f_map_obj F X)).
Proof.
intros.
etransitivity; [ | apply f_id_prop ].
apply f_equal, f_id_prop.
Defined.

Definition CatCat_comp (C C' C'' : category)
  (F : functor C C') (G : functor C' C'') : functor C C'' :=
  {| f_map_obj X := f_map_obj G (f_map_obj F X);
     f_map_hom X Y f := f_map_hom G (f_map_hom F f);
     f_comp_prop := CatCat_comp_prop;
     f_id_prop := CatCat_id_prop |}.

Definition CatCat_idc (C : category) : functor C C :=
  {| f_map_obj X := X;
     f_map_hom _ _ f := f;
     f_comp_prop _ _ _ _ _ := eq_refl;
     f_id_prop _ := eq_refl |}.

Theorem CatCat_unit_l (C C' : category) (F : functor C C') :
  CatCat_comp C C C' (CatCat_idc C) F = F.
Proof.
unfold CatCat_comp, CatCat_idc; cbn.
destruct F; cbn in *.
f_equal.
-apply extensionality; intros X.
 apply extensionality; intros Y.
 apply extensionality; intros Z.
 apply extensionality; intros f.
 apply extensionality; intros g.
 apply Hom_set.
-apply extensionality; intros X.
 apply Hom_set.
Qed.

Theorem CatCat_unit_r (C C' : category) (F : functor C C') :
  CatCat_comp C C' C' F (CatCat_idc C') = F.
Proof.
unfold CatCat_comp, CatCat_idc; cbn.
destruct F; cbn in *.
f_equal.
-apply extensionality; intros X.
 apply extensionality; intros Y.
 apply extensionality; intros Z.
 apply extensionality; intros f.
 apply extensionality; intros g.
 apply Hom_set.
-apply extensionality; intros X.
 apply Hom_set.
Qed.

Theorem CatCat_assoc C C' C'' C'''
  (F : functor C C') (G : functor C' C'') (H : functor C'' C''') :
  CatCat_comp C C' C''' F (CatCat_comp C' C'' C''' G H) =
  CatCat_comp C C'' C''' (CatCat_comp C C' C'' F G) H.
Proof.
unfold CatCat_comp; cbn.
f_equal.
-unfold CatCat_comp_prop; cbn.
 apply extensionality; intros X.
 apply extensionality; intros Y.
 apply extensionality; intros Z.
 apply extensionality; intros f.
 apply extensionality; intros g; cbn.
 unfold eq_trans, f_equal.
 destruct
   (f_comp_prop (f_map_hom G (f_map_hom F f)) (f_map_hom G (f_map_hom F g))).
 destruct (f_comp_prop (f_map_hom F f) (f_map_hom F g)).
 now destruct (f_comp_prop f g).
-unfold CatCat_id_prop.
 apply extensionality; intros X.
 unfold eq_trans, f_equal; cbn.
 destruct f_id_prop; cbn.
 destruct f_id_prop; cbn.
 now destruct f_id_prop; cbn.
Qed.

(*
Theorem CatCat_Hom_set C C' (F G : functor C C') (p q : F = G) : p = q.
Proof.
destruct F, G; cbn in *.
Set Keep Proof Equalities.
injection p; intros H1 H2 H3 H4.
destruct H4.
apply hott4cat.eq_existT_pair_transport in H3.
destruct H3 as (Hp3 & H3).
destruct H3.
apply hott4cat.eq_existT_pair_transport in H2.
destruct H2 as (Hp2 & H2).
destruct H2.
apply hott4cat.eq_existT_pair_transport in H1.
destruct H1 as (Hp1 & H1).
destruct H1.
move Hp1 after Hp3; move Hp2 after Hp3.
injection p; intros H1 H2 H3.
injection H3.
intros H4.
apply hott4cat.eq_existT_pair_transport in H4.
destruct H4 as (Hp4 & H4).
move Hp4 before Hp3.
(* doesn't work; but is it true? *)
...

Hom_set does not work: perhaps false or not

Definition CatCat :=
  {| Obj := category;
     Hom := functor;
     comp := CatCat_comp;
     idc := CatCat_idc;
     unit_l := CatCat_unit_l;
     unit_r := CatCat_unit_r;
     assoc := CatCat_assoc;
     Hom_set := 42 |}.
*)

(* isomorphism between functors *)

Definition is_iso_betw_fun {C D} {F G : functor C D}
  (α : natural_transformation F G) :=
  { β : natural_transformation G F &
    FunCat_comp _ _ _ α β = FunCat_id F &
    FunCat_comp _ _ _ β α = FunCat_id G }.

Definition are_isomorphic_functors {C D} (F G : functor C D) :=
  { α : natural_transformation F G & is_iso_betw_fun α }.

(* according to Léonard, this definition below is equivalent to
   is_equiv_betw_cat_allioux, one direction being easy, but the
   other way around requires univalence *)

Definition is_equiv_betw_cat_guetta {C D} (F : functor C D) :=
  { G : functor D C &
    are_isomorphic_functors (functor_comp F G) (functor_id C) &
    are_isomorphic_functors (functor_comp G F) (functor_id D) }.

(* category of sets *)

Definition Set_type := { A : Type & isSet A }.

Definition st_type (st : Set_type) := projT1 st.
Definition st_is_set (st : Set_type) := projT2 st.

Theorem SetCat_Hom_set : ∀ x y : Set_type, isSet (st_type x → st_type y).
Proof.
intros (A, HA) (B, HB).
move B before A; cbn.
apply hott4cat.ex_3_1_6.
now intros a.
Qed.

Definition SetCat :=
  {| Obj := Set_type;
     Hom A B := st_type A → st_type B;
     comp A B C HAB HBC HA := HBC (HAB HA);
     idc _ A := A;
     unit_l _ _ _ := eq_refl;
     unit_r _ _ _ := eq_refl;
     assoc _ _ _ _ _ _ _ := eq_refl;
     Hom_set := SetCat_Hom_set |}.

(* representable functors *)

(*
  Hom(A,–) : C → Set
  This is a covariant functor given by:
    Hom(A,–) maps each object X in C to the set of morphisms, Hom(A, X)
    Hom(A,–) maps each morphism f : X → Y to the function
        Hom(A, f) : Hom(A, X) → Hom(A, Y) given by
        g ↦ f ∘ g for each g in Hom(A, X).
*)

Theorem hom_functor_comp_prop {C} {A : Obj C} :
  ∀ (B B' B'' : Obj C) (f : Hom B B') (g : Hom B' B''),
  (λ h, g ◦ f ◦ h) =
  (@comp SetCat (existT isSet (Hom A B) (Hom_set A B))
         (existT isSet (Hom A B') (Hom_set A B'))
         (existT isSet (Hom A B'') (Hom_set A B''))
         (λ h, f ◦ h) (λ h, g ◦ h)).
Proof.
intros.
apply extensionality; intros h.
apply assoc.
Qed.

Theorem hom_functor_id_prop {C} {A : Obj C} :
  ∀ B : Obj C,
  (λ h, idc B ◦ h) = (@idc SetCat (existT isSet (Hom A B) (Hom_set A B))).
Proof.
intros.
apply extensionality; intros h; cbn.
apply unit_r.
Qed.

Definition hom_functor {C} A : functor C SetCat :=
  {| f_map_obj X := existT isSet (Hom A X) (Hom_set A X) : Obj SetCat;
     f_map_hom _ _ F G := F ◦ G;
     f_comp_prop := hom_functor_comp_prop;
     f_id_prop := hom_functor_id_prop |}.

Definition is_representable_functor {C} (F : functor C SetCat) :=
  { X : Obj C & are_isomorphic_functors F (hom_functor X) }.

(* Yoneda lemma *)

(*
  Let F be an arbitrary functor from C to SetCat. Then Yoneda's lemma
  says that: (h^A being the hom_functor above)

  For each object A of C, the natural transformations from h^A to F
  are in one-to-one correspondence with the elements of F(A). That is,
     Nat (h^A, F) ≅ F (A)

  [...]

  (wikipedia)
*)

Definition Yoneda_NT_FA {C} (F : functor C SetCat) (A : Obj C) :
  natural_transformation (hom_functor A) F → st_type (f_map_obj F A) :=
  λ Φ, nt_hom Φ A (idc A) : st_type (f_map_obj F A).

Definition Yoneda_FA_NT {C} (F : functor C SetCat) (A : Obj C) :
  st_type (f_map_obj F A) → natural_transformation (hom_functor A) F.
Proof.
intros u.
set (ϑ := λ (X : Obj C) (f : Hom A X), f_map_hom F f u).
assert (Hϑ :
  ∀ (X Y : Obj C) (f : Hom X Y),
  (λ g : Hom A X, ϑ Y (f ◦ g)) =
  (λ g : Hom A X, f_map_hom F f (ϑ X g))). {
  intros.
  apply extensionality; intros g.
  unfold ϑ; cbn.
  now rewrite f_comp_prop.
}
apply (existT _ ϑ Hϑ).
Defined.

Lemma Yoneda {C} (F : functor C SetCat) (A : Obj C) :
  let NT := natural_transformation (hom_functor A) F in
  let FA := st_type (f_map_obj F A) in
  ∃ f : NT → FA, ∃ g : FA → NT,
  (∀ x : NT, g (f x) = x) ∧ (∀ y : FA, f (g y) = y).
Proof.
intros.
exists (Yoneda_NT_FA F A).
exists (Yoneda_FA_NT F A).
split.
-intros (η, Hη); cbn.
 apply eq_existT_uncurried.
 assert (p : (λ X f, f_map_hom F f (η A (idc A))) = η). {
   apply extensionality; intros X.
   apply extensionality; intros f.
   specialize (Hη A X f) as H1; cbn in H1.
   specialize (@hott4cat.happly _ _ _ _ H1 (idc A)) as H2.
   cbn in H2.
   now rewrite unit_l in H2.
 }
 exists p.
 apply extensionality; intros X.
 apply extensionality; intros Y.
 apply extensionality; intros f.
 apply hott4cat.ex_3_1_6.
 intros g.
 apply st_is_set.
-intros u; cbn.
 now rewrite f_id_prop; cbn.
Qed.

(* product of categories *)

Definition pair_unit_l {C1 C2} (X Y : Obj C1 * Obj C2)
     (f : Hom (fst X) (fst Y) * Hom (snd X) (snd Y)) :
  (fst f ◦ fst (idc (fst X), idc (snd X)),
   snd f ◦ snd (idc (fst X), idc (snd X))) = f.
Proof.
destruct f as (f1, f2); cbn.
now do 2 rewrite unit_l.
Qed.

Definition pair_unit_r {C1 C2} (X Y : Obj C1 * Obj C2)
     (f : Hom (fst X) (fst Y) * Hom (snd X) (snd Y)) :
  (fst (idc (fst Y), idc (snd Y)) ◦ fst f,
   snd (idc (fst Y), idc (snd Y)) ◦ snd f) = f.
Proof.
destruct f as (f1, f2); cbn.
now do 2 rewrite unit_r.
Qed.

Definition pair_assoc {C1 C2} (X Y Z T : Obj C1 * Obj C2)
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

Definition pair_isSet {C1 C2} (X Y : Obj C1 * Obj C2) :
  isSet (Hom (fst X) (fst Y) * Hom (snd X) (snd Y)).
Proof.
apply hott4cat.ex_3_1_5; apply Hom_set.
Qed.

Definition category_product (C1 C2 : category) : category :=
  {| Obj := Obj C1 * Obj C2;
     Hom X Y := (Hom (fst X) (fst Y) * Hom (snd X) (snd Y))%type;
     comp _ _ _ f g := (fst g ◦ fst f, snd g ◦ snd f);
     idc X := (idc (fst X), idc (snd X));
     unit_l := pair_unit_l;
     unit_r := pair_unit_r;
     assoc := pair_assoc;
     Hom_set := pair_isSet |}.

(*
  [...]

     Nat (h^A, F) ≅ F (A)

  Moreover this isomorphism is natural in A and F when both sides are
  regarded as functors from Set^C x C to Set. (Here the notation Set^C
  denotes the category of functors from C to Set.)
*)

Definition SetC_C (C : category) := category_product (FunCat C SetCat) C.

Definition functor_SetC_C_Set1_map_hom {C} (D := SetC_C C) (X Y : Obj D)
  (f : Hom X Y) : Hom (f_map_obj (fst X) (snd X)) (f_map_obj (fst Y) (snd Y)).
Proof.
cbn in X, Y, f.
intros T.
destruct X as (F, A).
destruct Y as (G, B).
destruct f as (f, g).
now apply f, (f_map_hom F g).
Defined.

Theorem functor_SetC_C_Set1_comp_prop {C} (D := SetC_C C) (X Y Z : Obj D)
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
apply extensionality; intros T; cbn.
rewrite f_comp_prop; cbn.
destruct η' as (η', η'_prop).
destruct η as (η, η_prop).
cbn in *.
apply f_equal.
specialize (η_prop Y Z g) as H1.
now specialize (@hott4cat.happly _ _ _ _ H1 (f_map_hom F f T)) as H2.
Qed.

Theorem functor_SetC_C_Set1_id_prop {C} (D := SetC_C C) (X : Obj D) :
  functor_SetC_C_Set1_map_hom X X (idc X) = idc (f_map_obj (fst X) (snd X)).
Proof.
cbn in *.
destruct X as (F, X); cbn.
apply extensionality; intros T; cbn.
now rewrite f_id_prop.
Qed.

Definition functor_SetC_C_Set1 C : functor (SetC_C C) SetCat :=
  {| f_map_obj (X : Obj (SetC_C C)) := f_map_obj (fst X) (snd X);
     f_map_hom := functor_SetC_C_Set1_map_hom;
     f_comp_prop := functor_SetC_C_Set1_comp_prop;
     f_id_prop := functor_SetC_C_Set1_id_prop |}.

Definition functor_SetC_C_Set2_map_obj {C} (A : Obj (SetC_C C)) : Obj SetCat.
Proof.
exists (natural_transformation (hom_functor (snd A)) (fst A)).
apply FunCat_Hom_set.
Defined.

Definition functor_SetC_C_Set2_map_hom {C} (X Y : Obj (SetC_C C))
    (f : Hom X Y) :
  Hom (functor_SetC_C_Set2_map_obj X) (functor_SetC_C_Set2_map_obj Y).
Proof.
cbn; intros η.
set (ϑ := λ A g, projT1 (fst f) A (projT1 η A (g ◦ snd f))).
exists ϑ.
intros Z T h.
apply extensionality; intros g; cbn; cbn in h, ϑ.
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
specialize @FunCat_comp_nt_commute as H2.
specialize (H2 C SetCat (hom_functor X) F G η η' Z T h).
cbn in H2.
unfold nt_hom in H2.
specialize (@hott4cat.happly _ _ _ _ H2 (g ◦ f)) as H3.
cbn in H3.
etransitivity; [ | apply H3 ].
do 2 apply f_equal.
apply assoc.
Defined.

Theorem functor_SetC_C_Set2_comp_prop {C} (X Y Z : Obj (SetC_C C))
    (f : Hom X Y) (g : Hom Y Z) :
  functor_SetC_C_Set2_map_hom X Z (g ◦ f) =
  functor_SetC_C_Set2_map_hom Y Z g ◦ functor_SetC_C_Set2_map_hom X Y f.
Proof.
apply extensionality; intros η.
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
unfold nt_hom.
assert (p
  : (λ (A : Obj C) (g0 : Hom Z A),
       projT1 η'' A (projT1 η' A (projT1 η A (g0 ◦ (g ◦ f))))) =
    (λ (A : Obj C) (g0 : Hom Z A),
       projT1 η'' A (projT1 η' A (projT1 η A (g0 ◦ g ◦ f))))). {
  apply extensionality; intros A.
  apply extensionality; intros h.
  do 3 apply f_equal.
  symmetry; apply assoc.
}
exists p; cbn.
apply extensionality; intros A.
apply extensionality; intros B.
apply extensionality; intros h.
apply hott4cat.ex_3_1_6.
intros i.
now destruct (f_map_obj H B).
Qed.

Theorem functor_SetC_C_Set2_id_prop {C} (X : Obj (SetC_C C)) :
  functor_SetC_C_Set2_map_hom X X (idc X) = idc (functor_SetC_C_Set2_map_obj X).
Proof.
apply extensionality; intros η; cbn.
destruct η as (η, Hη); cbn in *.
unfold functor_SetC_C_Set2_map_hom; cbn.
apply eq_existT_uncurried; cbn.
assert (p : (λ A g, f_map_hom (fst X) (idc A) (η A (g ◦ idc (snd X)))) = η). {
  apply extensionality; intros A.
  apply extensionality; intros f.
  rewrite unit_l.
  destruct X as (F, X); cbn in *.
  now rewrite f_id_prop.
}
exists p; cbn.
apply extensionality; intros Y.
apply extensionality; intros Z.
apply extensionality; intros f.
apply hott4cat.ex_3_1_6.
intros i.
now destruct (f_map_obj (fst X) Z).
Qed.

Definition functor_SetC_C_Set2 C : functor (SetC_C C) SetCat :=
  {| f_map_obj := functor_SetC_C_Set2_map_obj;
     f_map_hom := functor_SetC_C_Set2_map_hom;
     f_comp_prop := functor_SetC_C_Set2_comp_prop;
     f_id_prop := functor_SetC_C_Set2_id_prop |}.

Theorem Yoneda_natural {C} :
  natural_transformation (functor_SetC_C_Set1 C) (functor_SetC_C_Set2 C).
Proof.
unfold natural_transformation; cbn.
set (ϑ :=
  λ F : functor C SetCat * Obj C,
  let (F, A) as p
    return
      (st_type (f_map_obj (fst p) (snd p))
      → natural_transformation (hom_functor (snd p)) (fst p)) := F
  in
  λ T : st_type (f_map_obj F A),
  let ϑ := λ (X : Obj C) (f : Hom A X), f_map_hom F f T in
  existT _ ϑ
    (λ (X Y : Obj C) (f : Hom X Y),
     extensionality _
       (λ _ : Hom A X, st_type (f_map_obj F Y)) (λ HA : Hom A X, ϑ Y (f ◦ HA))
       (λ HA : Hom A X, f_map_hom F f (ϑ X HA))
       (λ g : Hom A X,
        eq_ind_r
          (λ h : Hom (f_map_obj F A) (f_map_obj F Y),
           h T = f_map_hom F f (f_map_hom F g T))
          eq_refl (f_comp_prop g f)))).
exists ϑ.
intros F G η.
apply extensionality; intros T.
unfold ϑ; cbn.
destruct F as (F, A).
destruct G as (G, B).
unfold functor_SetC_C_Set2_map_hom; cbn.
apply eq_existT_uncurried; cbn.
assert (p :
   (λ (X : Obj C) (f1 : Hom B X),
    f_map_hom G f1 (let (f2, g) := η in (projT1 f2) B (f_map_hom F g T))) =
   (λ (A : Obj C) (g : Hom B A),
    projT1 (fst η) A (f_map_hom F (g ◦ snd η) T))). {
  apply extensionality; intros X.
  apply extensionality; intros f.
  destruct η as (η, g); cbn in *.
  destruct η as (η, Hη); cbn.
  rewrite f_comp_prop; cbn.
  specialize (Hη B X f) as H1; cbn in H1.
  specialize (@hott4cat.happly _ _ _ _ H1) as H2; cbn in H2.
  symmetry; apply H2.
}
exists p.
cbn.
apply extensionality; intros X.
apply extensionality; intros Y.
apply extensionality; intros g.
apply hott4cat.ex_3_1_6.
intros h.
now destruct (f_map_obj G Y).
Qed.
