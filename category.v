(* categories *)
(* http://angg.twu.net/tmp/2016-optativa/awodey__category_theory.pdf *)

Require Import Utf8.
Require hott4cat.
Set Nested Proofs Allowed.

Axiom extensionality : ∀ A B (f g : ∀ x : A, B x), (∀ x, f x = g x) → f = g.

Definition isSet (A : Type) := ∀ (a b : A) (p q : a = b), p = q.

Class category :=
  { Obj : Type;
    Hom : Obj → Obj → Type;
    comp : ∀ {A B C}, Hom A B → Hom B C → Hom A C;
    hid : ∀ {A}, Hom A A;
    unit_l : ∀ {A B} (f : Hom A B), comp hid f = f;
    unit_r : ∀ {A B} (f : Hom A B), comp f hid = f;
    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D),
      comp f (comp g h) = comp (comp f g) h;
    Hom_set x y : isSet (Hom x y) }.

Arguments Hom [_].
Notation "g '◦' f" := (comp f g) (at level 40, left associativity).

Arguments Obj : clear implicits.

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
     hid := @hid C;
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
    f_map_arr {a b} : Hom a b → Hom (f_map_obj a) (f_map_obj b);
    f_comp_prop {a b c} (f : Hom a b) (g : Hom b c) :
      f_map_arr (g ◦ f) = f_map_arr g ◦ f_map_arr f;
    f_id_prop {a} : @f_map_arr a _ hid = hid }.

Arguments f_map_obj [_] [_] _.
Arguments f_map_arr [_] [_] _ [_] [_].

Definition fop {C D} : functor C D → functor (op C) (op D) :=
  λ F,
  {| f_map_obj (x : Obj (op C)) := (@f_map_obj C D F x : Obj (op D));
     f_map_arr _ _ f := f_map_arr F f;
     f_comp_prop _ _ _ f g := @f_comp_prop _ _ F _ _ _ g f;
     f_id_prop a := @f_id_prop _ _ F a |}.

Definition is_isomorphism {C : category} {A B : Obj C} (f : Hom A B) :=
  ∃ g : Hom B A, g ◦ f = hid ∧ f ◦ g = hid.

(* A cone to a functor D(J,C) consists of an object c in C and a
   family of arrows in C : cj : c → Dj one for each object j ∈ J, such
   that for each arrow α : i → j in J, the following triangle
   commutes. *)

Record cone {J C} (D : functor J C) :=
  { cn_top : Obj C;
    cn_fam : ∀ j, Hom cn_top (f_map_obj D j);
    cn_commute : ∀ i j (α : Hom i j), cn_fam j = f_map_arr D α ◦ cn_fam i }.

Record co_cone {J C} (D : functor J C) :=
  { cc_top : Obj C;
    cc_fam : ∀ j, Hom (f_map_obj D j) cc_top;
    cc_commute : ∀ i j (α : Hom i j), cc_fam i = cc_fam j ◦ f_map_arr D α }.

Arguments cn_top [_] [_] [_].
Arguments cn_fam [_] [_] [_].
Arguments cc_top [_] [_] [_].
Arguments cc_fam [_] [_] [_].

(* category of cones & co-cones *)

Definition Cone_Hom {J C} {D : functor J C} (cn cn' : cone D) :=
  { ϑ : Hom (cn_top cn) (cn_top cn') & ∀ j, cn_fam cn j = cn_fam cn' j ◦ ϑ }.

Definition CoCone_Hom {J C} {D : functor J C} (cc cc' : co_cone D) :=
  { ϑ : Hom (cc_top cc) (cc_top cc') & ∀ j, cc_fam cc' j = ϑ ◦ cc_fam cc j }.

Definition Cone_comp {J C} {D : functor J C} (c c' c'' : cone D)
  (f : Cone_Hom c c') (g : Cone_Hom c' c'') : Cone_Hom c c''.
Proof.
exists (projT1 g ◦ projT1 f).
intros j.
etransitivity.
-apply (projT2 f j).
-etransitivity; [ | apply assoc ].
 f_equal.
 apply (projT2 g j).
Defined.

Definition CoCone_comp {J C} {D : functor J C} (c c' c'' : co_cone D)
  (f : CoCone_Hom c c') (g : CoCone_Hom c' c'') : CoCone_Hom c c''.
Proof.
exists (projT1 g ◦ projT1 f).
intros j.
etransitivity.
-apply (projT2 g j).
-etransitivity; [ | symmetry; apply assoc ].
 f_equal.
 apply (projT2 f j).
Defined.

Definition Cone_id {J C} {D : functor J C} (c : cone D) : Cone_Hom c c :=
   existT (λ ϑ, ∀ j, cn_fam c j = cn_fam c j ◦ ϑ) hid
     (λ j, eq_sym (unit_l (cn_fam c j))).

Definition CoCone_id {J C} {D : functor J C} (c : co_cone D) : CoCone_Hom c c :=
   existT (λ ϑ, ∀ j, cc_fam c j = ϑ ◦ cc_fam c j) hid
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

Definition Cone {J C} (D : functor J C) :=
  {| Obj := cone D;
     Hom := Cone_Hom;
     comp := Cone_comp;
     hid := Cone_id;
     unit_l := Cone_unit_l;
     unit_r := Cone_unit_r;
     assoc := Cone_assoc;
     Hom_set := Cone_Hom_set |}.

(* category of co-cones *)

Definition CoCone {J C} (D : functor J C) :=
  {| Obj := co_cone D;
     Hom := CoCone_Hom;
     comp := CoCone_comp;
     hid := CoCone_id;
     unit_l := CoCone_unit_l;
     unit_r := CoCone_unit_r;
     assoc := CoCone_assoc;
     Hom_set := CoCone_Hom_set |}.

(* A limit for a functor D : J → C is a terminal object in Cone(D)
   and a colimit an initial object in CoCone(D) *)

Definition is_limit {J C} {D : functor J C} (cn : cone D) :=
  @is_terminal (Cone D) cn.

Definition is_colimit {J C} {D : functor J C} (cc : co_cone D) :=
  @is_initial (CoCone D) cc.

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
exists (projT1 f).
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

(* other definition of category of co-cones *)

Definition CoCone2 {J C} (D : functor J C) := op (Cone (fop D)).

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

Definition F_CoCone_CoCone2_comp_prop {J C} {D : functor J C} {x y z : Obj (CoCone D)} :
  ∀ (f : Hom x y) (g : Hom y z),
   g ◦ f =
   @comp (CoCone2 D) (cone_fop_of_co_cone x) (cone_fop_of_co_cone y)
       (cone_fop_of_co_cone z) f g.
Proof.
intros; cbn.
apply eq_existT_uncurried; cbn.
exists eq_refl; cbn.
apply extensionality.
intros j.
apply Hom_set.
Defined.

Definition F_CoCone2_CoCone_comp_prop {J C} {D : functor J C} {x y z : Obj (CoCone2 D)} :
  ∀ (f : Hom x y) (g : Hom y z),
  g ◦ f =
  @comp (CoCone D) (co_cone_of_cone_fop x) (co_cone_of_cone_fop y)
        (co_cone_of_cone_fop z) f g.
Proof.
intros; cbn.
apply eq_existT_uncurried; cbn.
exists eq_refl; cbn.
apply extensionality.
intros j.
apply Hom_set.
Defined.

Definition F_CoCone_CoCone2 {J C} {D : functor J C} :
    functor (CoCone D) (CoCone2 D) :=
  {| f_map_obj := cone_fop_of_co_cone : Obj (CoCone D) → Obj (CoCone2 D);
     f_map_arr _ _ f := f;
     f_comp_prop _ _ _ := F_CoCone_CoCone2_comp_prop;
     f_id_prop _ := eq_refl |}.

Definition F_CoCone2_CoCone {J C} {D : functor J C} :
    functor (CoCone2 D) (CoCone D) :=
  {| f_map_obj := co_cone_of_cone_fop : Obj (CoCone2 D) → Obj (CoCone D);
     f_map_arr _ _ f := f;
     f_comp_prop _ _ _ := F_CoCone2_CoCone_comp_prop;
     f_id_prop _ := eq_refl |}.

...

Theorem F_CoCone_CoCone2_id1 {J C} {D : functor J C} :
  ∀ cc, f_map_obj F_CoCone2_CoCone (f_map_obj F_CoCone_CoCone2 cc) = cc.
Proof. now intros; destruct cc. Qed.

Theorem F_CoCone_CoCone2_id2 {J C} {D : functor J C} :
  ∀ cc, f_map_obj F_CoCone_CoCone2 (f_map_obj F_CoCone2_CoCone cc) = cc.
Proof. now intros; destruct cc. Qed.

Check transport.

Definition are_isomorphic_categories (C D : category) :=
  { F : functor C D &
    { G : functor D C &
      ((∀ x, f_map_obj G (f_map_obj F x) = x) *
       (∀ y, f_map_obj F (f_map_obj G y) = y))%type } }.

...
       (∀ x y (f : Hom x y), f_map_arr G (f_map_arr F f) = f)

Print functor.

...

Definition are_equivalent_categories (C D : category) :=
  (functor C D * functor D C)%type.

Theorem CoCone_and_CoCone2_are_equivalent {J C} {D : functor J C} :
  are_equivalent_categories (CoCone D) (CoCone2 (fop D)).
Proof.
split.
-apply functor_CoCone2_of_CoCone.
-apply functor_CoCone_of_CoCone2.
Qed.

Definition functor_CoCone4_of_CoCone2 {J C} {D : functor J C} :
  functor (CoCone4 (fop D)) (CoCone4 (fop D)) :=
  {| f_map_obj x := x;
     f_map_arr x y f := f;
     f_comp_prop x y z f g := eq_refl;
     f_id_prop _ := eq_refl |}.

Definition functor_CoCone2_of_CoCone4 {J C} {D : functor J C} :
  functor (CoCone2 (fop D)) (CoCone2 (fop D)) :=
  {| f_map_obj x := x;
     f_map_arr x y f := f;
     f_comp_prop x y z f g := eq_refl;
     f_id_prop _ := eq_refl |}.

Definition functor_comp {A B C} : functor A B → functor B C → functor A C :=
  λ F G,
  {| f_map_obj a := f_map_obj G (f_map_obj F a);
     f_map_arr _ _ f := f_map_arr G (f_map_arr F f);
     f_comp_prop x y z f g :=
       eq_trans (f_equal (@f_map_arr _ _ _ _ (f_map_obj F z)) (f_comp_prop f g))
                (f_comp_prop (f_map_arr F f) (f_map_arr F g));
     f_id_prop x :=
       eq_trans (f_equal (@f_map_arr _ _ _ _ (f_map_obj F x)) f_id_prop) f_id_prop |}.

... à voir...

Definition functor_CoCone4_of_CoCone {J C} {D : functor J C} :
    functor (CoCone D) (CoCone4 (fop D)) :=
  functor_comp
    (@functor_CoCone2_of_CoCone4 J C D)
    (functor_CoCone_of_CoCone2).
...

(*
Definition glop {J C} {D : functor J C} :
  ∀ (x y : Obj (CoCone D)) (f : Hom x y),
  @Hom (CoCone4 (fop D)) (cone_fop_of_co_cone x) (cone_fop_of_co_cone y).
intros.
cbn in *.
Print Cone_Hom.
exists f.
intros j; cbn in *.
Check cc_fam.
Check cc_commute.
...
Show Proof.
Search comp.
Check cc_commute.
...
destruct x, y; cbn in *.
specialize (cc_commute1 j j) as H1.
...
*)

Set Printing Implicit.

Definition functor_CoCone4_of_CoCone {J C} {D : functor J C} :
  functor (CoCone D) (CoCone4 (fop D)) :=
  {| f_map_obj := cone_fop_of_co_cone : Obj (CoCone _) → Obj (CoCone4 _);
     f_map_arr x y f := 2 |}.
     f_map_arr := glop |}.
