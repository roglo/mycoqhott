(* categories: cones and limits *)

Set Universe Polymorphism.
Require Import Utf8.
Require Import category.

(* A cone to a functor D(J,C) consists of an object c in C and a
   family of arrows in C : cj : c → Dj one for each object j ∈ J, such
   that for each arrow α : i → j in J, the following triangle
   commutes. *)

Record cone {J C} (D : functor J C) :=
  { cn_top : Ob C;
    cn_fam : ∀ j, Hom cn_top (f_map_obj D j);
    cn_commute : ∀ i j (α : Hom i j), cn_fam j = f_map_hom D α ◦ cn_fam i }.

Record co_cone {J C} (D : functor J C) :=
  { cc_top : Ob C;
    cc_fam : ∀ j, Hom (f_map_obj D j) cc_top;
    cc_commute : ∀ i j (α : Hom i j), cc_fam i = cc_fam j ◦ f_map_hom D α }.

Arguments cn_top [_] [_] [_].
Arguments cn_fam [_] [_] [_].
Arguments cn_commute [_] [_] [_].
Arguments cc_top [_] [_] [_].
Arguments cc_fam [_] [_] [_].
Arguments cc_commute [_] [_] [_].
Arguments cone _ _ D%Fun.
Arguments co_cone _ _ D%Fun.

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

Definition Cone_comp {J C} {D : functor J C} {c c' c'' : cone D}
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

Definition CoCone_comp {J C} {D : functor J C} {c c' c'' : co_cone D}
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
  Cone_comp (Cone_id c) f = f.
Proof.
intros.
unfold Cone_comp; cbn.
destruct f as (f & Hf); cbn.
apply eq_existT_uncurried.
exists (unit_l _).
apply fun_ext.
intros j.
apply Hom_set.
Defined.

Theorem CoCone_unit_l {J C} {D : functor J C} :
  ∀ (c c' : co_cone D) (f : CoCone_Hom c c'),
  CoCone_comp (CoCone_id c) f = f.
Proof.
intros.
unfold CoCone_comp; cbn.
destruct f as (f & Hf); cbn.
apply eq_existT_uncurried.
exists (unit_l _).
apply fun_ext.
intros j.
apply Hom_set.
Defined.

Theorem Cone_unit_r {J C} {D : functor J C} :
  ∀ (c c' : cone D) (f : Cone_Hom c c'),
  Cone_comp f (Cone_id c') = f.
Proof.
intros.
unfold Cone_comp; cbn.
destruct f as (f & Hf); cbn.
apply eq_existT_uncurried.
exists (unit_r _).
apply fun_ext.
intros j.
apply Hom_set.
Defined.

Theorem CoCone_unit_r {J C} {D : functor J C} :
  ∀ (c c' : co_cone D) (f : CoCone_Hom c c'),
  CoCone_comp f (CoCone_id c') = f.
Proof.
intros.
destruct f as (f & Hf); cbn.
apply eq_existT_uncurried.
exists (unit_r _).
apply fun_ext.
intros j.
apply Hom_set.
Defined.

Theorem Cone_assoc {J C} {D : functor J C} :
  ∀ (c c' c'' c''' : cone D) (f : Cone_Hom c c') (g : Cone_Hom c' c'')
    (h : Cone_Hom c'' c'''),
    Cone_comp f (Cone_comp g h) = Cone_comp (Cone_comp f g) h.
Proof.
intros.
unfold Cone_comp; cbn.
apply eq_existT_uncurried.
exists (assoc _ _ _).
apply fun_ext.
intros j.
apply Hom_set.
Defined.

Theorem CoCone_assoc {J C} {D : functor J C} :
  ∀ (c c' c'' c''' : co_cone D) (f : CoCone_Hom c c') (g : CoCone_Hom c' c'')
    (h : CoCone_Hom c'' c'''),
    CoCone_comp f (CoCone_comp g h) = CoCone_comp (CoCone_comp f g) h.
Proof.
intros.
apply eq_existT_uncurried.
exists (assoc _ _ _).
apply fun_ext.
intros j.
apply Hom_set.
Defined.

Theorem Cone_Hom_set {J C} {D : functor J C} :
  ∀ c c' : cone D, isSet (Cone_Hom c c').
Proof.
intros.
unfold Cone_Hom.
apply h4c.is_set_is_set_sigT; [ | apply Hom_set ].
intros f.
intros p q.
apply fun_ext.
intros x.
apply Hom_set.
Qed.

Theorem CoCone_Hom_set {J C} {D : functor J C} :
  ∀ c c' : co_cone D, isSet (CoCone_Hom c c').
Proof.
intros.
unfold CoCone_Hom.
apply h4c.is_set_is_set_sigT; [ | apply Hom_set ].
intros f.
intros p q.
apply fun_ext.
intros x.
apply Hom_set.
Qed.

Definition ConeCat {J C} (D : functor J C) :=
  {| Ob := cone D;
     Hom := Cone_Hom;
     comp _ _ _ := Cone_comp;
     idc := Cone_id;
     unit_l := Cone_unit_l;
     unit_r := Cone_unit_r;
     assoc := Cone_assoc;
     Hom_set := Cone_Hom_set |}.

Definition CoConeCat {J C} (D : functor J C) :=
  {| Ob := co_cone D;
     Hom := CoCone_Hom;
     comp _ _ _ := CoCone_comp;
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
assert (Hh' : ∀ j : Ob J, cn_fam c j = cn_fam l j ◦ h). {
  intros j; specialize (Hh j).
  now symmetry.
}
remember
  (existT
     (λ ϑ : Hom (cn_top c) (cn_top l),
      ∀ j : Ob J, cn_fam c j = cn_fam l j ◦ ϑ) h Hh') as hh.
now rewrite (H1 hh); subst hh.
Qed.

(* another definition of category of co-cones *)

Definition CoConeCat2 {J C} (D : functor J C) := op (ConeCat (fop D)).

Definition cone_fop_of_co_cone {J C} {D : functor J C} :
    co_cone D → cone (fop D) :=
  λ cc,
  {| cn_top := cc_top cc : Ob (op C);
     cn_fam j := cc_fam cc j : @Hom (op C) (cc_top cc) (f_map_obj (fop D) j);
     cn_commute i j := cc_commute cc j i |}.

Definition co_cone_of_cone_fop {J C} {D : functor J C} :
    cone (fop D) → co_cone D :=
  λ cn,
  {| cc_top := cn_top cn : Ob C;
     cc_fam j := cn_fam cn j : @Hom (op C) (cn_top cn) (f_map_obj D j);
     cc_commute i j := cn_commute cn j i |}.

Definition F_CoConeCat_CoConeCat2_comp_prop {J C} {D : functor J C}
  {x y z : Ob (CoConeCat D)} :
  ∀ (f : Hom x y) (g : Hom y z),
   g ◦ f =
   @comp (CoConeCat2 D) (cone_fop_of_co_cone x) (cone_fop_of_co_cone y)
       (cone_fop_of_co_cone z) f g.
Proof.
intros; cbn.
apply eq_existT_uncurried; cbn.
exists eq_refl; cbn.
apply fun_ext.
intros j.
apply Hom_set.
Defined.

Definition F_CoConeCat2_CoConeCat_comp_prop {J C} {D : functor J C}
  {x y z : Ob (CoConeCat2 D)} :
  ∀ (f : Hom x y) (g : Hom y z),
  g ◦ f =
  @comp (CoConeCat D) (co_cone_of_cone_fop x) (co_cone_of_cone_fop y)
        (co_cone_of_cone_fop z) f g.
Proof.
intros; cbn.
apply eq_existT_uncurried; cbn.
exists eq_refl; cbn.
apply fun_ext.
intros j.
apply Hom_set.
Defined.

Definition F_CoConeCat_CoConeCat2 {J C} {D : functor J C} :
    functor (CoConeCat D) (CoConeCat2 D) :=
  {| f_map_obj :=
       cone_fop_of_co_cone : Ob (CoConeCat D) → Ob (CoConeCat2 D);
     f_map_hom _ _ f := f;
     f_comp_prop _ _ _ := F_CoConeCat_CoConeCat2_comp_prop;
     f_id_prop _ := eq_refl |}.

Definition F_CoConeCat2_CoConeCat {J C} {D : functor J C} :
    functor (CoConeCat2 D) (CoConeCat D) :=
  {| f_map_obj :=
       co_cone_of_cone_fop : Ob (CoConeCat2 D) → Ob (CoConeCat D);
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
