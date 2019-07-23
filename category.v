(* categories *)
(* http://angg.twu.net/tmp/2016-optativa/awodey__category_theory.pdf *)

Set Universe Polymorphism.
Require Import Utf8.
Require ClassicalFacts.
Require hott4cat.
Set Nested Proofs Allowed.

Definition isSet := hott4cat.isSet.
Definition isProp := hott4cat.isProp.

Definition hProp := { A : Type & isProp A }.

Axiom fun_ext : ∀ A B (f g : ∀ x : A, B x), (∀ x, f x = g x) → f = g.
Axiom prop_ext : ∀ A B, (A ↔ B) → A = B.

Theorem proof_irrel : isSet Prop.
intros a1 a2.
apply (ClassicalFacts.ext_prop_dep_proof_irrel_cic prop_ext).
Qed.

Declare Scope category_scope.
Declare Scope functor_scope.
Declare Scope nat_transf_scope.
Delimit Scope category_scope with Cat.
Delimit Scope functor_scope with Fun.
Delimit Scope nat_transf_scope with NT.

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
Arguments Obj C%Cat : rename.
Arguments Hom [_%Cat].
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

(* functors *)

Class functor (C D : category) :=
  { f_map_obj : Obj C → Obj D;
    f_map_hom {a b} : Hom a b → Hom (f_map_obj a) (f_map_obj b);
    f_comp_prop {a b c} (f : Hom a b) (g : Hom b c) :
      f_map_hom (g ◦ f) = f_map_hom g ◦ f_map_hom f;
    f_id_prop {a} : @f_map_hom a _ (idc a) = idc (f_map_obj a) }.

Arguments functor C%Cat D%Cat.
Arguments f_map_obj [_] [_] _%Fun.
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

Notation "g '◦' f" := (functor_comp f g) (at level 40, left associativity) :
  functor_scope.
Notation "¹ C" := (functor_id C) (at level 35) :
  functor_scope.

(* *)

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
apply hott4cat.is_set_is_set_sigT; [ | apply Hom_set ].
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
apply hott4cat.is_set_is_set_sigT; [ | apply Hom_set ].
intros f.
intros p q.
apply fun_ext.
intros x.
apply Hom_set.
Qed.

Definition ConeCat {J C} (D : functor J C) :=
  {| Obj := cone D;
     Hom := Cone_Hom;
     comp _ _ _ := Cone_comp;
     idc := Cone_id;
     unit_l := Cone_unit_l;
     unit_r := Cone_unit_r;
     assoc := Cone_assoc;
     Hom_set := Cone_Hom_set |}.

Definition CoConeCat {J C} (D : functor J C) :=
  {| Obj := co_cone D;
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
     cn_commute i j := cc_commute cc j i |}.

Definition co_cone_of_cone_fop {J C} {D : functor J C} :
    cone (fop D) → co_cone D :=
  λ cn,
  {| cc_top := cn_top cn : Obj C;
     cc_fam j := cn_fam cn j : @Hom (op C) (cn_top cn) (f_map_obj D j);
     cc_commute i j := cn_commute cn j i |}.

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
apply fun_ext.
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
apply fun_ext.
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

Arguments natural_transformation _ _ F%Fun G%Fun.

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
  ∀ (x y : Obj C) (f : Hom x y),
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

Theorem Fun_unit_l {C D} (F G : functor C D) :
  ∀ (f : natural_transformation F G), nat_transf_comp (nat_transf_id F) f = f.
Proof.
intros.
destruct f as (f, Hf).
unfold nat_transf_comp; cbn.
apply eq_existT_uncurried.
assert (p : (λ x : Obj C, f x ◦ idc (f_map_obj F x)) = f). {
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
assert (p : (λ x : Obj C, idc (f_map_obj G x) ◦ f x) = f). {
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
apply hott4cat.is_set_is_set_sigT. {
  intros ϑ f g.
  apply fun_ext; intros x.
  apply fun_ext; intros y.
  apply fun_ext; intros h.
  apply Hom_set.
}
apply hott4cat.isSet_forall.
intros x.
apply Hom_set.
Qed.

Definition FunCat C D :=
  {| Obj := functor C D;
     Hom := natural_transformation;
     comp _ _ _ := nat_transf_comp;
     idc := nat_transf_id;
     unit_l := Fun_unit_l;
     unit_r := Fun_unit_r;
     assoc := Fun_assoc;
     Hom_set := Fun_Hom_set |}.

Notation "g '◦' f" := (nat_transf_comp f g) (at level 40, left associativity) :
  nat_transf_scope.

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

Definition CatCat_comp {C C' C'' : category}
  (F : functor C C') (G : functor C' C'') : functor C C'' :=
  {| f_map_obj X := f_map_obj G (f_map_obj F X);
     f_map_hom X Y f := f_map_hom G (f_map_hom F f);
     f_comp_prop := CatCat_comp_prop;
     f_id_prop := CatCat_id_prop |}.

Theorem CatCat_unit_l (C C' : category) (F : functor C C') :
  CatCat_comp (functor_id C) F = F.
Proof.
unfold CatCat_comp, functor_id; cbn.
destruct F; cbn in *.
f_equal.
-apply fun_ext; intros X.
 apply fun_ext; intros Y.
 apply fun_ext; intros Z.
 apply fun_ext; intros f.
 apply fun_ext; intros g.
 apply Hom_set.
-apply fun_ext; intros X.
 apply Hom_set.
Qed.

Theorem CatCat_unit_r (C C' : category) (F : functor C C') :
  CatCat_comp F (functor_id C') = F.
Proof.
unfold CatCat_comp, functor_id; cbn.
destruct F; cbn in *.
f_equal.
-apply fun_ext; intros X.
 apply fun_ext; intros Y.
 apply fun_ext; intros Z.
 apply fun_ext; intros f.
 apply fun_ext; intros g.
 apply Hom_set.
-apply fun_ext; intros X.
 apply Hom_set.
Qed.

Theorem CatCat_assoc C C' C'' C'''
  (F : functor C C') (G : functor C' C'') (H : functor C'' C''') :
  CatCat_comp F (CatCat_comp G H) = CatCat_comp (CatCat_comp F G) H.
Proof.
unfold CatCat_comp; cbn.
f_equal.
-unfold CatCat_comp_prop; cbn.
 apply fun_ext; intros X.
 apply fun_ext; intros Y.
 apply fun_ext; intros Z.
 apply fun_ext; intros f.
 apply fun_ext; intros g; cbn.
 unfold eq_trans, f_equal.
 destruct
   (f_comp_prop (f_map_hom G (f_map_hom F f)) (f_map_hom G (f_map_hom F g))).
 destruct (f_comp_prop (f_map_hom F f) (f_map_hom F g)).
 now destruct (f_comp_prop f g).
-unfold CatCat_id_prop.
 apply fun_ext; intros X.
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
     comp _ _ := CatCat_comp;
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
apply hott4cat.isSet_pair; apply Hom_set.
Qed.

Definition cat_prod (C1 C2 : category) : category :=
  {| Obj := Obj C1 * Obj C2;
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
    (X Y Z : Obj (cat_prod C C')) (f : Hom X Y) (g : Hom Y Z) :
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
    (X : Obj (cat_prod C C')) :
  (f_map_hom F (fst (idc X)), f_map_hom F' (snd (idc X))) =
  @idc (cat_prod D D') (f_map_obj F (fst X), f_map_obj F' (snd X)).
Proof.
now cbn; do 2 rewrite f_id_prop.
Defined.

Definition functor_prod {C C' D D'} (F : functor C D) (F' : functor C' D') :
  functor (cat_prod C C') (cat_prod D D') :=
  {| f_map_obj (X : Obj (cat_prod C C')) :=
       (f_map_obj F (fst X), f_map_obj F' (snd X)) : Obj (cat_prod D D');
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
apply hott4cat.isSet_forall.
now intros a.
Qed.

Definition SetCat :=
  {| Obj := Set_type;
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

Theorem cov_hom_functor_comp_prop {C} {A : Obj C} :
  ∀ (B B' B'' : Obj C) (f : Hom B B') (g : Hom B' B''),
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

Theorem cov_hom_functor_id_prop {C} {A : Obj C} :
  ∀ B : Obj C,
  (λ h, idc B ◦ h) = (@idc SetCat (existT isSet (Hom A B) (Hom_set A B))).
Proof.
intros.
apply fun_ext; intros h; cbn.
apply unit_r.
Qed.

Definition cov_hom_functor {C} (A : Obj C) : functor C SetCat :=
  {| f_map_obj (X : Obj C) := existT isSet (Hom A X) (Hom_set A X) : Obj SetCat;
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

Definition con_hom_functor {C} (B : Obj C) : functor (op C) SetCat :=
  {| f_map_obj (X : Obj (op C)) :=
       existT isSet (@Hom C X B) (@Hom_set C X B) : Obj SetCat;
     f_map_hom (X Y : Obj C) (H : @Hom C Y X) (G : @Hom C X B) := G ◦ H;
     f_comp_prop := @cov_hom_functor_comp_prop (op C) B;
     f_id_prop := @cov_hom_functor_id_prop (op C) B |}.

Theorem con_hom_functor_is_cov_hom_functor_op {C} {A : Obj C} :
  con_hom_functor A = @cov_hom_functor (op C) A.
Proof. easy. Qed.

(* Hom functor: bifunctor of covariant and contravariant *)

(* erroneous definition

Definition hom_functor_map_obj {C} (A B : Obj C)
  (X : Obj (cat_prod (op C) C)) : Obj SetCat :=
  existT isSet (@Hom C A (snd X) * @Hom C (fst X) B)%type
    (hott4cat.isSet_pair (@Hom_set C A (snd X)) (@Hom_set C (fst X) B)).

Definition hom_functor_map_hom {C} (A B : Obj C)
  (X Y : Obj (cat_prod (op C) C)) (f : Hom X Y) :
  Hom (hom_functor_map_obj A B X) (hom_functor_map_obj A B Y).
Proof.
intros g.
split.
-eapply comp; [ apply (fst g) | apply (snd f) ].
-eapply comp; [ apply (fst f) | apply (snd g) ].
Defined.

Theorem hom_functor_comp_prop {C} (A B : Obj C)
  (X Y Z : Obj (cat_prod (op C) C))
  (f : Hom X Y) (g : Hom Y Z) :
  hom_functor_map_hom A B X Z (g ◦ f) =
  hom_functor_map_hom A B Y Z g ◦ hom_functor_map_hom A B X Y f.
Proof.
unfold hom_functor_map_hom; cbn.
apply fun_ext; intros h; cbn in h; cbn.
now do 2 rewrite assoc.
Qed.

Theorem hom_functor_id_prop {C} (A B : Obj C)
  (X : Obj (cat_prod C (op C))) :
  hom_functor_map_hom A B X X (idc X) = idc (hom_functor_map_obj A B X).
Proof.
unfold hom_functor_map_hom; cbn.
apply fun_ext; intros h; cbn in h; cbn.
rewrite unit_l, unit_r.
now destruct h.
Qed.

Definition hom_functor {C} (A B : Obj C) :
    functor (cat_prod (op C) C) SetCat :=
  {| f_map_obj X := hom_functor_map_obj A B X : Obj SetCat;
     f_map_hom := hom_functor_map_hom A B;
     f_comp_prop := hom_functor_comp_prop A B;
     f_id_prop := hom_functor_id_prop A B |}.
*)

Definition hom_functor_map_obj {C} (X : Obj (op C × C)) : Obj SetCat :=
  existT isSet (@Hom C (fst X) (snd X)) (@Hom_set C (fst X) (snd X)).

Definition hom_functor_map_hom {C} {X Y : Obj (op C × C)} (f : Hom X Y) :
  Hom (@hom_functor_map_obj C X) (@hom_functor_map_obj C Y) :=
  λ g,
  (@comp C (fst Y) (fst X) (snd Y) (fst f)
     (@comp C (fst X) (snd X) (snd Y) g (snd f))).

Theorem hom_functor_comp_prop {C} {X Y Z : Obj (op C × C)}
  (f : Hom X Y) (g : Hom Y Z) :
  hom_functor_map_hom (g ◦ f) = hom_functor_map_hom g ◦ hom_functor_map_hom f.
Proof.
unfold hom_functor_map_hom; cbn.
apply fun_ext; intros h.
now do 5 rewrite assoc.
Defined.

Theorem hom_functor_id_prop {C} (X : Obj (op C × C)) :
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

...

(* representable functors *)

Definition is_representable_functor {C} (F : functor C SetCat) :=
  { X : Obj C & are_isomorphic_functors F (cov_hom_functor X) }.

(* Yoneda lemma *)

(*
  Let F be an arbitrary functor from C to SetCat. Then Yoneda's lemma
  says that: (h^A being the cov_hom_functor above)

  For each object A of C, the natural transformations from h^A to F
  are in one-to-one correspondence with the elements of F(A). That is,
     Nat (h^A, F) ≅ F (A)

  [...]

  (wikipedia)
*)

Definition Yoneda_NT_FA {C} (F : functor C SetCat) (A : Obj C) :
  natural_transformation (cov_hom_functor A) F → st_type (f_map_obj F A) :=
  λ Φ, nt_component Φ A (idc A) : st_type (f_map_obj F A).

Definition Yoneda_FA_NT {C} (F : functor C SetCat) (A : Obj C) :
  st_type (f_map_obj F A) → natural_transformation (cov_hom_functor A) F.
Proof.
intros u.
set (ϑ := λ (X : Obj C) (f : Hom A X), f_map_hom F f u).
assert (Hϑ :
  ∀ (X Y : Obj C) (f : Hom X Y),
  (λ g : Hom A X, ϑ Y (f ◦ g)) =
  (λ g : Hom A X, f_map_hom F f (ϑ X g))). {
  intros.
  apply fun_ext; intros g.
  unfold ϑ; cbn.
  now rewrite f_comp_prop.
}
apply (existT _ ϑ Hϑ).
Defined.

Lemma Yoneda {C} (F : functor C SetCat) (A : Obj C) :
  let NT := natural_transformation (cov_hom_functor A) F in
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
   apply fun_ext; intros X.
   apply fun_ext; intros f.
   specialize (Hη A X f) as H1; cbn in H1.
   specialize (@hott4cat.happly _ _ _ _ H1 (idc A)) as H2.
   cbn in H2.
   now rewrite unit_l in H2.
 }
 exists p.
 apply fun_ext; intros X.
 apply fun_ext; intros Y.
 apply fun_ext; intros f.
 apply hott4cat.isSet_forall.
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
apply fun_ext; intros T; cbn.
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
apply fun_ext; intros T; cbn.
now rewrite f_id_prop.
Qed.

Definition functor_SetC_C_Set1 C : functor (SetC_C C) SetCat :=
  {| f_map_obj (X : Obj (SetC_C C)) := f_map_obj (fst X) (snd X);
     f_map_hom := functor_SetC_C_Set1_map_hom;
     f_comp_prop := functor_SetC_C_Set1_comp_prop;
     f_id_prop := functor_SetC_C_Set1_id_prop |}.

Definition functor_SetC_C_Set2_map_obj {C} (A : Obj (SetC_C C)) : Obj SetCat.
Proof.
exists (natural_transformation (cov_hom_functor (snd A)) (fst A)).
apply Fun_Hom_set.
Defined.

Definition functor_SetC_C_Set2_map_hom {C} (X Y : Obj (SetC_C C))
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
  : (λ (A : Obj C) (g0 : Hom Z A),
       projT1 η'' A (projT1 η' A (projT1 η A (g0 ◦ (g ◦ f))))) =
    (λ (A : Obj C) (g0 : Hom Z A),
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
apply hott4cat.isSet_forall.
intros i.
now destruct (f_map_obj H B).
Qed.

Theorem functor_SetC_C_Set2_id_prop {C} (X : Obj (SetC_C C)) :
  functor_SetC_C_Set2_map_hom X X (idc X) = idc (functor_SetC_C_Set2_map_obj X).
Proof.
apply fun_ext; intros η; cbn.
destruct η as (η, Hη); cbn in *.
unfold functor_SetC_C_Set2_map_hom; cbn.
apply eq_existT_uncurried; cbn.
assert (p : (λ (A : Obj C) (g : Hom (snd X) A), η A (g ◦ idc (snd X))) = η). {
  apply fun_ext; intros A.
  apply fun_ext; intros f.
  now rewrite unit_l.
}
exists p; cbn.
apply fun_ext; intros Y.
apply fun_ext; intros Z.
apply fun_ext; intros f.
apply hott4cat.isSet_forall.
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
      → natural_transformation (cov_hom_functor (snd p)) (fst p)) := F
  in
  λ T : st_type (f_map_obj F A),
  let ϑ := λ (X : Obj C) (f : Hom A X), f_map_hom F f T in
  existT _ ϑ
    (λ (X Y : Obj C) (f : Hom X Y),
     fun_ext _
       (λ _ : Hom A X, st_type (f_map_obj F Y)) (λ HA : Hom A X, ϑ Y (f ◦ HA))
       (λ HA : Hom A X, f_map_hom F f (ϑ X HA))
       (λ g : Hom A X,
        eq_ind_r
          (λ h : Hom (f_map_obj F A) (f_map_obj F Y),
           h T = f_map_hom F f (f_map_hom F g T))
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
   (λ (X : Obj C) (f1 : Hom B X),
    f_map_hom G f1 (let (f2, g) := η in (projT1 f2) B (f_map_hom F g T))) =
   (λ (A : Obj C) (g : Hom B A),
    projT1 (fst η) A (f_map_hom F (g ◦ snd η) T))). {
  apply fun_ext; intros X.
  apply fun_ext; intros f.
  destruct η as (η, g); cbn in *.
  destruct η as (η, Hη); cbn.
  rewrite f_comp_prop; cbn.
  specialize (Hη B X f) as H1; cbn in H1.
  specialize (@hott4cat.happly _ _ _ _ H1) as H2; cbn in H2.
  symmetry; apply H2.
}
exists p.
cbn.
apply fun_ext; intros X.
apply fun_ext; intros Y.
apply fun_ext; intros g.
apply hott4cat.isSet_forall.
intros h.
now destruct (f_map_obj G Y).
Qed.

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

(* adjunction *)

Definition adjunction {C D} (L : functor C D) (R : functor D C)
    (η : natural_transformation (¹ C) (R ◦ L))
    (ε : natural_transformation (L ◦ R) (¹ D)) :=
  (right_whiskering R ε ◦ left_whiskering η R = nat_transf_id R)%NT ∧
  (left_whiskering ε L ◦ right_whiskering L η = nat_transf_id L)%NT.

Definition is_left_adjoint {C D} (L : functor C D) :=
  ∃ R η ε, adjunction L R η ε.

Definition is_right_adjoint {C D} (R : functor D C) :=
  ∃ L η ε, adjunction L R η ε.

Definition are_adjoint {C D} (L : functor C D) (R : functor D C) :=
  ∃ η ε, adjunction L R η ε.

Notation "L ⊣ R" := (are_adjoint L R) (at level 70).

(*
   Other definition of adjunction.

   An adjunction between categories C and D is a pair of functors
   (assumed to be covariant)
      R : D → C and L : C → D
   and, for all objects X in C and Y in D a bijection between
   the respective morphism sets
      Hom_C (R Y, X) ≅ Hom_D (Y, L X)
   such that this family of bijections is natural in X and Y.
   (Wikipedia)
*)

Check @hom_functor.
...

(* doubtful new implementation

Definition adjunction2 {C D} (L : functor C D) (R : functor D C) :=
  ∃ (F : functor C D) (G : functor D C)
     (p : ∀ X, f_map_obj G (f_map_obj F X) = X)
     (q : ∀ Y, f_map_obj F (f_map_obj G Y) = Y),
  (∀ X Y (f : Hom (f_map_obj R Y) X),
   f_map_hom G (f_map_hom F f) = transport2 p _ _ f) ∧
  (∀ X Y (g : Hom Y (f_map_obj L X)),
   f_map_hom F (f_map_hom G g) = transport2 q _ _ g).

*)

(*
   (not sure this implementation is good)
*)

Definition adjunction2 {C D} (L : functor C D) (R : functor D C) :=
  ∀ X Y,
  (∃ f : Hom (f_map_obj R Y) X → Hom Y (f_map_obj L X),
   ∃ g : Hom Y (f_map_obj L X) → Hom (f_map_obj R Y) X,
   (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)) ∧
  (∀ (η :
       natural_transformation
         (hom_functor (f_map_obj R Y) X ◦ (fop R × ¹ C))%Fun
         (hom_functor Y (f_map_obj L X) ◦ (¹ op D × L))%Fun),
   is_natural_isomorphism η).

Definition are_adjoint2 {C D} (L : functor C D) (R : functor D C) :=
  adjunction2 L R.

(* cone image by a functor *)

Definition cone_image_fam {J C D} {X : functor J C} {cn : cone X}
    (F : functor C D) (j : Obj J) :
    Hom (f_map_obj F (cn_top cn)) (f_map_obj (F ◦ X) j) :=
  f_map_hom F (cn_fam cn j).

Theorem cone_image_commute {J C D} {X : functor J C} (F : functor C D)
    {cn : cone X} (i j : Obj J) (f : Hom i j) :
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
  (λ J C (X_ : functor J C) (Y : Obj C) (c : cone X_) (p : is_limit c),
   hom_functor Y (cn_top c)).
(* → functor (op C × C) SetCat *)
(* ... to? *)
Check
  (λ J C (X_ : functor J C) (Y : Obj C),
   (cov_hom_functor Y ◦ X_)%Fun).
(* → functor J SetCat *)

(* functors not of the same type! *)

Check @is_natural_isomorphism.

Theorem hom_functor_preserves_limit {C} :
  ∀ J (X_ : functor J C) (lim_i_Xi : cone X_),
  is_limit lim_i_Xi →
  ∀ (Y : Obj C) lim_i_Hom_C_Y_Xi,
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

Theorem hom_functor_preserves_limit {C} (A B : Obj C)
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

Theorem lim_hom_fun {J C D} (E : functor J C) (F : functor C D) (X : Obj C) (j : Obj J) (cn : cone E) :
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
apply hott4cat.isSet_forall.
intros a.
apply fs_is_set.
Qed.

Definition FinSetCat :=
  {| Obj := FinSet_type;
     Hom A B := fs_type A → fs_type B;
     comp A B C f g x := g (f x);
     idc _ A := A;
     unit_l _ _ _ := eq_refl;
     unit_r _ _ _ := eq_refl;
     assoc _ _ _ _ _ _ _ := eq_refl;
     Hom_set := FinSet_Hom_set |}.

(* category 1 *)

Theorem Cat_1_unit (A B : unit) (f : unit → unit) : (λ x : unit, x) = f.
Proof.
apply fun_ext; intros x.
now destruct x, (f tt).
Defined.

Theorem Cat_1_Hom_set (a b : unit) : isSet (unit → unit).
Proof.
apply hott4cat.isSet_forall; intros x.
apply hott4cat.isProp_isSet; intros y z.
now destruct y, z.
Qed.

Definition Cat_1 :=
  {| Obj := unit;
     Hom _ _ := unit → unit;
     comp _ _ _ _ _ := λ x, x;
     idc _ x := x;
     unit_l := Cat_1_unit;
     unit_r := Cat_1_unit;
     assoc _ _ _ _ _ _ _ := eq_refl;
     Hom_set := Cat_1_Hom_set |}.

(* category 2 *)

Definition Cat_2_Hom A B : Type :=
  if (A && negb B)%bool then False else True.

Definition Cat_2_comp {a b c} (f : Cat_2_Hom a b) (g : Cat_2_Hom b c) :
  Cat_2_Hom a c.
Proof.
now destruct a, b.
Defined.

Definition Cat_2_id a : Cat_2_Hom a a.
Proof.
now destruct a.
Defined.

Theorem Cat_2_unit_l a b (f : Cat_2_Hom a b) : Cat_2_comp (Cat_2_id a) f = f.
Proof.
now destruct a.
Defined.

Theorem Cat_2_unit_r a b (f : Cat_2_Hom a b) : Cat_2_comp f (Cat_2_id b) = f.
Proof.
now destruct a, b, f.
Defined.

Theorem Cat_2_assoc a b c d (f : Cat_2_Hom a b) (g : Cat_2_Hom b c)
  (h : Cat_2_Hom c d) :
  Cat_2_comp f (Cat_2_comp g h) = Cat_2_comp (Cat_2_comp f g) h.
Proof.
now destruct a, b, c; cbn in *.
Defined.

Theorem Cat_2_Hom_set a b : isSet (Cat_2_Hom a b).
Proof.
unfold Cat_2_Hom.
destruct (a && negb b)%bool.
-apply hott4cat.isSet_False.
-apply hott4cat.isSet_True.
Defined.

Definition Cat_2 :=
  {| Obj := bool;
     Hom := Cat_2_Hom;
     comp _ _ _ := Cat_2_comp;
     idc := Cat_2_id;
     unit_l := Cat_2_unit_l;
     unit_r := Cat_2_unit_r;
     assoc := Cat_2_assoc;
     Hom_set := Cat_2_Hom_set |}.

(* category 3 *)

Inductive Cat_3_type := C1 | C2 | C3.

Definition Cat_3_Hom A B : Type :=
  match A with
  | C1 => True
  | C2 =>
      match B with
      | C1 => False
      | _ => True
      end
  | C3 =>
      match B with
      | C3 => True
      | _ => False
      end
  end.

Definition Cat_3_comp {a b c} (f : Cat_3_Hom a b) (g : Cat_3_Hom b c) :
  Cat_3_Hom a c.
Proof.
now destruct a, b, c.
Defined.

Definition Cat_3_id a : Cat_3_Hom a a.
Proof.
now destruct a.
Defined.

Theorem Cat_3_unit_l A B (f : Cat_3_Hom A B) :
  Cat_3_comp (Cat_3_id A) f = f.
Proof.
now destruct A, B.
Defined.

Theorem Cat_3_unit_r A B (f : Cat_3_Hom A B) :
  Cat_3_comp f (Cat_3_id B) = f.
Proof.
now destruct A, B, f; cbn.
Defined.

Theorem Cat_3_assoc A B C D (f : Cat_3_Hom A B) (g : Cat_3_Hom B C)
  (h : Cat_3_Hom C D) :
  Cat_3_comp f (Cat_3_comp g h) = Cat_3_comp (Cat_3_comp f g) h.
Proof.
now destruct A, B, C, D, g, h.
Defined.

Theorem Cat_3_Hom_set A B : isSet (Cat_3_Hom A B).
Proof.
destruct A; [ apply hott4cat.isSet_True | | ].
-destruct B; [ apply hott4cat.isSet_False | | ]; apply hott4cat.isSet_True.
-destruct B; [ | | apply hott4cat.isSet_True ]; apply hott4cat.isSet_False.
Defined.

Definition Cat_3 :=
  {| Obj := Cat_3_type;
     Hom := Cat_3_Hom;
     comp _ _ _ := Cat_3_comp;
     idc := Cat_3_id;
     unit_l := Cat_3_unit_l;
     unit_r := Cat_3_unit_r;
     assoc := Cat_3_assoc;
     Hom_set := Cat_3_Hom_set |}.

(* category 0 *)

Definition Cat_0 :=
  {| Obj := False;
     Hom _ _ := False;
     comp _ _ _ f _ := f;
     idc x := x;
     unit_l A := match A with end;
     unit_r A := match A with end;
     assoc A _ _ _ _ := match A with end;
     Hom_set A := match A with end |}.

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
apply hott4cat.is_set_is_set_sigT. {
  intros f.
  unfold is_monotone.
  intros g h.
  apply fun_ext; intros a.
  apply fun_ext; intros a'.
  apply fun_ext; intros p.
  apply ps_prop.
}
apply hott4cat.isSet_forall.
intros a.
unfold ps_stype; cbn.
apply st_is_set.
Defined.

Definition PosCat :=
  {| Obj := Pos_type;
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
apply hott4cat.isSet_forall; intros a.
apply hott4cat.isSet_forall; intros b.
apply proof_irrel.
Defined.

Definition RelCat :=
  {| Obj := Set_type;
     Hom := Rel_Hom;
     comp _ _ _ := Rel_comp;
     idc := Rel_id;
     unit_l := Rel_unit_l;
     unit_r := Rel_unit_r;
     assoc _ _ _ _ := Rel_assoc;
     Hom_set := Rel_Hom_set |}.
