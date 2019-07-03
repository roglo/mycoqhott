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
    f_map_hom {a b} : Hom a b → Hom (f_map_obj a) (f_map_obj b);
    f_comp_prop {a b c} (f : Hom a b) (g : Hom b c) :
      f_map_hom (g ◦ f) = f_map_hom g ◦ f_map_hom f;
    f_id_prop {a} : @f_map_hom a _ hid = hid }.

Arguments f_map_obj [_] [_] _.
Arguments f_map_hom [_] [_] _ [_] [_].

Definition fop {C D} : functor C D → functor (op C) (op D) :=
  λ F,
  {| f_map_obj (x : Obj (op C)) := (@f_map_obj C D F x : Obj (op D));
     f_map_hom _ _ f := f_map_hom F f;
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

Record Cone_Hom {J C} {D : functor J C} (cn cn' : cone D) :=
  { cnh_hom : Hom (cn_top cn) (cn_top cn');
    cnh_commute : ∀ j, cn_fam cn j = cn_fam cn' j ◦ cnh_hom }.

Record CoCone_Hom {J C} {D : functor J C} (cc cc' : co_cone D) :=
  { cch_hom : Hom (cc_top cc) (cc_top cc');
    cch_commute : ∀ j, cc_fam cc' j = cch_hom ◦ cc_fam cc j }.

Arguments cnh_hom [_] [_] [_] [_] [_].
Arguments cch_hom [_] [_] [_] [_] [_].

Definition pair_dep_of_Cone_Hom {J C} {D : functor J C} {cn cn' : cone D} :
  Cone_Hom cn cn' → {u & ∀ j : Obj J, cn_fam cn j = cn_fam cn' j ◦ u} :=
  λ f, existT _ (cnh_hom f) (cnh_commute cn cn' f).

(*
Definition pair_dep_of_Cone_Hom {J C} {D : functor J C} {cn cn' : cone D} :
  Cone_Hom cn cn'
  → {u : Hom (cn_top cn) (cn_top cn') & ∀ j : Obj J, cn_fam cn j = cn_fam cn' j ◦ u}
  :=
  λ f, existT _ (cnh_hom f) (cnh_commute cn cn' f).
  existT (λ u : Hom (cn_top cn) (cn_top cn'), ∀ j : Obj J, cn_fam cn j = cn_fam cn' j ◦ u)
     (cnh_hom f) (cnh_commute cn cn' f).
*)

(*
Theorem eq_pair_dep_eq_Cone_Hom {J C} {D : functor J C}
     (cn cn' : cone D) :
  let P := λ u, ∀ j : Obj J, cn_fam cn j = cn_fam cn' j ◦ u in
  ∀ (f g : Hom (cn_top cn) (cn_top cn')) (fc : P f) (gc : P g),
   existT P f fc = existT P g gc
   → {| cnh_hom := f; cnh_commute := fc |} =
      {| cnh_hom := g; cnh_commute := gc |}.
Proof.
intros * H.
injection H; intros H1.
destruct H1.
apply f_equal, extensionality.
intros j.
apply Hom_set.
Defined.

Theorem eq_pair_dep_eq_CoCone_Hom {J C} {D : functor J C}
     (cc cc' : co_cone D) :
  let P := λ u, ∀ j : Obj J, cc_fam cc' j = u ◦ cc_fam cc j in
  ∀ (f g : Hom (cc_top cc) (cc_top cc')) (fc : P f) (gc : P g),
   existT P f fc = existT P g gc
   → {| cch_hom := f; cch_commute := fc |} =
      {| cch_hom := g; cch_commute := gc |}.
Proof.
intros * H.
injection H; intros H1.
destruct H1.
apply f_equal, extensionality.
intros j.
apply Hom_set.
Defined.
*)

Definition Cone_comp {J C} {D : functor J C} (c c' c'' : cone D)
  (f : Cone_Hom c c') (g : Cone_Hom c' c'') : Cone_Hom c c''.
Proof.
remember (cnh_hom g ◦ cnh_hom f) as h eqn:Hh.
assert (Hcom : ∀ j, cn_fam c j = cn_fam c'' j ◦ h). {
  intros.
  rewrite Hh.
  etransitivity; [ apply (cnh_commute _ _ f) | ].
  etransitivity; [ | apply assoc ].
  apply f_equal, cnh_commute.
}
apply {| cnh_hom := h; cnh_commute := Hcom |}.
Defined.

Definition CoCone_comp {J C} {D : functor J C} (c c' c'' : co_cone D)
  (f : CoCone_Hom c c') (g : CoCone_Hom c' c'') : CoCone_Hom c c''.
Proof.
remember (cch_hom g ◦ cch_hom f) as h eqn:Hh.
assert (Hcom : ∀ j, cc_fam c'' j = h ◦ cc_fam c j). {
  intros.
  rewrite Hh.
  etransitivity; [ apply (cch_commute _ _ g) | ].
  etransitivity; [ | symmetry; apply assoc ].
  f_equal; apply cch_commute.
}
apply {| cch_hom := h; cch_commute := Hcom |}.
Defined.

Definition Cone_id {J C} {D : functor J C} (cn : cone D) :
    Cone_Hom cn cn :=
  {| cnh_hom := hid;
     cnh_commute j := eq_sym (unit_l (cn_fam cn j)) |}.

Definition CoCone_id {J C} {D : functor J C} (cc : co_cone D) :
    CoCone_Hom cc cc :=
  {| cch_hom := hid;
     cch_commute j := eq_sym (unit_r (cc_fam cc j)) |}.

Theorem Cone_unit_l {J C} {D : functor J C} :
  ∀ (c c' : cone D) (f : Cone_Hom c c'),
  Cone_comp c c c' (Cone_id c) f = f.
Proof.
intros.
remember (pair_dep_of_Cone_Hom f) as p.
...
intros.
unfold Cone_comp; cbn.
destruct f as (f & Hf); cbn.
apply eq_pair_dep_eq_Cone_Hom.
apply eq_existT_uncurried.
exists (unit_l _).
apply extensionality.
intros j; apply Hom_set.
Defined.

Theorem CoCone_unit_l {J C} {D : functor J C} :
  ∀ (c c' : co_cone D) (f : CoCone_Hom c c'),
  CoCone_comp c c c' (CoCone_id c) f = f.
Proof.
intros.
unfold CoCone_comp; cbn.
destruct f as (f & Hf); cbn.
apply eq_pair_dep_eq_CoCone_Hom.
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
apply eq_pair_dep_eq_Cone_Hom.
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
apply eq_pair_dep_eq_CoCone_Hom.
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
apply eq_pair_dep_eq_Cone_Hom.
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
apply eq_pair_dep_eq_CoCone_Hom.
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
intros f g p q.
Check eq_pair_dep_eq_Cone_Hom.
Check hott4cat.is_set_is_set_sigT.
destruct f, g.
...
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

(* another definition of category of co-cones *)

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
     f_map_hom _ _ f := f;
     f_comp_prop _ _ _ := F_CoCone_CoCone2_comp_prop;
     f_id_prop _ := eq_refl |}.

Definition F_CoCone2_CoCone {J C} {D : functor J C} :
    functor (CoCone2 D) (CoCone D) :=
  {| f_map_obj := co_cone_of_cone_fop : Obj (CoCone2 D) → Obj (CoCone D);
     f_map_hom _ _ f := f;
     f_comp_prop _ _ _ := F_CoCone2_CoCone_comp_prop;
     f_id_prop _ := eq_refl |}.

Theorem F_CoCone_CoCone2_id {J C} {D : functor J C} :
  ∀ cc, f_map_obj F_CoCone2_CoCone (f_map_obj F_CoCone_CoCone2 cc) = cc.
Proof. now intros; destruct cc. Defined.

Theorem F_CoCone2_CoCone_id {J C} {D : functor J C} :
  ∀ cc, f_map_obj F_CoCone_CoCone2 (f_map_obj F_CoCone2_CoCone cc) = cc.
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

Theorem CoCone_CoCone2_iso J C {D : functor J C} :
  are_isomorphic_categories (CoCone D) (CoCone2 D).
Proof.
exists F_CoCone_CoCone2.
exists F_CoCone2_CoCone.
exists F_CoCone_CoCone2_id.
exists F_CoCone2_CoCone_id.
split.
-now intros; destruct x, y.
-now intros; destruct x, y.
Qed.

(* natural transformation *)

Definition nat_transf {C D} (F G : functor C D) :=
  { ϑ : ∀ x, Hom (f_map_obj F x) (f_map_obj G x) &
    ∀ x y (f : Hom x y), ϑ y ◦ f_map_hom F f = f_map_hom G f ◦ ϑ x }.

Definition nt_hom {C D} {F G : functor C D} (η : nat_transf F G) :=
  projT1 η.
Definition nt_commute {C D} {F G : functor C D} (η : nat_transf F G) :=
  projT2 η.

(* category of functors *)

Theorem Fun_comp_nt_commute {C D} {F G H : functor C D} :
  ∀ (η : nat_transf F G) (η' : nat_transf G H),
  ∀ (x y : Obj C) (f : Hom x y),
  nt_hom η' y ◦ nt_hom η y ◦ f_map_hom F f =
  f_map_hom H f ◦ (nt_hom η' x ◦ nt_hom η x).
Proof.
intros.
rewrite assoc, (nt_commute η).
do 2 rewrite <- assoc.
apply f_equal, (nt_commute η').
Defined.

Definition Fun_comp {C D} (F G H : functor C D) :
    nat_transf F G → nat_transf G H → nat_transf F H :=
  λ η η',
  existT _ (λ x, nt_hom η' x ◦ nt_hom η x) (Fun_comp_nt_commute η η').

Definition Fun_id {C D} (F : functor C D) : nat_transf F F.
Proof.
Print functor.
unfold nat_transf.
exists (f_map_hom F).
...

Definition Fun C D :=
  {| Obj := functor C D;
     Hom := nat_transf;
     comp := Fun_comp;
     hid F := 42 |}.
