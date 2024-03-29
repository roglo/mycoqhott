(* miscellaneous categories *)

Set Universe Polymorphism.
Set Nested Proofs Allowed.

Require Import Utf8.
Require Import category.
Require areSet.

(* category 0 *)

Definition Cat_0 :=
  {| Ob := False;
     Hom _ _ := False;
     comp _ _ _ f _ := f;
     idc x := x;
     unit_l A := match A with end;
     unit_r A := match A with end;
     assoc A _ _ _ _ := match A with end;
     Hom_set A := match A with end |}.

(* category 1 *)

Theorem Cat_1_unit (A B : unit) (f : unit → unit) : (λ x : unit, x) = f.
Proof.
apply fun_ext; intros x.
now destruct x, (f tt).
Defined.

Theorem Cat_1_Hom_set (a b : unit) : isSet (unit → unit).
Proof.
apply h4c.isSet_forall; intros x.
apply h4c.isProp_isSet; intros y z.
now destruct y, z.
Qed.

Definition Cat_1 :=
  {| Ob := unit;
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
-apply h4c.isSet_False.
-apply h4c.isSet_True.
Defined.

Definition Cat_2 :=
  {| Ob := bool;
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
destruct A; [ apply h4c.isSet_True | | ].
-destruct B; [ apply h4c.isSet_False | | ]; apply h4c.isSet_True.
-destruct B; [ | | apply h4c.isSet_True ]; apply h4c.isSet_False.
Defined.

Definition Cat_3 :=
  {| Ob := Cat_3_type;
     Hom := Cat_3_Hom;
     comp _ _ _ := Cat_3_comp;
     idc := Cat_3_id;
     unit_l := Cat_3_unit_l;
     unit_r := Cat_3_unit_r;
     assoc := Cat_3_assoc;
     Hom_set := Cat_3_Hom_set |}.

(* The arrow category C→ of a category C has the arrows of C as objects,
   and an arrow g from f : A → B to f' : A' → B' in C→ is a “commutative
   square”
           g₁
        A ---> A'
        |      |
      f |      | f'
        |      |
        v      v
        B ---> B'
           g₂

   where g1 and g2 are arrows in C. That is, such an arrow is a pair of
   arrows g = (g1, g2) in C such that
       g2 ◦ f = f' ◦ g1.

   (Awodey)
*)

Definition Arr_Ob C := { A : Ob C & { B : Ob C & Hom A B } }.
Definition AC_A {C} (X : Arr_Ob C) := projT1 X.
Definition AC_B {C} (X : Arr_Ob C) := projT1 (projT2 X).
Definition AC_Hom {C} (X : Arr_Ob C) := projT2 (projT2 X).

Definition Arr_Hom {C} (X X' : Arr_Ob C) :=
  { g1g2 & snd g1g2 ◦ AC_Hom X = AC_Hom X' ◦ fst g1g2 }.

Definition AC_Hom_g1 {C} {X X' : Arr_Ob C} (f : Arr_Hom X X') :=
  fst (projT1 f).
Definition AC_Hom_g2 {C} {X X' : Arr_Ob C} (f : Arr_Hom X X') :=
  snd (projT1 f).
Definition AC_Hom_prop {C} {X X' : Arr_Ob C} (f : Arr_Hom X X') :=
  projT2 f.

Definition Arr_comp {C} {X Y Z : Arr_Ob C}
  (f : Arr_Hom X Y) (g : Arr_Hom Y Z) : Arr_Hom X Z.
Proof.
unfold Arr_Hom.
exists (AC_Hom_g1 g ◦ AC_Hom_g1 f, AC_Hom_g2 g ◦ AC_Hom_g2 f).
unfold AC_Hom_g2, AC_Hom_g1; cbn.
symmetry.
etransitivity; [ symmetry; apply assoc | ].
etransitivity; [ apply f_equal; symmetry; apply (AC_Hom_prop g) | ].
etransitivity; [ apply assoc | symmetry ].
etransitivity; [ apply assoc | ].
now rewrite (AC_Hom_prop f).
Defined.

Definition Arr_id {C} (X : Arr_Ob C) : Arr_Hom X X.
Proof.
exists (idc _, idc _).
etransitivity; [ apply unit_r | ].
symmetry; apply unit_l.
Defined.

Theorem Arr_unit_l {C} {X Y : Arr_Ob C} (f : Arr_Hom X Y) :
  Arr_comp (Arr_id X) f = f.
Proof.
destruct f as ((g1, g2) & Hgg); cbn in Hgg.
unfold Arr_comp; cbn.
apply eq_existT_uncurried.
assert (p : (g1 ◦ idc (AC_A X), g2 ◦ idc (AC_B X)) = (g1, g2)). {
  now do 2 rewrite unit_l.
}
exists p.
apply Hom_set.
Defined.

Theorem Arr_unit_r {C} {X Y : Arr_Ob C} (f : Arr_Hom X Y) :
  Arr_comp f (Arr_id Y) = f.
Proof.
destruct f as ((g1, g2) & Hgg); cbn in Hgg.
unfold Arr_comp; cbn.
apply eq_existT_uncurried.
assert (p : (idc (AC_A Y) ◦ g1, idc (AC_B Y) ◦ g2) = (g1, g2)). {
  now do 2 rewrite unit_r.
}
exists p.
apply Hom_set.
Defined.

Theorem Arr_assoc {C} {X Y Z T : Arr_Ob C} (f : Arr_Hom X Y)
  (g : Arr_Hom Y Z) (h : Arr_Hom Z T) :
  Arr_comp f (Arr_comp g h) = Arr_comp (Arr_comp f g) h.
Proof.
unfold Arr_comp at 1 3.
apply eq_existT_uncurried.
assert (p
  : (AC_Hom_g1 (Arr_comp g h) ◦ AC_Hom_g1 f,
     AC_Hom_g2 (Arr_comp g h) ◦ AC_Hom_g2 f) =
    (AC_Hom_g1 h ◦ AC_Hom_g1 (Arr_comp f g),
     AC_Hom_g2 h ◦ AC_Hom_g2 (Arr_comp f g))). {
  now cbn; do 2 rewrite assoc.
}
exists p.
apply Hom_set.
Qed.

Theorem Arr_Hom_set {C} (X Y : Arr_Ob C) :
  isSet (Arr_Hom X Y).
Proof.
unfold Arr_Hom.
apply h4c.isSet_isSet_sigT. 2: {
  apply h4c.isSet_pair; apply Hom_set.
}
intros (f, g); cbn.
unfold h4c.isProp.
apply Hom_set.
Defined.

Definition ArrCat C :=
  {| Ob := Arr_Ob C;
     Hom := Arr_Hom;
     comp _ _ _ := Arr_comp;
     idc := Arr_id;
     unit_l _ _ := Arr_unit_l;
     unit_r _ _ := Arr_unit_r;
     assoc _ _ _ _ := Arr_assoc;
     Hom_set := Arr_Hom_set |}.

(* The slice category 𝒞/C of a category 𝒞 over an object C ∈ 𝒞 has:
    • objects: all arrows f ∈ 𝒞 such that cod(f)=C,
    • arrows: g from f : X → C to f′ : X′ → C is an arrow g : X → X′ in 𝒞
      such that f′ ◦ g = f, as indicated in
                 g
            X ------> X'
             \       /
            f \     / f'
               ↘ ↙
                 C
   (Awodey)
 *)

Definition Slice_Ob {C} (B : Ob C) := { A & Hom A B }.
Definition SC_arr {C} {B : Ob C} (f : Slice_Ob B) := projT2 f.

Definition Slice_Hom {C} {B : Ob C} (f f' : Slice_Ob B) :=
  { g & SC_arr f' ◦ g = SC_arr f }.
Definition SC_hom {C} {B : Ob C} {f f' : Slice_Ob B}
  (g : Slice_Hom f f') := projT1 g.
Definition SC_prop {C} {B : Ob C} {f f' : Slice_Ob B}
  (g : Slice_Hom f f') := projT2 g.

Definition Slice_comp {C} {B : Ob C} {f f' f'' : Slice_Ob B}
  (g : Slice_Hom f f') (g' : Slice_Hom f' f'') : Slice_Hom f f''.
Proof.
exists (SC_hom g' ◦ SC_hom g).
rewrite <- assoc.
unfold SC_hom; rewrite SC_prop; apply SC_prop.
Defined.

Definition Slice_id {C} {B : Ob C} (f : Slice_Ob B) : Slice_Hom f f.
Proof.
exists (idc _).
apply unit_l.
Defined.

Theorem Slice_unit_l {C} {B : Ob C} {f f' : Slice_Ob B}
  (g : Slice_Hom f f') : Slice_comp (Slice_id f) g = g.
Proof.
destruct g as (g & Hg).
unfold Slice_comp; cbn.
apply eq_existT_uncurried.
exists (unit_l _).
apply Hom_set.
Defined.

Theorem Slice_unit_r {C} {B : Ob C} {f f' : Slice_Ob B}
  (g : Slice_Hom f f') : Slice_comp g (Slice_id f') = g.
Proof.
destruct g as (g & Hg).
unfold Slice_comp; cbn.
apply eq_existT_uncurried.
exists (unit_r _).
apply Hom_set.
Defined.

Theorem Slice_assoc {C} {B : Ob C} {f f' f'' f''' : Slice_Ob B}
  (g : Slice_Hom f f') (h : Slice_Hom f' f'')
  (i : Slice_Hom f'' f''') :
  Slice_comp g (Slice_comp h i) = Slice_comp (Slice_comp g h) i.
Proof.
unfold Slice_comp at 1 3.
apply eq_existT_uncurried.
exists (assoc _ _ _).
apply Hom_set.
Defined.

Theorem Slice_Hom_set {C} {B : Ob C} (f f' : Slice_Ob B) :
  isSet (Slice_Hom f f').
Proof.
unfold Slice_Hom.
apply h4c.isSet_isSet_sigT; [ | apply Hom_set ].
intros g.
unfold h4c.isProp.
apply Hom_set.
Defined.

Definition SliceCat {C} (B : Ob C) :=
  {| Ob := Slice_Ob B;
     Hom := Slice_Hom;
     comp _ _ _ := Slice_comp;
     idc := Slice_id;
     unit_l _ _ := Slice_unit_l;
     unit_r _ _ := Slice_unit_r;
     assoc _ _ _ _ := Slice_assoc;
     Hom_set := Slice_Hom_set |}.

(* coslice category *)

(* The coslice category 𝒞/C of a category 𝒞 under an object C of 𝒞 has
   as objects all arrows f of 𝒞 such that dom(f)=C, and an arrow from
   f : C → X to f′ : C → X′ is an arrow h : X → X′ such that h ◦ f= f′.
   (Awodey)
 *)

Definition Coslice_Ob {C} (A : Ob C) := { B & Hom A B }.
Definition CC_arr {C} {A : Ob C} (f : Coslice_Ob A) := projT2 f.

Definition Coslice_Hom {C} {A : Ob C} (f f' : Coslice_Ob A) :=
  { h & h ◦ CC_arr f = CC_arr f' }.
Definition CC_hom {C} {B : Ob C} {f f' : Coslice_Ob B}
  (g : Coslice_Hom f f') := projT1 g.
Definition CC_prop {C} {B : Ob C} {f f' : Coslice_Ob B}
  (g : Coslice_Hom f f') := projT2 g.

Definition Coslice_comp {C} {A : Ob C} {f f' f'' : Coslice_Ob A}
  (g : Coslice_Hom f f') (g' : Coslice_Hom f' f'') : Coslice_Hom f f''.
Proof.
exists (CC_hom g' ◦ CC_hom g).
rewrite assoc.
unfold CC_hom; rewrite CC_prop; apply CC_prop.
Defined.

Definition Coslice_id {C} {A : Ob C} (f : Coslice_Ob A) : Coslice_Hom f f.
Proof.
exists (idc _).
apply unit_r.
Defined.

Theorem Coslice_unit_l {C} {A : Ob C} {f f' : Coslice_Ob A}
  (g : Coslice_Hom f f') : Coslice_comp (Coslice_id f) g = g.
Proof.
destruct g as (g & Hg).
unfold Coslice_comp; cbn.
apply eq_existT_uncurried.
exists (unit_l _).
apply Hom_set.
Defined.

Theorem Coslice_unit_r {C} {A : Ob C} {f f' : Coslice_Ob A}
  (g : Coslice_Hom f f') : Coslice_comp g (Coslice_id f') = g.
Proof.
destruct g as (g & Hg).
unfold Coslice_comp; cbn.
apply eq_existT_uncurried.
exists (unit_r _).
apply Hom_set.
Defined.

Theorem Coslice_assoc {C} {A : Ob C} {f f' f'' f''' : Coslice_Ob A}
  (g : Coslice_Hom f f') (h : Coslice_Hom f' f'')
  (i : Coslice_Hom f'' f''') :
  Coslice_comp g (Coslice_comp h i) = Coslice_comp (Coslice_comp g h) i.
Proof.
unfold Coslice_comp at 1 3.
apply eq_existT_uncurried.
exists (assoc _ _ _).
apply Hom_set.
Defined.

Theorem Coslice_Hom_set {C} {A : Ob C} (f f' : Coslice_Ob A) :
  isSet (Coslice_Hom f f').
Proof.
unfold Coslice_Hom.
apply h4c.isSet_isSet_sigT; [ | apply Hom_set ].
intros g.
unfold h4c.isProp.
apply Hom_set.
Defined.

Definition CosliceCat {C} (A : Ob C) :=
  {| Ob := Coslice_Ob A;
     Hom := Coslice_Hom;
     comp _ _ _ := Coslice_comp;
     idc := Coslice_id;
     unit_l _ _ := Coslice_unit_l;
     unit_r _ _ := Coslice_unit_r;
     assoc _ _ _ _ := Coslice_assoc;
     Hom_set := Coslice_Hom_set |}.

(* Coslice C A is equivalent to (Slice C^op A)^op *)
(* I guess they should be equal, but I cannot prove it *)

Theorem coslice_slice_comp_prop {C} {A : Ob C} {X Y Z : Ob (CosliceCat A)}
        (f : Hom X Y) (g : Hom Y Z) :
  id (g ◦ f) = @comp (@SliceCat C⁰ A)⁰ _ _ _ (id f) (id g).
Proof.
apply eq_existT_uncurried.
exists eq_refl; cbn.
apply Hom_set.
Defined.

Theorem slice_coslice_comp_prop {C} {A : Ob C}
  {X Y Z : Ob (op (@SliceCat (op C) A))}
  (f : @Hom (op (@SliceCat (op C) A)) X Y)
  (g : @Hom (op (@SliceCat (op C) A)) Y Z) :
  id (@comp (op (@SliceCat (op C) A)) X Y Z f g) =
  @comp (CosliceCat A) X Y Z (@id (@Hom (op (@SliceCat (op C) A)) X Y) f)
        (@id (@Hom (op (@SliceCat (op C) A)) Y Z) g).
Proof.
apply eq_existT_uncurried.
exists eq_refl; cbn.
apply Hom_set.
Defined.

Theorem coslice_slice {C} (A : Ob C) :
  are_equivalent_categories (CosliceCat A) (@SliceCat C⁰ A)⁰.
Proof.
unfold are_equivalent_categories.
set
  (F :=
    {| f_obj (X : Ob (CosliceCat A)) :=
         X : Ob (@SliceCat C⁰ A)⁰;
       f_hom X Y (f : @Hom (CosliceCat A) X Y) :=
         id f : @Hom (@SliceCat C⁰ A)⁰ X Y;
       f_comp_prop _ _ _ := coslice_slice_comp_prop;
       f_id_prop _ := eq_refl |} :
   functor (CosliceCat A) (@SliceCat C⁰ A)⁰).
exists F.
unfold is_equiv_betw_cat.
set
  (G :=
    {| f_obj (X : Ob (@SliceCat C⁰ A)⁰) :=
         X : Ob (CosliceCat A);
       f_hom X Y (f : @Hom (@SliceCat C⁰ A)⁰ X Y) :=
         id f : @Hom (CosliceCat A) X Y;
       f_comp_prop _ _ _ := slice_coslice_comp_prop;
       f_id_prop _ := eq_refl |} :
    functor (@SliceCat C⁰ A)⁰ (CosliceCat A)).
exists G.
-unfold F, G; cbn.
 unfold functor_comp; cbn.
 unfold "¹"; cbn.
 unfold id; f_equal.
 apply fun_ext; intros X.
 apply fun_ext; intros Y.
 apply fun_ext; intros Z.
 apply fun_ext; intros f.
 apply fun_ext; intros g.
 apply Hom_set.
-unfold F, G; cbn.
 unfold functor_comp; cbn.
 unfold "¹"; cbn.
 unfold id; f_equal.
 apply fun_ext; intros X.
 apply fun_ext; intros Y.
 apply fun_ext; intros Z.
 apply fun_ext; intros f.
 apply fun_ext; intros g.
 apply Hom_set.
Qed.

(*  The category Sets∗ of pointed sets consists of sets A with a distinguished
    element a ∈ A, and arrows f:(A, a)→(B, b) are functions f:A→B that
    preserves the “points” f(a)=b.
    (Awodey)
 *)

Record SetsStar_Ob := { ss_type : Set_type; ss_elem : st_type ss_type }.

(*
Record SetsStar_Hom A B := mk_ss_hom
  { ss_fun : st_type (ss_type A) → st_type (ss_type B);
    ss_prop : h4c.PT (ss_fun (ss_elem A) = ss_elem B) }.
Arguments ss_fun {_} {_}.
Arguments ss_prop {_} {_}.
Arguments mk_ss_hom {_} {_}.
*)
Definition SetsStar_Hom A B :=
  { f : st_type (ss_type A) → st_type (ss_type B) & f (ss_elem A) = ss_elem B }.
Definition ss_fun {A B} (ss : SetsStar_Hom A B) := projT1 ss.
Definition ss_prop {A B} (ss : SetsStar_Hom A B) := projT2 ss.
Definition mk_ss_hom {A B} ssf ssp : SetsStar_Hom A B := existT _ ssf ssp.
(**)

Theorem SetsStar_comp_prop {A B C} (f : SetsStar_Hom A B)
        (g : SetsStar_Hom B C) :
  ss_fun g (ss_fun f (ss_elem A)) = ss_elem C.
Proof.
etransitivity; [ | apply @ss_prop ].
apply f_equal, ss_prop.
Defined.

Definition SetsStar_comp {A B C} (f : SetsStar_Hom A B)
  (g : SetsStar_Hom B C) : SetsStar_Hom A C
:=
  mk_ss_hom (λ x, ss_fun g (ss_fun f x)) (SetsStar_comp_prop f g).

Definition SetsStar_idc (A : SetsStar_Ob) : SetsStar_Hom A A :=
  mk_ss_hom id eq_refl.

Theorem SetsStar_unit_l {A B : SetsStar_Ob} (f : SetsStar_Hom A B) :
  SetsStar_comp (SetsStar_idc A) f = f.
Proof.
destruct f as (f & Hf); cbn.
unfold SetsStar_comp; cbn.
apply f_equal.
unfold SetsStar_comp_prop; cbn.
now destruct Hf.
Defined.

Theorem SetsStar_unit_r {A B : SetsStar_Ob} (f : SetsStar_Hom A B) :
  SetsStar_comp f (SetsStar_idc B) = f.
Proof.
destruct f as (f & Hf); cbn.
unfold SetsStar_comp; cbn.
apply f_equal.
unfold SetsStar_comp_prop; cbn.
now destruct Hf.
Defined.

Theorem SetsStar_assoc {A B C D : SetsStar_Ob}
  (f : SetsStar_Hom A B) (g : SetsStar_Hom B C) (h : SetsStar_Hom C D) :
  SetsStar_comp f (SetsStar_comp g h) = SetsStar_comp (SetsStar_comp f g) h.
Proof.
unfold SetsStar_comp.
apply f_equal; cbn.
unfold SetsStar_comp_prop; cbn.
unfold eq_trans; cbn.
destruct (ss_prop h); cbn.
unfold f_equal; cbn.
destruct (ss_prop g).
now destruct (ss_prop f).
Defined.

Definition SetsStar_Hom_td A B :=
  { f : st_type (ss_type A) → st_type (ss_type B) &
    f (ss_elem A) = ss_elem B }.

(*
Theorem SetsStar_Hom_of_dep_pair A B : ∀ f g pf pg,
  existT _ f pf = (existT _ g pg : SetsStar_Hom_td A B)
  → {| ss_fun := f; ss_prop := pf |} = {| ss_fun := g; ss_prop := pg |}.
Proof.
...
*)

Theorem SetsStar_Hom_set (A B : SetsStar_Ob) :
  isSet (SetsStar_Hom A B).
Proof.
apply h4c.isSet_isSet_sigT. 2: {
  apply h4c.isSet_forall.
  intros a.
  apply st_is_set.
}
intros f p q.
apply st_is_set.
Defined.

Definition SetsStarCat :=
  {| Ob := SetsStar_Ob;
     Hom := SetsStar_Hom;
     comp _ _ _ := SetsStar_comp;
     idc := SetsStar_idc;
     unit_l _ _ := SetsStar_unit_l;
     unit_r _ _ := SetsStar_unit_r;
     assoc _ _ _ _ := SetsStar_assoc;
     Hom_set := SetsStar_Hom_set |}.

(*
    The category Set* is isomorphic to the coslice category,
        Sets∗ ≅ 1\Sets
    of Sets “under” any singleton 1 ={∗}

    (Awodey)
*)

Definition setsstar_coslice_ob_map_obj {C} (A : Ob C) :
  Ob (CosliceCat A) := existT _ A (idc _).

Definition setsstar_coslice_ob_map_hom {C} (A : Ob C) :
  Hom (setsstar_coslice_ob_map_obj A) (setsstar_coslice_ob_map_obj A) :=
  existT _ (idc A) (unit_l (idc A)).

Theorem setsstar_coslice_ob_comp_prop {C} (A : Ob C)
  {U U' U'' : Ob Cat_1} (f : Hom U U') (g : Hom U' U'') :
  setsstar_coslice_ob_map_hom A =
  setsstar_coslice_ob_map_hom A ◦ setsstar_coslice_ob_map_hom A.
Proof.
apply eq_existT_uncurried; cbn.
exists (eq_sym (unit_l _)).
apply Hom_set.
Defined.

Theorem setsstar_coslice_ob_id_prop {C} (A : Ob C) (X : Ob SetsStarCat) :
  setsstar_coslice_ob_map_hom A = idc (setsstar_coslice_ob_map_obj A).
Proof.
apply eq_existT_uncurried; cbn.
exists eq_refl.
apply Hom_set.
Defined.

Definition setsstar_coslice_ob {C} (A : Ob C) (X : Ob SetsStarCat) :
  Ob (FunCat Cat_1 (CosliceCat A)) :=
  {| f_obj _ := setsstar_coslice_ob_map_obj A;
     f_hom _ _ _ := setsstar_coslice_ob_map_hom A;
     f_comp_prop _ _ _ := setsstar_coslice_ob_comp_prop A;
     f_id_prop _ := setsstar_coslice_ob_id_prop A X |}.

Definition setsstar_coslice_hom {C} (A : Ob C) (X Y : Ob SetsStarCat)
  (f : Hom X Y) :
  Hom (setsstar_coslice_ob A X) (setsstar_coslice_ob A Y).
Proof.
exists (λ _, existT (λ h, h ◦ idc A = idc A) (idc A) (unit_l (idc A))).
intros U U' g; cbn.
apply eq_existT_uncurried; cbn.
exists eq_refl.
apply Hom_set.
Defined.

(*
Definition setsstar_coslice_comop_prop {C} (A : Ob C) (X Y Z : Ob SetsStarCat)
           (f : Hom X Y) (g : Hom Y Z) :
  setsstar_coslice_hom A X Z (g ◦ f) =
  setsstar_coslice_hom A Y Z g ◦ setsstar_coslice_hom A X Y f.
Proof.
cbn in *.
unfold nat_transf_comp.
unfold setsstar_coslice_hom; cbn.
apply eq_existT_uncurried; cbn.
assert (p :
          @eq (forall _ : unit, @Coslice_Hom C A (@setsstar_coslice_ob_obj C A) (@setsstar_coslice_ob_obj C A))
             (fun _ : unit =>
              @existT (@Hom C A A)
                (fun h : @Hom C A A => @eq (@Hom C A A) (@comp C A A A (@idc C A) h) (@idc C A))
                (@idc C A) (@unit_l C A A (@idc C A)))
             (fun _ : unit =>
              @Coslice_comp C A (@setsstar_coslice_ob_obj C A) (@setsstar_coslice_ob_obj C A)
                (@setsstar_coslice_ob_obj C A)
                (@existT (@Hom C A A)
                   (fun h : @Hom C A A => @eq (@Hom C A A) (@comp C A A A (@idc C A) h) (@idc C A))
                   (@idc C A) (@unit_l C A A (@idc C A)))
                (@existT (@Hom C A A)
                   (fun h : @Hom C A A => @eq (@Hom C A A) (@comp C A A A (@idc C A) h) (@idc C A))
                   (@idc C A) (@unit_l C A A (@idc C A))))). {
  apply fun_ext.
  intros _.
  unfold Coslice_comp.
  apply eq_existT_uncurried; cbn.
  assert (p : idc A = idc A ◦ idc A). {
    symmetry; apply unit_l.
  }
  exists p.
  apply Hom_set.
}
exists p; cbn.
apply fun_ext; intros U; destruct U.
apply fun_ext; intros U; destruct U.
apply fun_ext; intros h.
unfold nat_transf_comp_nt_commute; cbn.
(* prise de tête ; je laisse béton *)
Abort.

Theorem setsstar_1_coslice {C} (A : Ob C):
  are_equivalent_categories SetsStarCat (FunCat Cat_1 (CosliceCat A)).
Proof.
unfold are_equivalent_categories.
assert (F : functor SetsStarCat (FunCat Cat_1 (CosliceCat A))). {
  apply
    {| f_obj := setsstar_coslice_ob A;
       f_hom := setsstar_coslice_hom A;
       f_comp_prop X Y Z f g := 42 |}.
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
apply h4c.isSet_isSet_sigT. {
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

(* category of categories *)

Theorem CatCat_comp_prop {C C' C'' : category}
  {F : functor C C'} {G : functor C' C''} :
  ∀ (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
  f_hom G (f_hom F (g ◦ f)) =
  f_hom G (f_hom F g) ◦ f_hom G (f_hom F f).
Proof.
intros.
etransitivity; [ | apply f_comp_prop ].
apply f_equal, f_comp_prop.
Defined.

Theorem CatCat_id_prop {C C' C'' : category}
  {F : functor C C'} {G : functor C' C''} :
  ∀ X : Ob C,
  f_hom G (f_hom F (idc X)) = idc (f_obj G (f_obj F X)).
Proof.
intros.
etransitivity; [ | apply f_id_prop ].
apply f_equal, f_id_prop.
Defined.

Definition CatCat_comp {C C' C'' : category}
  (F : functor C C') (G : functor C' C'') : functor C C'' :=
  {| f_obj X := f_obj G (f_obj F X);
     f_hom X Y f := f_hom G (f_hom F f);
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
   (f_comp_prop (f_hom G (f_hom F f)) (f_hom G (f_hom F g))).
 destruct (f_comp_prop (f_hom F f) (f_hom F g)).
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
apply h4c.eq_existT_pair_transport in H3.
destruct H3 as (Hp3 & H3).
destruct H3.
apply h4c.eq_existT_pair_transport in H2.
destruct H2 as (Hp2 & H2).
destruct H2.
apply h4c.eq_existT_pair_transport in H1.
destruct H1 as (Hp1 & H1).
destruct H1.
move Hp1 after Hp3; move Hp2 after Hp3.
injection p; intros H1 H2 H3.
injection H3.
intros H4.
apply h4c.eq_existT_pair_transport in H4.
destruct H4 as (Hp4 & H4).
move Hp4 before Hp3.
(* doesn't work; but is it true? *)
...

Hom_set does not work: perhaps false or not

Definition CatCat :=
  {| Ob := category;
     Hom := functor;
     comp _ _ := CatCat_comp;
     idc := CatCat_idc;
     unit_l := CatCat_unit_l;
     unit_r := CatCat_unit_r;
     assoc := CatCat_assoc;
     Hom_set := 42 |}.
*)

(* arrow category is equivalent to [2, C] *)

Definition fun_arr_2_C_map_obj_map_obj {C} (X : Ob (ArrCat C)) (b : Ob Cat_2) :
    Ob C := if b then AC_B X else AC_A X.

Definition fun_arr_2_C_map_obj_map_hom {C} (X : Ob (ArrCat C))
    {b1 b2 : Ob Cat_2} (f : Hom b1 b2) :
  Hom (fun_arr_2_C_map_obj_map_obj X b1) (fun_arr_2_C_map_obj_map_obj X b2).
Proof.
intros.
destruct b1.
-destruct b2; [ apply idc | easy ].
-destruct b2; [ now destruct X as (XA & XB & Xf) | apply idc ].
Defined.

Theorem fun_arr_2_C_map_obj_comp_prop {C} (X : Ob (ArrCat C))
        {b1 b2 b3 : Ob Cat_2} (f : Hom b1 b2) (g : Hom b2 b3) :
  fun_arr_2_C_map_obj_map_hom X (g ◦ f) =
  fun_arr_2_C_map_obj_map_hom X g ◦ fun_arr_2_C_map_obj_map_hom X f.
Proof.
destruct X as (XA & XB & Xf); symmetry.
destruct b1, b2, b3; cbn; try easy.
-apply unit_l.
-apply unit_r.
-apply unit_l.
-apply unit_r.
Defined.

Theorem fun_arr_2_C_map_obj_id_prop {C} (X : Ob (ArrCat C)) (b : Ob Cat_2) :
  fun_arr_2_C_map_obj_map_hom X (idc b) = idc (if b then AC_B X else AC_A X).
Proof.
now destruct b.
Defined.

Definition arr_cat_fun_2_C_map_obj {C} (X : Ob (ArrCat C)) :
     Ob (FunCat Cat_2 C)
:=
  {| f_obj := fun_arr_2_C_map_obj_map_obj X;
     f_hom _ _ := fun_arr_2_C_map_obj_map_hom X;
     f_comp_prop _ _ _ := fun_arr_2_C_map_obj_comp_prop X;
     f_id_prop := fun_arr_2_C_map_obj_id_prop X |}.

Definition arr_cat_fun_2_C_map_hom {C} {X Y : Ob (ArrCat C)}
   (f : Hom X Y) :
  Hom (arr_cat_fun_2_C_map_obj X) (arr_cat_fun_2_C_map_obj Y).
Proof.
cbn; unfold natural_transformation; cbn.
destruct f as ((g1 & g2) & Hgg); cbn in Hgg.
exists
  (λ b : bool,
   if b return
      Hom (fun_arr_2_C_map_obj_map_obj X b) (fun_arr_2_C_map_obj_map_obj Y b)
   then g2 else g1).
intros b1 b2 f.
destruct X as (XA & XB & Xf).
destruct Y as (YA & YB & Yf).
move Xf before Yf.
unfold fun_arr_2_C_map_obj_map_hom.
cbn in *.
destruct b1, b2; cbn.
-now rewrite unit_l, unit_r.
-easy.
-easy.
-now rewrite unit_l, unit_r.
Defined.

Theorem arr_cat_fun_2_C_comp_prop {C} {X Y Z : Ob (ArrCat C)}
  (f : Hom X Y) (g : Hom Y Z) :
  arr_cat_fun_2_C_map_hom (g ◦ f) =
  arr_cat_fun_2_C_map_hom g ◦ arr_cat_fun_2_C_map_hom f.
Proof.
destruct f as ((f1 & f2) & Hff); cbn in Hff.
destruct g as ((g1 & g2) & Hgg); cbn in Hgg.
move Hff before Hgg.
unfold arr_cat_fun_2_C_map_hom; cbn.
unfold nat_transf_comp; cbn.
apply eq_existT_uncurried.
assert
  (p
  : (λ b : bool,
       if b return
          (Hom (fun_arr_2_C_map_obj_map_obj X b)
               (fun_arr_2_C_map_obj_map_obj Z b))
       then g2 ◦ f2 else g1 ◦ f1) =
    (λ b : bool,
       (if b return
           (Hom (fun_arr_2_C_map_obj_map_obj Y b)
                (fun_arr_2_C_map_obj_map_obj Z b))
        then g2 else g1)
       ◦
       (if b return
           (Hom (fun_arr_2_C_map_obj_map_obj X b)
                (fun_arr_2_C_map_obj_map_obj Y b))
        then f2 else f1))). {
  apply fun_ext; intros b.
  now destruct b.
}
exists p.
apply fun_ext; intros b1.
apply fun_ext; intros b2.
apply fun_ext; intros f.
apply Hom_set.
Qed.

Theorem arr_cat_fun_2_C_id_prop {C} (X : Ob (ArrCat C)) :
  arr_cat_fun_2_C_map_hom (idc X) = idc (arr_cat_fun_2_C_map_obj X).
Proof.
cbn; unfold nat_transf_id.
apply eq_existT_uncurried.
assert
  (p
  : (λ b : bool,
       if b return
          (Hom (fun_arr_2_C_map_obj_map_obj X b)
               (fun_arr_2_C_map_obj_map_obj X b))
       then idc (projT1 (projT2 X))
       else
         idc (projT1 X)) =
         (λ b : bool, idc (fun_arr_2_C_map_obj_map_obj X b))). {
  apply fun_ext; intros b.
  now destruct b.
}
exists p.
apply fun_ext; intros b1.
apply fun_ext; intros b2.
apply fun_ext; intros f.
apply Hom_set.
Qed.

Definition fun_2_C_arr_cat_map_obj {C} (X : Ob (FunCat Cat_2 C)) :
  Ob (ArrCat C).
Proof.
exists (f_obj X false).
exists (f_obj X true).
now apply f_hom.
Defined.

Definition fun_2_C_arr_cat_map_hom {C} {X Y : Ob (FunCat Cat_2 C)}
  (f : Hom X Y) : Hom (fun_2_C_arr_cat_map_obj X) (fun_2_C_arr_cat_map_obj Y).
Proof.
cbn; unfold Arr_Hom; cbn.
exists (nt_component f false, nt_component f true); cbn.
apply nt_commute.
Defined.

Theorem fun_2_C_arr_cat_comp_prop {C} {X Y Z : Ob (FunCat Cat_2 C)}
  (f : Hom X Y) (g : Hom Y Z) :
  fun_2_C_arr_cat_map_hom (g ◦ f) =
  fun_2_C_arr_cat_map_hom g ◦ fun_2_C_arr_cat_map_hom f.
Proof.
apply eq_existT_uncurried.
exists eq_refl; cbn.
apply Hom_set.
Defined.

Theorem fun_2_C_arr_cat_id_prop {C} (X : Ob (FunCat Cat_2 C)) :
  fun_2_C_arr_cat_map_hom (idc X) = idc (fun_2_C_arr_cat_map_obj X).
Proof.
apply eq_existT_uncurried.
now exists eq_refl.
Defined.

(* to use equality of functor records;
   to do:
     1/ move it to category.v after the definition of records
        (but not sure it is useful, actually)
     2/ use the same system for all definitions with dependend
        pairs I made, to define them with records, which is
        more readable *)

Definition functor_td C D :=
  {mo : Ob C → Ob D &
   {mh : ∀ a b : Ob C, Hom a b → Hom (mo a) (mo b) &
    ((∀ (a b c : Ob C) (f : Hom a b) (g : Hom b c),
         mh a c (g ◦ f) = mh b c g ◦ mh a b f) *
     (∀ a : Ob C, mh a a (idc a) = idc (mo a)))%type }}.

Theorem functor_eq_of_dep_pair {C D} :
  ∀ (mo1 mo2 : Ob C → Ob D) mh1 mh2 mc1 mc2 mi1 mi2,
  (existT _ mo1 (existT _ mh1 (mc1, mi1)) : functor_td C D) =
  (existT _ mo2 (existT _ mh2 (mc2, mi2)) : functor_td C D)
  → {| f_obj := mo1; f_hom := mh1; f_comp_prop := mc1;
        f_id_prop := mi1 |} =
     {| f_obj := mo2; f_hom := mh2; f_comp_prop := mc2;
        f_id_prop := mi2 |}.
Proof.
intros * Hp.
apply h4c.eq_existT_pair_transport in Hp.
destruct Hp as (p, Hp).
destruct p; cbn in Hp.
apply h4c.eq_existT_pair_transport in Hp.
destruct Hp as (p, Hp).
destruct p; cbn in Hp.
Set Keep Proof Equalities.
injection Hp.
intros H1 H2.
now destruct H1, H2.
Qed.

(* *)

Theorem arr_cat_equiv_2_cat {C} :
  are_equivalent_categories (ArrCat C) (FunCat Cat_2 C).
Proof.
exists
  {| f_obj := arr_cat_fun_2_C_map_obj;
     f_hom _ _ := arr_cat_fun_2_C_map_hom;
     f_comp_prop _ _ _ := arr_cat_fun_2_C_comp_prop;
     f_id_prop := arr_cat_fun_2_C_id_prop |}.
exists
  {| f_obj := fun_2_C_arr_cat_map_obj;
     f_hom _ _ := fun_2_C_arr_cat_map_hom;
     f_comp_prop _ _ _ := fun_2_C_arr_cat_comp_prop;
     f_id_prop := fun_2_C_arr_cat_id_prop |}.
-unfold functor_comp; cbn.
 unfold functor_id; cbn.
 assert ((λ x : Arr_Ob C, fun_2_C_arr_cat_map_obj (arr_cat_fun_2_C_map_obj x)) =
         (λ x : Arr_Ob C, x)). {
   apply fun_ext; intros (XA & XB & Xf).
   unfold fun_2_C_arr_cat_map_obj.
   now unfold arr_cat_fun_2_C_map_obj; cbn.
 }
 unfold functor_comp_id_prop; cbn.
 unfold fun_2_C_arr_cat_map_hom at 2.
 apply functor_eq_of_dep_pair.
 apply eq_existT_uncurried.
 assert
   (H1 : (λ x : Arr_Ob C,
     fun_2_C_arr_cat_map_obj (arr_cat_fun_2_C_map_obj x)) =
    (λ x, x)). {
   apply fun_ext; intros x.
   now destruct x as (XA & XB & Xf).
 }
 exists H1; cbn.
 (* blocked: the problem comes from the definition of ArrCat because the
    objects are not all of the same type, therefore a dependent pair is
    required (actually a dependent triplet), and transport (or eq_rect)
    is also necessary, which create difficulties to be simplified, due
    to the equality requires ext_fun. Probable solution: remove ArrCat
    and define it as C^2. I don't like that but perhaps there is no
    better solution *)
Abort.

(* Monoid *)

Record monoid :=
  { m_set : Set_type;
    m_op : st_type m_set → st_type m_set → st_type m_set;
    m_unit : st_type m_set;
    m_assoc : ∀ x y z, m_op x (m_op y z) = m_op (m_op x y) z;
    m_unit_l : ∀ x, m_op m_unit x = x;
    m_unit_r : ∀ x, m_op x m_unit = x }.

Arguments m_op {_}.

Definition m_type (M : monoid) : Type := st_type (m_set M).

Definition cat_of_monoid M :=
  {| Ob := unit;
     Hom _ _ := m_type M;
     comp _ _ _ := m_op;
     idc _ := m_unit M;
     unit_l _ _ := m_unit_l M;
     unit_r _ _ := m_unit_r M;
     assoc _ _ _ _ := m_assoc M;
     Hom_set _ _ := st_is_set (m_set M) |}.

(* For any object C in any category 𝒞, the set of arrows from C to C,
   written as Hom_𝒞 (C, C), is a monoid under the composition operation
   of 𝒞. (Awodey) *)

Theorem arrow_set_is_monoid {𝒞} (C : Ob 𝒞) : monoid.
refine
  {| m_set := mk_Set_type (Hom C C) (Hom_set _ _);
     m_op a b := b ◦ a;
     m_unit := idc _;
     m_assoc := assoc;
     m_unit_l := unit_l;
     m_unit_r := unit_r |}.
Defined.

(* Since monoids are structured sets, there is a category Mon whose
   objects are monoids and whose arrows are functions that preserve
   the monoid structure. In detail, a homomorphism from a monoid M to
   a monoid N is a function h : M → N such that for all m, n ∈ M,
      h (m ._M n) = h(m) ·_N h(n)
   and
      h (u_M) = u_N.

   (Awodey)
 *)

Definition Mon_Hom (M N : monoid) :=
  { h : m_type M → m_type N &
    ((∀ m n, h (m_op m n) = m_op (h m) (h n)) *
     (h (m_unit _) = m_unit _))%type }.

Definition mh_fun {M N} (f : Mon_Hom M N) : m_type M → m_type N := projT1 f.

Definition Mon_comp {M N P : monoid}
  (f : Mon_Hom M N) (g : Mon_Hom N P) : Mon_Hom M P.
Proof.
destruct f as (hf & f_op_prop & f_unit_prop).
destruct g as (hg & g_op_prop & g_unit_prop).
move hg before hf.
move g_op_prop before f_op_prop.
exists (λ m, (hg (hf m))).
split.
-intros m n.
 etransitivity; [ | apply g_op_prop ].
 apply f_equal, f_op_prop.
-etransitivity; [ | apply g_unit_prop ].
 apply f_equal, f_unit_prop.
Defined.

Definition Mon_id (M : monoid) : Mon_Hom M M.
Proof.
exists id; unfold id.
split; [ now intros | easy ].
Defined.

Theorem Mon_unit_l {M N : monoid} (f : Mon_Hom M N) :
  Mon_comp (Mon_id M) f = f.
Proof.
destruct f as (hf & f_op_prop & f_unit_prop).
apply eq_existT_uncurried; unfold id.
exists eq_refl; cbn.
f_equal; [ | now destruct f_unit_prop ].
apply fun_ext; intros m.
apply fun_ext; intros n.
now destruct (f_op_prop m n).
Defined.

Theorem Mon_unit_r {M N : monoid} (f : Mon_Hom M N) :
  Mon_comp f (Mon_id N) = f.
Proof.
destruct f as (hf & f_op_prop & f_unit_prop).
apply eq_existT_uncurried; unfold id.
exists eq_refl; cbn.
f_equal; [ | now destruct f_unit_prop ].
apply fun_ext; intros m.
apply fun_ext; intros n.
now destruct (f_op_prop m n).
Defined.

Theorem Mon_assoc {M N P Q : monoid}
        (f : Mon_Hom M N) (g : Mon_Hom N P) (h : Mon_Hom P Q) :
  Mon_comp f (Mon_comp g h) = Mon_comp (Mon_comp f g) h.
Proof.
destruct f as (hf & f_op_prop & f_unit_prop).
destruct g as (hg & g_op_prop & g_unit_prop).
destruct h as (hh & h_op_prop & h_unit_prop).
apply eq_existT_uncurried.
exists eq_refl; cbn.
f_equal.
-apply fun_ext; intros a.
 apply fun_ext; intros b.
 unfold eq_trans.
 destruct (h_op_prop (hg (hf a)) (hg (hf b))).
 unfold f_equal.
 destruct (g_op_prop (hf a) (hf b)).
 now destruct (f_op_prop a b).
-unfold eq_trans; cbn.
 destruct h_unit_prop; cbn.
 destruct g_unit_prop; cbn.
 now destruct f_unit_prop.
Defined.

Theorem Mon_Hom_set M N : isSet (Mon_Hom M N).
Proof.
apply h4c.isSet_isSet_sigT.
-intros f.
 intros (p1, p2) (q1, q2).
 move q1 before p1.
 f_equal; [ | apply st_is_set ].
 apply fun_ext; intros m.
 apply fun_ext; intros n.
 apply st_is_set.
-apply h4c.isSet_forall.
 intros; apply st_is_set.
Defined.

Definition MonCat :=
  {| Ob := monoid;
     Hom := Mon_Hom;
     comp _ _ _ := Mon_comp;
     idc := Mon_id;
     unit_l _ _ := Mon_unit_l;
     unit_r _ _ := Mon_unit_r;
     assoc _ _ _ _ := Mon_assoc;
     Hom_set := Mon_Hom_set |}.

(* The reader should check that a monoid homomorphism from M to N is
   the same thing as a functor from M regarded as a category to N
   regarded as a category. In this sense, categories are also
   generalized monoids, and functors are generalized homomorphisms.
   (Awodey)
 *)

(* what does he mean by "same thing"? one is a specific definition
   (a "monoid homomorphism") and the other is a functor, differently
   defined *)

(*
Mon_Hom
     : monoid → monoid → Type
functor
     : category → category → Type

Mon_Hom =
λ M N : monoid,
  {h : m_type M → m_type N &
  (∀ m n : m_type M, h (m_op m n) = m_op (h m) (h n)) *
  (h (m_unit M) = m_unit N)}
     : monoid → monoid → Type

Record functor (C D : category) : Type := Build_functor
  { f_obj : Ob C → Ob D;
    f_hom : ∀ a b : Ob C, Hom a b → Hom (f_obj a) (f_obj b);
    f_comp_prop : ∀ (a b c : Ob C) (f : Hom a b) (g : Hom b c),
                    f_hom a c (g ◦ f) = f_hom b c g ◦ f_hom a b f;
    f_id_prop : ∀ a : Ob C, f_hom a a (idc a) = idc (f_obj a) }
*)

(* Free monoid *)

Require Import List.
Import List.ListNotations.

Record alphabet :=
  { fm : { A & ((∀ a b : A, {a = b} + {a ≠ b}) * h4c.isSet A)%type } }.

Definition a_type alph := projT1 (fm alph).
Definition a_eq_dec alph := fst (projT2 (fm alph)).
Definition a_is_set alph := snd (projT2 (fm alph)).

Definition kc_set : alphabet → Set_type :=
  λ alph,
  existT _ (list (a_type alph))
    (areSet.isSet_list (a_eq_dec alph) (a_is_set alph)).

Definition kleene_closure (alph : alphabet) :=
  {| m_set := kc_set alph;
     m_op a b := a ++ b;
     m_unit := [];
     m_assoc a b c := List.app_assoc a b c;
     m_unit_l a := app_nil_l a;
     m_unit_r a := app_nil_r a |}.

(* insertion of generators *)

Definition ins_gen {alph} : a_type alph → m_type (kleene_closure alph) :=
  λ a, [a].

(* A monoid M is freely generated by a subset A of M, if the following
   conditions hold.
   1. Every element m ∈ M can be written as a product of elements of A
      m = a1 ·_M ... ·_M an , ai ∈ A.
   2. No “nontrivial” relations hold in M, that is, if a1 ...aj = a'1
      ...a'k, then this is required by the axioms for monoids.

   The first condition is sometimes called “no junk,” while the second
   condition is sometimes called “no noise.”

   (Awodey)
 *)

Definition no_junk M (A : _ → Prop) :=
  (∀ m : m_type M,
   ∃ ai : list (m_type M),
   (∀ a, List.In a ai → A a) ∧
   List.fold_right (@m_op M) (m_unit M) ai = m).

(* this second condition is ill defined above; what does it mean? *)
Definition no_noise (M : monoid) (A : m_type M → Prop) :=
  True.

Theorem is_freely_generated_by (M : monoid) (A : m_type M → Prop) :
  no_junk M A ∧ no_noise M A
  → ∃ alph, M = kleene_closure alph.
Proof.
intros (H1, _).
unfold no_junk in H1.
assert {A : Type & ((∀ a b : A, {a = b} + {a ≠ b}) * h4c.isSet A)%type }. {
  exists (m_type M).
  split; [ | apply st_is_set ].
  intros.
  (* problem to prove decidability of equality;
     anyway things are not clear in this theorem;
     I give up *)
Abort. (*
}
exists {| fm := X |}.
...
*)

(* First, every monoid N has an underlying set |N|, and every monoid
   homomorphism f : N → M has an underlying function |f| : |N|→|M|. It
   is easy to see that this is a functor, called the “forgetful
   functor.” (Awodey) *)

Definition forgetful_map_obj : Ob MonCat → Ob SetCat := m_set.

Definition forgetful_map_hom {N M : monoid} (f : Mon_Hom N M) :
  Hom (forgetful_map_obj N) (forgetful_map_obj M) := projT1 f.

Theorem forgetful_comp_prop {N M P : Ob MonCat} (f : Hom N M) (g : Hom M P) :
  forgetful_map_hom (g ◦ f) = forgetful_map_hom g ◦ forgetful_map_hom f.
Proof.
destruct f as (f & Hf1 & Hf2).
destruct g as (g & Hg1 & Hg2).
reflexivity.
Defined.

Definition forgetful_functor : functor MonCat SetCat :=
  {| f_obj := forgetful_map_obj;
     f_hom _ _ := forgetful_map_hom;
     f_comp_prop _ _ _ := forgetful_comp_prop;
     f_id_prop _ := eq_refl |}.

(* The free monoid M(A) on a set A is by definition “the” monoid with
   the following so called universal mapping property, or UMP!

   Universal Mapping Property of M(A)

   There is a function i : A → |M(A)|, and given any monoid N and any
   function f : A → |N|, there is a *unique* monoid homomorphism ¯f :
   M(A) → N such that |¯f| ◦ i = f, all as indicated in the following
   diagram:

   In Mon:
              ¯f
       M(A) ------⟶ N

   In Sets:
             |¯f|
     |M(A)| ------> |N|
        ↑         ↗
        |       ⋰
      i |     ⋰ f
        |   ⋰
        | ⋰
        A

   (Awodey)
 *)

(* addendum: *unique* up to equality in monoid homomorphisms *)

Definition Mon_Hom_eq {M N : monoid} (f g : Mon_Hom M N) :=
  mh_fun f = mh_fun g.

Notation "{! ( eq ) x : A  & P }" := (sigT (setoid_unique eq (fun x : A => P)))
  (at level 0, x at level 99) : type_scope.

Definition is_free_monoid (A : alphabet) (M : monoid) :=
  { i : a_type A → m_type M &
    ∀ (N : monoid) (f : a_type A → m_type N),
    {! (Mon_Hom_eq) f' : Hom (M : Ob MonCat) (N : Ob MonCat) &
     ∀ x, mh_fun f' (i x) = f x } }.

Definition ifm_fun {A M} (fm : is_free_monoid A M) : a_type A → m_type M :=
  projT1 fm.

Theorem kleene_closure_has_free_monoid_UMP (A : alphabet) :
  is_free_monoid A (kleene_closure A).
Proof.
exists (λ a, [a]).
intros *.
transparent assert (f' : Hom (kleene_closure A : Ob MonCat) N). {
  exists (List.fold_right (λ s, m_op (f s)) (m_unit N)); cbn.
  split; [ | easy ].
  intros la lb.
  induction la as [| a la]; intros; [ symmetry; apply m_unit_l | ].
  cbn; rewrite IHla.
  apply m_assoc.
}
exists f'; subst f'.
split; [ intros; apply m_unit_r | ].
intros (f' & Hf1 & Hf2) Hff.
apply fun_ext; intros la.
cbn in Hf1, Hf2, Hff, la; cbn.
induction la as [| a la]; [ easy | ].
cbn; rewrite IHla.
specialize (Hf1 [a] la) as H1.
now cbn in H1; rewrite Hff in H1.
Qed.

(* Given monoids M and N with functions i : A → |M| and j : A → |N|,
   each with the UMP of the free monoid on A, there is a (unique)
   monoid isomorphism : h : M ≅ N such that |h| i = j and
   |h⁻¹| j = i. (Awodey) *)

Record Mon_iso (M N : monoid) :=
  { mi :
    { f : Mon_Hom M N &
      { g : Mon_Hom N M &
        (∀ x, mh_fun g (mh_fun f x) = x) ∧
        (∀ y, mh_fun f (mh_fun g y) = y) } } }.

Arguments mi {_} {_}.
Definition mi_fun {M N} (f : Mon_iso M N) :=
  mh_fun (projT1 (mi f)).
Definition mi_fun_inv {M N} (f : Mon_iso M N) :=
  mh_fun (projT1 (projT2 (mi f))).

(*
Theorem glop {A M N} :
  is_free_monoid A M
  → is_free_monoid A N
  → Mon_Hom M N.
Proof.
intros HM HN.
unfold Mon_Hom.
destruct HM as (f, Hf).
destruct HN as (g, Hg).
transparent assert (h : m_type M → m_type N). {
  intros a.
  apply Hf; [ apply g | apply a ].
}
exists h; subst h; cbn.
destruct (Hf N g) as ((f' & Hf'1 & Hf'2), Hf'3).
split; [ | easy ].
apply Hf'1.
Defined.
*)

Theorem free_monoid_fun {A M N i' j'} :
  ∀ (HM : is_free_monoid A M) (HN : is_free_monoid A N),
  (∀ m n, i' (m_op m n) = m_op (i' m) (i' n))
  → (∀ m n, j' (m_op m n) = m_op (j' m) (j' n))
  → i' (m_unit N) = m_unit M
  → j' (m_unit M) = m_unit N
  → (∀ x, i' (ifm_fun HN x) = ifm_fun HM x)
  → (∀ x, j' (ifm_fun HM x) = ifm_fun HN x)
  → ∀ x, i' (j' x) = x.
Proof.
intros * Hi1 Hj1 Hi2 Hj2 Hi3 Hj3.
assert (Hij : ∀ a, i' (j' (ifm_fun HM a)) = ifm_fun HM a). {
  intros a.
  etransitivity; [ | apply Hi3 ].
  apply f_equal, Hj3.
}
specialize (projT2 HM M (ifm_fun HM)) as H1.
destruct H1 as (h & Hh1 & Hh2).
unfold Mon_Hom in Hh2.
cbn in Hh2.
transparent assert
  (h' :
     {h : m_type M → m_type M &
      ((∀ m n : st_type (m_set M), h (m_op m n) = m_op (h m) (h n)) *
       (h (m_unit M) = m_unit M))%type}). {
  transparent assert (h' : m_type M → m_type M). {
    intros a.
    apply i', j', a.
  }
  exists h'; subst h'; cbn.
  split.
  -intros a b.
   etransitivity; [ | apply Hi1 ].
   apply f_equal, Hj1.
  -etransitivity; [ | apply Hi2 ].
   apply f_equal, Hj2.
}
specialize (Hh2 h') as H1.
subst h'; cbn in H1.
specialize (H1 Hij).
unfold Mon_Hom_eq in H1.
cbn in H1.
transparent assert
  (h'' :
     {h : m_type M → m_type M &
      ((∀ m n : st_type (m_set M), h (m_op m n) = m_op (h m) (h n)) *
       (h (m_unit M) = m_unit M))%type}). {
  transparent assert (h' : m_type M → m_type M). {
    intros a; apply a.
  }
  exists h'; subst h'; cbn.
  easy.
}
specialize (Hh2 h'') as H2.
subst h''; cbn in H2.
assert (H : ∀ a, projT1 HM a = projT1 HM a) by easy.
specialize (H2 H); clear H.
unfold Mon_Hom_eq in H2.
cbn in H2.
rewrite H1 in H2.
now specialize (@funext.happly _ _ _ _ H2) as H3.
Defined.

Theorem proposition_1_10 :
  ∀ (A : alphabet) (M N : monoid)
     (HM : is_free_monoid A M)
     (HN : is_free_monoid A N),
  ∃(*!*) h : Mon_iso M N,
   (∀ a, mi_fun h (ifm_fun HM a) = ifm_fun HN a) ∧
   (∀ a, mi_fun_inv h (ifm_fun HN a) = ifm_fun HM a).
Proof.
intros *.
destruct (projT2 HN M (ifm_fun HM)) as ((i' & Hi'1 & Hi'2), (Hi'3, Hi'4)).
destruct (projT2 HM N (ifm_fun HN)) as ((j' & Hj'1 & Hj'2), (Hj'3, Hj'4)).
cbn in Hi'3, Hi'4.
cbn in Hj'3, Hj'4.
move i' after j'.
move Hj'3 before j'.
move Hi'3 before j'.
unfold Mon_Hom_eq in Hj'4, Hi'4.
cbn in Hj'4, Hi'4.
specialize (@free_monoid_fun A M N i' j' HM HN) as H1.
specialize (H1 Hi'1 Hj'1 Hi'2 Hj'2 Hi'3 Hj'3).
specialize (@free_monoid_fun A N M j' i' HN HM) as H2.
specialize (H2 Hj'1 Hi'1 Hj'2 Hi'2 Hj'3 Hi'3).
transparent assert (h : Mon_iso M N). {
  split.
  transparent assert (f : Mon_Hom M N). {
    exists j'.
    split; [ apply Hj'1 | apply Hj'2 ].
  }
  exists f; subst f; cbn.
  transparent assert (g : Mon_Hom N M). {
    exists i'.
    split; [ apply Hi'1 | apply Hi'2 ].
  }
  now exists g; subst g.
}
exists h; subst h; cbn.
easy.
Qed.
(* unicity seems impossible to prove
unfold unique; cbn.
split; [ easy | ].
intros (f) (Hf1, Hf2).
unfold mi_fun in Hf1; cbn in Hf1.
unfold mi_fun_inv in Hf2; cbn in Hf2.
destruct f as (f & g & Hf3 & Hf4).
f_equal; cbn in *.
assert (H3 : j' = mh_fun f) by now apply Hj'4.
assert (H4 : i' = mh_fun g) by now apply Hi'4.
subst i' j'; cbn in *.
apply eq_existT_uncurried.
transparent assert (p
  : existT
      (λ h : m_type M → m_type N,
         ((∀ m n : st_type (m_set M), h (m_op m n) = m_op (h m) (h n)) * (h (m_unit M) = m_unit N))%type)
      (mh_fun f) (Hj'1, Hj'2) = f). {
  destruct f as (f & Hf5 & Hf6); cbn in *.
  apply eq_existT_uncurried.
  exists eq_refl; cbn.
  f_equal.
  -apply fun_ext; intros a.
   apply fun_ext; intros b.
   apply st_is_set.
  -apply st_is_set.
}
exists p; subst p; cbn.
destruct f as (f & Hf5 & Hf6); cbn in *.
destruct g as (g & Hg5 & Hg6); cbn in *.
Set Printing Depth 15.
*)

(* graphs *)

(*
Record graph :=
  { vertex : Type;
    edge : vertex → vertex → Type }.

Arguments edge {_}.

Record graph :=
  { vertex : Type;
    edge : Type;
    source : edge → vertex;
    target : edge → vertex }.
*)

(*
Record graph :=
  { vertex : Type;
    edge : Type;
    source : edge → vertex;
    target : edge → vertex;
    as_source : vertex → list edge;
    as_target : vertex → list edge;
    source_consistency :
      ∀ v e, List.In e (as_source v) ↔ source e = v;
    target_consistency :
      ∀ v e, List.In e (as_target v) ↔ target e = v }.

(* but we are restricted here to graphs whose vertices
   have a finite number of edges *)
*)

(* graphs having a finite number of edges *)

Record graph :=
  { vertex : Type;
    edges : list (vertex * vertex) }.

(* category of graph *)

(* does not work: no way to define Hom

Fixpoint graph_paths {G} n A B :=
  match n with
  | 0 => []
  | S n' =>
      let l := List.map snd (List.filter (λ st, fst st = A) (edges G)) in
...

Definition fcog_Hom {G} : vertex G → vertex G → Type.
Proof.
intros A B.
apply (graph_paths (length (edges G)) A B).
...

Definition free_cat_of_graph (G : graph) : category :=
  {| Ob := vertex G;
     Hom := 42 |}.
...

Definition fcog_comp {G} :
  ∀ A B C : vertex G, edge A B → edge B C → edge A C.
Proof.
intros * EAB EBC.
...

Definition free_cat_of_graph (G : graph) : category :=
  {| Ob := vertex G;
     Hom := 42 |}.
*)

(* monomorphism *)

Definition is_mono {𝒞} {A B : Ob 𝒞} (f : Hom A B) :=
  ∀ C (g h : Hom C A), f ◦ g = f ◦ h → g = h.

Definition is_epi {𝒞} {A B : Ob 𝒞} (f : Hom A B) :=
  ∀ C (g h : Hom B C), g ◦ f = h ◦ f → g = h.

Definition is_inj {A B} (f : A → B) :=
  ∀ x y : A, f x = f y → x = y.

Definition is_surj {A B} (f : A → B) :=
  ∀ y : B, ∃ x : A, f x = y.

(* defined in nLab; equal to is_inj if excluded middle *)
Definition is_strongly_inj {A B} (f : A → B) :=
  ∀ x y : A, x ≠ y → f x ≠ f y.

Theorem is_inj_is_mono {A B : Ob SetCat} (f : Hom A B) :
  is_inj f → is_mono f.
Proof.
intros Hi C g h Hgh.
assert (H1 : ∀ x, f (g x) = f (h x)). {
  intros x.
  change ((λ x, f (g x)) x = (λ x, f (h x)) x).
  unfold "◦" in Hgh.
  cbn in Hgh.
  now destruct Hgh.
}
apply fun_ext; intros x.
apply Hi, H1.
Qed.

Print Assumptions is_inj_is_mono.

Theorem is_mono_is_inj {A B : Ob SetCat} (f : Hom A B) :
  is_mono f → is_inj f.
Proof.
intros Hm x y Hf.
unfold is_mono in Hm.
specialize (Hm A) as H1.
specialize (H1 (λ _, x) (λ _, y)).
cbn in H1.
assert (H : (λ _ : st_type A, f x) = (λ _, f y)). {
  apply fun_ext; intros; easy.
}
specialize (H1 H); clear H.
now apply @funext.happly in H1.
Qed.

Print Assumptions is_mono_is_inj.

Theorem is_inj_is_strongly_inj {A B : Ob SetCat} (f : Hom A B) :
  is_inj f → is_strongly_inj f.
Proof.
intros H x y Hxy Hc.
now apply Hxy, H.
Qed.

Theorem is_strongly_inj_is_mono {A B : Ob SetCat} (f : Hom A B) :
  is_strongly_inj f → is_mono f.
Proof.
intros Hi C g h Hgh.
apply fun_ext; intros x.
specialize (@funext.happly _ _ _ _ Hgh) as H1.
cbn in H1.
unfold is_strongly_inj in Hi.
specialize (H1 x) as H2.
specialize (Hi (g x) (h x)) as H3.
(* requires excluded middle *)
Abort.

Theorem is_mono_is_strongly_inj {A B : Ob SetCat} (f : Hom A B) :
  is_mono f → is_strongly_inj f.
Proof.
intros Hm.
now apply is_inj_is_strongly_inj, is_mono_is_inj.
Qed.

Print Assumptions is_mono_is_strongly_inj.

Theorem is_surj_is_epi {A B : Ob SetCat} (f : Hom A B) :
  is_surj f → is_epi f.
Proof.
intros Hi C g h Hgh.
cbn in C, f.
unfold is_surj in Hi.
apply fun_ext; intros y.
specialize (Hi y) as (x, Hx).
subst y.
apply (@funext.happly _ _ _ _ Hgh).
Qed.

Print Assumptions is_surj_is_epi.

Theorem is_epi_is_surj {A B : Ob SetCat} (f : Hom A B) :
  (∀ P, P + (P → False))
  → is_epi f → is_surj f.
Proof.
intros excl_mid He y.
assert (H1 : not (∀ x, f x ≠ y)). {
  intros Hf.
  specialize (He (existT _ bool areSet.isSet_bool)) as H1.
  cbn in H1.
  specialize (H1 (λ x, if excl_mid (x = y) then true else false)).
  specialize (H1 (λ _, false)).
  cbn in H1.
  assert (H :
    (λ x : st_type A, if excl_mid (f x = y) then true else false) =
    (λ _ : st_type A, false)). {
    apply fun_ext; intros x.
    destruct (excl_mid (f x = y)) as [H| H]; [ | easy ].
    now specialize (Hf x).
  }
  specialize (H1 H); clear H.
  specialize (@funext.happly _ _ _ _ H1 y) as H2.
  cbn in H2.
  now destruct (excl_mid (y = y)).
}
specialize (excl_mid (∃ x, f x = y)) as H2.
destruct H2 as [H2| H2]; [ easy | ].
exfalso; apply H1; intros x H3.
now apply H2; exists x.
Qed.

(* some people claim that excluded middle is not required for this proof *)
Theorem is_epi_is_surj2 {A B : Ob SetCat} (f : Hom A B) :
  is_epi f → is_surj f.
Proof.
intros He y.
Abort.

(* Proposition 2.6. Every iso is mono and epi (Awodey) *)

Proposition awodey_2_6 {𝒞} {A B : Ob 𝒞} {f : Hom A B} :
  is_isomorphism f → is_mono f * is_epi f.
Proof.
intros Hiso.
destruct Hiso as (g & Hgf & Hfg).
split.
-intros C h i Hhi.
 move C before B.
 assert (h = g ◦ f ◦ i). {
   replace h with (idc A ◦ h) by apply unit_r.
   now rewrite <- Hgf, assoc, Hhi, assoc.
 }
 rewrite H, Hgf.
 apply unit_r.
-intros C h i Hhi.
 move C before B.
 assert (h = i ◦ f ◦ g). {
   replace h with (h ◦ idc B) by apply unit_l.
   now rewrite <- Hfg, <- assoc, Hhi.
 }
 rewrite H, assoc, Hfg.
 apply unit_l.
Qed.

(* In Sets the converse of the foregoing also holds: every mono-epi is iso *)

Theorem is_mono_epi_is_iso {A B : Ob SetCat} {f : Hom A B} :
  (∀ P, P + (P → False)) →
  is_mono f → is_epi f → is_isomorphism f.
Proof.
intros excl_mid Hm He.
unfold is_isomorphism.
unfold is_mono in Hm.
unfold is_epi in He.
cbn in *.
assert (g : st_type B → st_type A). {
  intros b.
  specialize (He (existT _ bool areSet.isSet_bool)) as H1.
  cbn in H1.
  specialize (H1 (λ x, if excl_mid (x = b) then true else false)).
  specialize (H1 (λ _, false)).
  cbn in H1.
Abort. (* à voir... *)
