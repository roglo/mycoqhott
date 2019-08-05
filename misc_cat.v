(* miscellaneous categories *)

Set Universe Polymorphism.
Set Nested Proofs Allowed.

Require Import Utf8.
Require Import category.

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
apply h4c.is_set_is_set_sigT. 2: {
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
apply h4c.is_set_is_set_sigT; [ | apply Hom_set ].
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
apply h4c.is_set_is_set_sigT; [ | apply Hom_set ].
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

(* attempt to prove that Coslice C A is equivalent to Slice C^op A *)
(* I guess so *)

Theorem coslice_slice {C} (A : Ob C) :
  are_equivalent_categories (CosliceCat A) (@SliceCat C⁰ A).
Proof.
unfold are_equivalent_categories.
...

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
apply h4c.is_set_is_set_sigT. 2: {
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
        Sets∗∼=1\Sets
    of Sets “under” any singleton 1 ={∗}

    (Awodey)
*)

...

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

(* category of categories *)

Theorem CatCat_comp_prop {C C' C'' : category}
  {F : functor C C'} {G : functor C' C''} :
  ∀ (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
  f_map_hom G (f_map_hom F (g ◦ f)) =
  f_map_hom G (f_map_hom F g) ◦ f_map_hom G (f_map_hom F f).
Proof.
intros.
etransitivity; [ | apply f_comp_prop ].
apply f_equal, f_comp_prop.
Defined.

Theorem CatCat_id_prop {C C' C'' : category}
  {F : functor C C'} {G : functor C' C''} :
  ∀ X : Ob C,
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

Definition fun_arr_2_C_map_obj {C} (X : Ob (ArrCat C)) (b : Ob Cat_2) :
    Ob C := if b then AC_B X else AC_A X.

Definition fun_arr_2_C_map_hom {C} (X : Ob (ArrCat C))
    {b1 b2 : Ob Cat_2} (f : Hom b1 b2) :
  Hom (fun_arr_2_C_map_obj X b1) (fun_arr_2_C_map_obj X b2).
Proof.
intros.
destruct b1.
-destruct b2; [ apply idc | easy ].
-destruct b2; [ now destruct X as (XA & XB & Xf) | apply idc ].
Defined.

Theorem fun_arr_2_C_comp_prop {C} (X : Ob (ArrCat C))
        {b1 b2 b3 : Ob Cat_2} (f : Hom b1 b2) (g : Hom b2 b3) :
  fun_arr_2_C_map_hom X (g ◦ f) =
  fun_arr_2_C_map_hom X g ◦ fun_arr_2_C_map_hom X f.
Proof.
destruct X as (XA & XB & Xf); symmetry.
destruct b1, b2, b3; cbn; try easy.
-apply unit_l.
-apply unit_r.
-apply unit_l.
-apply unit_r.
Defined.

Theorem fun_arr_2_C_id_prop {C} (X : Ob (ArrCat C)) (b : Ob Cat_2) :
  fun_arr_2_C_map_hom X (idc b) = idc (if b then AC_B X else AC_A X).
Proof.
now destruct b.
Defined.

Definition arr_cat_fun_2_C_map_obj {C} (X : Ob (ArrCat C)) :
     Ob (FunCat Cat_2 C)
:=
  {| f_map_obj := fun_arr_2_C_map_obj X;
     f_map_hom _ _ := fun_arr_2_C_map_hom X;
     f_comp_prop _ _ _ := fun_arr_2_C_comp_prop X;
     f_id_prop := fun_arr_2_C_id_prop X |}.

Definition arr_cat_fun_2_C_map_hom {C} {X Y : Ob (ArrCat C)}
   (f : Hom X Y) :
  Hom (arr_cat_fun_2_C_map_obj X) (arr_cat_fun_2_C_map_obj Y).
Proof.
cbn; unfold natural_transformation; cbn.
destruct f as ((g1 & g2) & Hgg); cbn in Hgg.
exists
  (λ b : bool,
   if b return Hom (fun_arr_2_C_map_obj X b) (fun_arr_2_C_map_obj Y b)
   then g2 else g1).
intros b1 b2 f.
destruct X as (XA & XB & Xf).
destruct Y as (YA & YB & Yf).
move Xf before Yf.
unfold fun_arr_2_C_map_hom.
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
       if b return (Hom (fun_arr_2_C_map_obj X b) (fun_arr_2_C_map_obj Z b))
       then g2 ◦ f2 else g1 ◦ f1) =
    (λ b : bool,
       (if b return (Hom (fun_arr_2_C_map_obj Y b) (fun_arr_2_C_map_obj Z b))
        then g2 else g1)
       ◦
       (if b return (Hom (fun_arr_2_C_map_obj X b) (fun_arr_2_C_map_obj Y b))
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
       if b return (Hom (fun_arr_2_C_map_obj X b) (fun_arr_2_C_map_obj X b))
       then idc (projT1 (projT2 X))
       else idc (projT1 X)) = (λ b : bool, idc (fun_arr_2_C_map_obj X b))). {
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
exists (f_map_obj X false).
exists (f_map_obj X true).
now apply f_map_hom.
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
  → {| f_map_obj := mo1; f_map_hom := mh1; f_comp_prop := mc1;
        f_id_prop := mi1 |} =
     {| f_map_obj := mo2; f_map_hom := mh2; f_comp_prop := mc2;
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
  {| f_map_obj := arr_cat_fun_2_C_map_obj;
     f_map_hom _ _ := arr_cat_fun_2_C_map_hom;
     f_comp_prop _ _ _ := arr_cat_fun_2_C_comp_prop;
     f_id_prop := arr_cat_fun_2_C_id_prop |}.
exists
  {| f_map_obj := fun_2_C_arr_cat_map_obj;
     f_map_hom _ _ := fun_2_C_arr_cat_map_hom;
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
