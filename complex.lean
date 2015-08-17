import algebra.group
import algebra.ring
import algebra.field
import data.prod

namespace algebra

open prod ring

definition complex_ty [reducible] (A : Type) : Type := A × A

structure complex [class] (A : Type) :=
  (C : Type)
  (mk_complex : A → A → C)
  (real_part : C → A)
  (imaginary_part : C → A)
  (complex_conj : C → C)

namespace complex_ty

definition mk_complex_impl {A : Type} (real : A) (imag : A) := (real, imag)

definition complex_conj_impl {A : Type} [hn : has_neg A] :
                             complex_ty A → complex_ty A
  | (rval, ival) := (rval, -ival)

definition complex_zero [reducible] {A : Type} [hz : has_zero A] :
                        complex_ty A := (0, 0)

definition complex_has_zero [instance] {A : Type} [hz : has_zero A] :
                            has_zero (complex_ty A) :=
  ⦃ has_zero, zero := complex_zero ⦄

definition complex_one {A : Type} [hz : has_zero A] [ho : has_one A] :
  complex_ty A := (1, 0)

definition complex_has_one [instance] {A : Type}
                           [hz : has_zero A] [hz : has_one A] :
                           has_one (complex_ty A) :=
  ⦃ has_one, one := complex_one ⦄

definition complex_I [reducible] {A : Type} [hz : has_zero A] [hz : has_one A] :
                     complex_ty A := (0, 1)

definition complex_add [reducible] {A : Type} [ha : has_add A]
                       (v1 : complex_ty A) (v2 : complex_ty A) : complex_ty A :=
  let r1 : A := pr1 v1,
      r2 : A := pr1 v2,
      i1 : A := pr2 v1,
      i2 : A := pr2 v2
  in
    (r1 + r2, i1 + i2)

definition complex_has_add [instance] {A : Type} [ha : has_add A] :
                           has_add (complex_ty A) :=
  ⦃ has_add, add := complex_add ⦄

definition complex_mul [reducible] {A : Type}
                       [ag : add_group A] [hm : has_mul A]
                       (v1 : complex_ty A) (v2 : complex_ty A) :
    complex_ty A :=
  let r1 := pr1 v1,
      r2 := pr1 v2,
      i1 := pr2 v1,
      i2 := pr2 v2
  in
    ((r1 * r2) - (i1 * i2), (r1 * i2) + (i1 * r2))

definition complex_has_mul [instance] {A : Type}
                           [ag : add_group A] [hm : has_mul A] :
                           has_mul (complex_ty A) :=
  ⦃ has_mul, mul := complex_mul ⦄

definition complex_neg {A : Type} [hn : has_neg A] (c : complex_ty A) :
                       complex_ty A :=
  let r := pr1 c,
      i := pr2 c
  in
    (-r, -i)

definition complex_has_neg [instance] {A : Type} [hn : has_neg A] :
                           has_neg (complex_ty A) :=
  ⦃ has_neg, neg := complex_neg ⦄

definition complex_inv {A : Type} [hi : has_inv A] [ha : has_add A]
                       [hm : has_mul A] [hn : has_neg A] :
    complex_ty A -> complex_ty A
  | (rval, ival) := (rval * ((rval * rval) + (ival * ival))⁻¹,
                     (-ival) * ((rval * rval) + (ival * ival))⁻¹)

theorem complex_add_assoc {A : Type} [asg : add_semigroup A] :
  ∀ (c1 c2 c3 : complex_ty A), complex_add (complex_add c1 c2) c3 =
                               complex_add c1 (complex_add c2 c3) :=
  take c1 : complex_ty A,
  take c2 : complex_ty A,
  take c3 : complex_ty A,
  let r1 := pr1 c1,
      r2 := pr1 c2,
      r3 := pr1 c3,
      i1 := pr2 c1,
      i2 := pr2 c2,
      i3 := pr2 c3
  in
    show (r1 + r2 + r3, i1 + i2 + i3) = (r1 + (r2 + r3), i1 + (i2 + i3)),
    from pair_eq (by rewrite add.assoc) (by rewrite add.assoc)

definition complex_add_semigroup [instance] {A : Type} [asg : add_semigroup A] :
                                            add_semigroup (complex_ty A) :=
  ⦃ add_semigroup, add_assoc := complex_add_assoc ⦄

theorem complex_zero_add {A : Type} [am : add_monoid A] :
  ∀ (c : complex_ty A), complex_add complex_zero c = c :=
  take c : complex_ty A,
  let r : A := pr1 c,
      i : A := pr2 c
  in
    show (0 + r, 0 + i) = c,
    from prod.eq (calc pr₁ (0 + r, 0 + i) = 0 + r : by esimp
                                      ... = r : by rewrite zero_add)
                 (calc pr₂ (0 + r, 0 + i) = 0 + i : by esimp
                                      ... = i : by rewrite zero_add)

theorem complex_add_zero {A : Type} [am : add_monoid A] :
  ∀ (c : complex_ty A), complex_add c complex_zero = c :=
  take c : complex_ty A,
  let r : A := pr1 c,
      i : A := pr2 c
  in
    show (r + 0, i + 0) = c,
    from prod.eq (calc pr₁ (r + 0, i + 0) = r + 0 : by esimp
                                      ... = r : by rewrite add_zero)
                 (calc pr₂ (r + 0, i + 0) = i + 0 : by esimp
                                      ... = i : by rewrite add_zero)

definition complex_add_monoid [instance] {A : Type} [am : add_monoid A] :
                                         add_monoid (complex_ty A) :=
  ⦃ add_monoid, add_assoc := complex_add_assoc,
                zero_add := complex_zero_add,
                add_zero := complex_add_zero ⦄

theorem complex_add_comm {A : Type} [acsg : add_comm_semigroup A] :
  ∀ (c1 c2 : complex_ty A), complex_add c1 c2 = complex_add c2 c1 :=
  take c1 : complex_ty A,
  take c2 : complex_ty A,
  let r1 := pr1 c1,
      r2 := pr1 c2,
      i1 := pr2 c1,
      i2 := pr2 c2
  in
    show (r1 + r2, i1 + i2) = (r2 + r1, i2 + i1),
    from pair_eq (by rewrite add.comm) (by rewrite add.comm)

definition complex_add_comm_semigroup [instance] {A : Type}
                                      [asg : add_comm_semigroup A] :
                                      add_comm_semigroup (complex_ty A) :=
  ⦃ add_comm_semigroup, add_assoc := complex_add_assoc,
                        add_comm := complex_add_comm ⦄

definition complex_add_comm_monoid [instance] {A : Type}
                                   [acm : add_comm_monoid A] :
                                   add_comm_monoid (complex_ty A) :=
  ⦃ add_comm_monoid, add_assoc := complex_add_assoc,
                     zero_add := complex_zero_add,
                     add_zero := complex_add_zero,
                     add_comm := complex_add_comm ⦄

theorem complex_add_left_inv {A : Type} [ag : add_group A] :
  ∀ (c : complex_ty A), complex_add (complex_neg c) c = complex_zero :=
  take c : complex_ty A,
  let r : A := pr1 c,
      i : A := pr2 c
  in
    show (-r + r, -i + i) = (0, 0),
    from pair_eq (add_group.add_left_inv r) (add_group.add_left_inv i)

definition complex_add_group [instance] {A : Type}
                             [ag : add_group A] :
                             add_group (complex_ty A) :=
  ⦃ add_group, add_assoc := complex_add_assoc,
               zero_add := complex_zero_add,
               add_zero := complex_add_zero,
               add_left_inv := complex_add_left_inv ⦄

definition complex_add_comm_group [instance] {A : Type}
                                  [acg : add_comm_group A] :
                                  add_comm_group (complex_ty A) :=
  ⦃ add_comm_group, add_assoc := complex_add_assoc,
                    add_comm := complex_add_comm,
                    zero_add := complex_zero_add,
                    add_zero := complex_add_zero,
                    add_left_inv := complex_add_left_inv ⦄

theorem complex_mul_assoc {A : Type} [r : ring A] :
  ∀ (c1 c2 c3 : complex_ty A), complex_mul (complex_mul c1 c2) c3 =
                               complex_mul c1 (complex_mul c2 c3) :=
  take c1 : complex_ty A,
  take c2 : complex_ty A,
  take c3 : complex_ty A,
  let r1 := pr1 c1,
      r2 := pr1 c2,
      r3 := pr1 c3,
      i1 := pr2 c1,
      i2 := pr2 c2,
      i3 := pr2 c3
  in
  show ((r1 * r2 - i1 * i2) * r3 - (r1 * i2 + i1 * r2) * i3,
        (r1 * r2 - i1 * i2) * i3 + (r1 * i2 + i1 * r2) * r3) =
        (r1 * (r2 * r3 - i2 * i3) - i1 * (r2 * i3 + i2 * r3),
        pr₁ c1 * (r2 * i3 + i2 * r3) + i1 * (r2 * r3 - i2 * i3)),
  from pair_eq
         (calc (r1 * r2 - i1 * i2) * r3 - (r1 * i2 + i1 * r2) * i3
                   = r1 * r2 * r3 - i1 * i2 * r3 - (r1 * i2 + i1 * r2) * i3 :
                     by rewrite mul_sub_right_distrib
               ... = r1 * r2 * r3 - i1 * i2 * r3 -
                     (r1 * i2 * i3 + i1 * r2 * i3) :
                     by rewrite right_distrib
               ... = r1 * r2 * r3 - i1 * i2 * r3 -
                     i1 * r2 * i3 - r1 * i2 * i3 :
                     by rewrite sub_add_eq_sub_sub_swap
               ... = -(r1 * i2 * i3) + (r1 * r2 * r3 +
                     (-(i1 * i2 * r3) - i1 * r2 * i3)) :
                     by rewrite [add.comm, add.assoc]
               ... = -(r1 * i2 * i3) + (r1 * r2 * r3 -
                     (i1 * r2 * i3 + i1 * i2 * r3)) :
                     by rewrite -neg_add_rev
               ... = -(r1 * i2 * i3) + (r1 * r2 * r3 -
                     (i1 * (r2 * i3) + i1 * (i2 * r3))) :
                     by rewrite -*mul.assoc
               ... = -(r1 * i2 * i3) + (r1 * r2 * r3 -
                     i1 * (r2 * i3 + i2 * r3)) :
                     by rewrite -left_distrib
               ... = (-(r1 * i2 * i3) + r1 * r2 * r3) -
                     i1 * (r2 * i3 + i2 * r3) :
                     by rewrite add.assoc
               ... = (r1 * r2 * r3 - r1 * i2 * i3) -
                     i1 * (r2 * i3 + i2 * r3) :
                     by krewrite add.comm
               ... = (r1 * (r2 * r3) - r1 * (i2 * i3)) -
                     i1 * (r2 * i3 + i2 * r3) :
                     by rewrite *mul.assoc
               ... = (r1 * (r2 * r3) + r1 * -(i2 * i3)) -
                     i1 * (r2 * i3 + i2 * r3) :
                     by rewrite -neg_mul_eq_mul_neg
               ... = r1 * (r2 * r3 -i2 * i3) - i1 * (r2 * i3 + i2 * r3) :
                     by rewrite -left_distrib)
         (calc (r1 * r2 - i1 * i2) * i3 + (r1 * i2 + i1 * r2) * r3
                   = r1 * r2 * i3 - i1 * i2 * i3 + (r1 * i2 + i1 * r2) * r3 :
                     by rewrite mul_sub_right_distrib
               ... = r1 * r2 * i3 - i1 * i2 * i3 +
                     (r1 * i2 * r3 + i1 * r2 * r3) :
                     by rewrite right_distrib
               ... = (r1 * r2 * i3 - i1 * i2 * i3) +
                     r1 * i2 * r3 + i1 * r2 * r3 :
                     by rewrite *add.assoc
               ... = (-(i1 * i2 * i3) + r1 * r2 * i3) +
                     r1 * i2 * r3 + i1 * r2 * r3 :
                     by rewrite {_ + r1 * r2 * i3}add.comm
               ... = -(i1 * i2 * i3) + (r1 * r2 * i3 +
                     (r1 * i2 * r3 + i1 * r2 * r3)) :
                     by rewrite *add.assoc
               ... = (r1 * r2 * i3 + (r1 * i2 * r3 +
                     i1 * r2 * r3)) -(i1 * i2 * i3) :
                     by rewrite add.comm
               ... = r1 * r2 * i3 + r1 * i2 * r3 +
                     (i1 * r2 * r3 - i1 * i2 * i3) :
                     by rewrite *add.assoc
               ... = r1 * (r2 * i3) + r1 * (i2 * r3) +
                     (i1 * (r2 * r3) - i1 * (i2 * i3)) :
                     by rewrite *mul.assoc
               ... = r1 * (r2 * i3 + i2 * r3) +
                     (i1 * (r2 * r3) - i1 * (i2 * i3)) :
                     by rewrite -left_distrib
               ... = r1 * (r2 * i3 + i2 * r3) +
                     (i1 * (r2 * r3) + i1 * -(i2 * i3)) :
                     by rewrite -neg_mul_eq_mul_neg
              ... = r1 * (r2 * i3 + i2 * r3) + i1 * (r2 * r3 - i2 * i3) :
                     by rewrite -left_distrib)

theorem complex_mul_comm {A : Type} [r : comm_ring A] :
  ∀ (c1 c2 : complex_ty A), complex_mul c1 c2 = complex_mul c2 c1 :=
  take c1 : complex_ty A,
  take c2 : complex_ty A,
  let r1 := pr1 c1,
      r2 := pr1 c2,
      i1 := pr2 c1,
      i2 := pr2 c2
  in
    show (r1 * r2 - i1 * i2, r1 * i2 + i1 * r2) =
         (r2 * r1 - i2 * i1, r2 * i1 + i2 * r1),
    from pair_eq (calc r1 * r2 - i1 * i2 = r2 * r1 - i1 * i2 :
                    by rewrite mul.comm
                                     ... = r2 * r1 - i2 * i1 :
                    by rewrite {_ * i1}mul.comm)
                 (calc r1 * i2 + i1 * r2 = i1 * r2 + r1 * i2 :
                    by rewrite add.comm
                                     ... = r2 * i1 + r1 * i2 :
                    by rewrite mul.comm
                                     ... = r2 * i1 + i2 * r1 :
                    by rewrite {_ * r1}mul.comm)

end complex_ty

end algebra
