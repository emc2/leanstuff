import algebra.group
import algebra.ring
import algebra.field
import data.prod

namespace algebra

open prod ring

definition complex_ty (A : Type) : Type := A × A

structure complex [class] (A : Type) :=
  (C : Type)
  (mk_complex : A → A → C)
  (real_part : C → A)
  (imaginary_part : C → A)
  (complex_conj : C → C)

namespace complex_ty

definition mk_complex_impl (A : Type) (real : A) (imag : A) := (real, imag)

definition complex_conj_impl (A : Type) [hn : has_neg A] :
                             complex_ty A → complex_ty A
  | (rval, ival) := (rval, -ival)

definition complex_zero (A : Type) [hz : has_zero A] : complex_ty A := (0, 0)

definition complex_one (A : Type) [hz : has_zero A] [ho : has_one A] :
  complex_ty A := (1, 0)

definition complex_add [reducible] {A : Type} [r : ring A]
                       (v1 : complex_ty A) (v2 : complex_ty A) : complex_ty A :=
  let r1 : A := pr1 v1,
      r2 : A := pr1 v2,
      i1 : A := pr2 v1,
      i2 : A := pr2 v2
  in
    (r1 + r2, i1 + i2)

definition complex_mul [reducible] {A : Type} [r : ring A]
                       (v1 : complex_ty A) (v2 : complex_ty A) :
    complex_ty A :=
  let r1 := pr1 v1,
      r2 := pr1 v2,
      i1 := pr2 v1,
      i2 := pr2 v2
  in
    ((r1 * r2) - (i1 * i2), (r1 * i2) + (i1 * r2))

definition complex_neg (A : Type) [hn : has_neg A] :
    complex_ty A → complex_ty A
  | (rval, ival) := (-rval, -ival)

definition complex_inv (A : Type) [hi : has_inv A] [ha : has_add A]
                       [hm : has_mul A] [hn : has_neg A] :
    complex_ty A -> complex_ty A
  | (rval, ival) := (rval * ((rval * rval) + (ival * ival))⁻¹,
                     (-ival) * ((rval * rval) + (ival * ival))⁻¹)

theorem complex_add_assoc (A : Type) [r : ring A] :
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

theorem complex_add_comm (A : Type) [r : ring A] :
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

theorem complex_mul_assoc (A : Type) [r : ring A] :
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
/-
theorem complex_mul_comm (A : Type) [r : ring A] :
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
    from pair_eq (calc r1 * r2 - i1 * i2 = r1 * r2 - i2 * i1 :
                    by rewrite mul.comm
                                     ... = r2 * r1 - i2 * i1 :
                    by rewrite mul.comm)
                 (calc r1 * i2 + i1 * r2 = i1 * r2 + r1 * i2 :
                    by rewrite add.comm
                                     ... = r2 * i1 + r1 * i2 :
                    by rewrite mul.comm
                                     ... = r2 * i1 + i2 * r1 :
                    by rewrite mul.comm)
-/
end complex_ty

end algebra
