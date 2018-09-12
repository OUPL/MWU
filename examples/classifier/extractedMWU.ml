
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val pred : nat -> nat **)

let pred n0 = match n0 with
| O -> n0
| S u -> u

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val internal_eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let internal_eq_rew_r_dep _ _ hC =
  hC

module type DecidableTypeOrig =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module Nat =
 struct
  (** val pred : nat -> nat **)

  let pred n0 = match n0 with
  | O -> n0
  | S u -> u
 end

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : Big.big_int -> Big.big_int **)

  let rec succ = Big.succ

  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)

  let rec add = Big.add

  (** val add_carry : Big.big_int -> Big.big_int -> Big.big_int **)

  and add_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone (add_carry p q0))
        (fun q0 -> Big.double (add_carry p q0))
        (fun _ -> Big.doubleplusone (succ p))
        y)
      (fun p ->
      Big.positive_case
        (fun q0 -> Big.double (add_carry p q0))
        (fun q0 -> Big.doubleplusone (add p q0))
        (fun _ -> Big.double (succ p))
        y)
      (fun _ ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone (succ q0))
        (fun q0 -> Big.double (succ q0))
        (fun _ -> Big.doubleplusone Big.one)
        y)
      x

  (** val pred_double : Big.big_int -> Big.big_int **)

  let rec pred_double x =
    Big.positive_case
      (fun p -> Big.doubleplusone (Big.double p))
      (fun p -> Big.doubleplusone (pred_double p))
      (fun _ -> Big.one)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos Big.one
  | IsPos p -> IsPos (Big.doubleplusone p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (Big.double p)
  | x0 -> x0

  (** val double_pred_mask : Big.big_int -> mask **)

  let double_pred_mask x =
    Big.positive_case
      (fun p -> IsPos (Big.double (Big.double p)))
      (fun p -> IsPos (Big.double (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : Big.big_int -> Big.big_int -> mask **)

  let rec sub_mask x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 -> double_mask (sub_mask p q0))
        (fun q0 -> succ_double_mask (sub_mask p q0))
        (fun _ -> IsPos (Big.double p))
        y)
      (fun p ->
      Big.positive_case
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      Big.positive_case
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : Big.big_int -> Big.big_int -> mask **)

  and sub_mask_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      Big.positive_case
        (fun q0 -> double_mask (sub_mask_carry p q0))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)

  let sub = fun n m -> Big.max Big.one (Big.sub n m)

  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)

  let rec mul = Big.mult

  (** val iter : ('a1 -> 'a1) -> 'a1 -> Big.big_int -> 'a1 **)

  let rec iter f x n0 =
    Big.positive_case
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n0

  (** val div2 : Big.big_int -> Big.big_int **)

  let div2 p =
    Big.positive_case
      (fun p0 -> p0)
      (fun p0 -> p0)
      (fun _ -> Big.one)
      p

  (** val div2_up : Big.big_int -> Big.big_int **)

  let div2_up p =
    Big.positive_case
      (fun p0 -> succ p0)
      (fun p0 -> p0)
      (fun _ -> Big.one)
      p

  (** val compare_cont :
      comparison -> Big.big_int -> Big.big_int -> comparison **)

  let rec compare_cont = fun c x y -> Big.compare_case c Lt Gt x y

  (** val compare : Big.big_int -> Big.big_int -> comparison **)

  let compare = fun x y -> Big.compare_case Eq Lt Gt x y

  (** val eqb : Big.big_int -> Big.big_int -> bool **)

  let rec eqb p q0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q1 -> eqb p0 q1)
        (fun _ -> false)
        (fun _ -> false)
        q0)
      (fun p0 ->
      Big.positive_case
        (fun _ -> false)
        (fun q1 -> eqb p0 q1)
        (fun _ -> false)
        q0)
      (fun _ ->
      Big.positive_case
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q0)
      p

  (** val ltb : Big.big_int -> Big.big_int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    Big.positive_case
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : Big.big_int -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_nat : nat -> Big.big_int **)

  let rec of_nat = function
  | O -> Big.one
  | S x -> (match x with
            | O -> Big.one
            | S _ -> succ (of_nat x))

  (** val of_succ_nat : nat -> Big.big_int **)

  let rec of_succ_nat = function
  | O -> Big.one
  | S x -> succ (of_succ_nat x)

  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)

  let rec eq_dec p x0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      Big.positive_case
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      Big.positive_case
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p
 end

module N =
 struct
  (** val eqb : Big.big_int -> Big.big_int -> bool **)

  let rec eqb n0 m =
    Big.n_case
      (fun _ -> Big.n_case
                  (fun _ -> true)
                  (fun _ -> false)
                  m)
      (fun p -> Big.n_case
                  (fun _ -> false)
                  (fun q0 -> Coq_Pos.eqb p q0)
                  m)
      n0
 end

module Coq_N =
 struct
  type t = Big.big_int

  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)

  let add = Big.add

  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)

  let mul = Big.mult

  (** val compare : Big.big_int -> Big.big_int -> comparison **)

  let compare = Big.compare_case Eq Lt Gt

  (** val ltb : Big.big_int -> Big.big_int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val to_nat : Big.big_int -> nat **)

  let to_nat a =
    Big.n_case
      (fun _ -> O)
      (fun p -> Coq_Pos.to_nat p)
      a

  (** val of_nat : nat -> Big.big_int **)

  let of_nat = function
  | O -> Big.zero
  | S n' -> (Coq_Pos.of_succ_nat n')

  (** val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n0 f x =
    Big.n_case
      (fun _ -> x)
      (fun p -> Coq_Pos.iter f x p)
      n0

  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)

  let eq_dec n0 m =
    Big.n_case
      (fun _ -> Big.n_case
                  (fun _ -> true)
                  (fun _ -> false)
                  m)
      (fun x -> Big.n_case
                  (fun _ -> false)
                  (fun p0 -> Coq_Pos.eq_dec x p0)
                  m)
      n0
 end

(** val le_lt_dec : nat -> nat -> bool **)

let rec le_lt_dec n0 m =
  match n0 with
  | O -> true
  | S n1 -> (match m with
             | O -> false
             | S m0 -> le_lt_dec n1 m0)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t2 -> (f a) :: (map f t2)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t2 -> f b (fold_right f a0 t2)

module Z =
 struct
  (** val double : Big.big_int -> Big.big_int **)

  let double x =
    Big.z_case
      (fun _ -> Big.zero)
      (fun p -> (Big.double p))
      (fun p -> Big.opp (Big.double p))
      x

  (** val succ_double : Big.big_int -> Big.big_int **)

  let succ_double x =
    Big.z_case
      (fun _ -> Big.one)
      (fun p -> (Big.doubleplusone p))
      (fun p -> Big.opp (Coq_Pos.pred_double p))
      x

  (** val pred_double : Big.big_int -> Big.big_int **)

  let pred_double x =
    Big.z_case
      (fun _ -> Big.opp Big.one)
      (fun p -> (Coq_Pos.pred_double p))
      (fun p -> Big.opp (Big.doubleplusone p))
      x

  (** val pos_sub : Big.big_int -> Big.big_int -> Big.big_int **)

  let rec pos_sub x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 -> double (pos_sub p q0))
        (fun q0 -> succ_double (pos_sub p q0))
        (fun _ -> (Big.double p))
        y)
      (fun p ->
      Big.positive_case
        (fun q0 -> pred_double (pos_sub p q0))
        (fun q0 -> double (pos_sub p q0))
        (fun _ -> (Coq_Pos.pred_double p))
        y)
      (fun _ ->
      Big.positive_case
        (fun q0 -> Big.opp (Big.double q0))
        (fun q0 -> Big.opp (Coq_Pos.pred_double q0))
        (fun _ -> Big.zero)
        y)
      x

  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)

  let add = Big.add

  (** val opp : Big.big_int -> Big.big_int **)

  let opp = Big.opp

  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)

  let sub = Big.sub

  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)

  let mul = Big.mult

  (** val pow_pos : Big.big_int -> Big.big_int -> Big.big_int **)

  let pow_pos z =
    Coq_Pos.iter (mul z) Big.one

  (** val compare : Big.big_int -> Big.big_int -> comparison **)

  let compare = Big.compare_case Eq Lt Gt

  (** val leb : Big.big_int -> Big.big_int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : Big.big_int -> Big.big_int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : Big.big_int -> Big.big_int -> bool **)

  let rec eqb x y =
    Big.z_case
      (fun _ ->
      Big.z_case
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      Big.z_case
        (fun _ -> false)
        (fun q0 -> Coq_Pos.eqb p q0)
        (fun _ -> false)
        y)
      (fun p ->
      Big.z_case
        (fun _ -> false)
        (fun _ -> false)
        (fun q0 -> Coq_Pos.eqb p q0)
        y)
      x

  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)

  let max = Big.max

  (** val div2 : Big.big_int -> Big.big_int **)

  let div2 z =
    Big.z_case
      (fun _ -> Big.zero)
      (fun p ->
      Big.positive_case
        (fun _ -> (Coq_Pos.div2 p))
        (fun _ -> (Coq_Pos.div2 p))
        (fun _ -> Big.zero)
        p)
      (fun p -> Big.opp (Coq_Pos.div2_up p))
      z

  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)

  let eq_dec x y =
    Big.z_case
      (fun _ ->
      Big.z_case
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun x0 ->
      Big.z_case
        (fun _ -> false)
        (fun p0 -> Coq_Pos.eq_dec x0 p0)
        (fun _ -> false)
        y)
      (fun x0 ->
      Big.z_case
        (fun _ -> false)
        (fun _ -> false)
        (fun p0 -> Coq_Pos.eq_dec x0 p0)
        y)
      x
 end

(** val zeven_dec : Big.big_int -> bool **)

let zeven_dec n0 =
  Big.z_case
    (fun _ -> true)
    (fun p ->
    Big.positive_case
      (fun _ -> false)
      (fun _ -> true)
      (fun _ -> false)
      p)
    (fun p ->
    Big.positive_case
      (fun _ -> false)
      (fun _ -> true)
      (fun _ -> false)
      p)
    n0

(** val shift_pos : Big.big_int -> Big.big_int -> Big.big_int **)

let shift_pos n0 z =
  Coq_Pos.iter (fun x -> Big.double x) z n0

type q = { qnum : Big.big_int; qden : Big.big_int }

(** val qnum : q -> Big.big_int **)

let qnum x = x.qnum

(** val qden : q -> Big.big_int **)

let qden x = x.qden

(** val qcompare : q -> q -> comparison **)

let qcompare p q0 =
  Z.compare (Z.mul p.qnum q0.qden) (Z.mul q0.qnum p.qden)

(** val qle_bool : q -> q -> bool **)

let qle_bool x y =
  Z.leb (Z.mul x.qnum y.qden) (Z.mul y.qnum x.qden)

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qinv : q -> q **)

let qinv x =
  Big.z_case
    (fun _ -> { qnum = Big.zero; qden = Big.one })
    (fun p -> { qnum = x.qden; qden = p })
    (fun p -> { qnum = (Big.opp x.qden); qden = p })
    x.qnum

(** val qdiv : q -> q -> q **)

let qdiv x y =
  qmult x (qinv y)

(** val n_of_digits : bool list -> Big.big_int **)

let rec n_of_digits = function
| [] -> Big.zero
| b :: l' ->
  Coq_N.add (if b then Big.one else Big.zero)
    (Coq_N.mul (Big.double Big.one) (n_of_digits l'))

(** val n_of_ascii : char -> Big.big_int **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

module type DecidableType =
 DecidableTypeOrig

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> true
    | _ -> false

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module type WS =
 sig
  module E :
   DecidableType

  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Raw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p :: l ->
    let (k', _) = p in
    (match X.compare k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem k l)

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

  (** val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rect k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rec k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rec k f f0 f1 f2 l _res r0)

  (** val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec mem_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t2, e) = p in
       let f7 = f6 t2 e l __ in
       let f8 = fun _ _ -> let hrec = mem_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t2 e l __ in
       let f10 = f4 t2 e l __ in
       (match X.compare k t2 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let mem_rec =
    mem_rect

  (** val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem **)

  let coq_R_mem_correct k s _res =
    Obj.magic mem_rect k (fun y _ _ _ -> R_mem_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_mem_3 (y, y0, y1, y2, (mem k y2),
      (y6 (mem k y2) __))) s _res __

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p :: s' ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
     * 'elt coq_R_find

  (** val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rect k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rect k f f0 f1 f2 s' _res r0)

  (** val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rec k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rec k f f0 f1 f2 s' _res r0)

  (** val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec find_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t2, e) = p in
       let f7 = f6 t2 e l __ in
       let f8 = fun _ _ ->
         let hrec = find_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t2 e l __ in
       let f10 = f4 t2 e l __ in
       (match X.compare k t2 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let find_rec =
    find_rect

  (** val coq_R_find_correct :
      key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find **)

  let coq_R_find_correct k s _res =
    Obj.magic find_rect k (fun y _ _ _ -> R_find_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_find_3 (y, y0, y1, y2, (find k y2),
      (y6 (find k y2) __))) s _res __

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | [] -> (k, x) :: []
  | p :: l ->
    let (k', y) = p in
    (match X.compare k k' with
     | LT -> (k, x) :: s
     | EQ -> (k, x) :: l
     | GT -> (k', y) :: (add k x l))

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_add

  (** val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rect k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rect k x f f0 f1 f2 l _res r0)

  (** val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rec k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rec k x f f0 f1 f2 l _res r0)

  (** val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec add_rect k x f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t2, e) = p in
       let f7 = f6 t2 e l __ in
       let f8 = fun _ _ ->
         let hrec = add_rect k x f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t2 e l __ in
       let f10 = f4 t2 e l __ in
       (match X.compare k t2 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let add_rec =
    add_rect

  (** val coq_R_add_correct :
      key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add **)

  let coq_R_add_correct k x s _res =
    add_rect k x (fun y _ _ _ -> R_add_0 y) (fun y y0 y1 y2 _ _ _ _ _ ->
      R_add_1 (y, y0, y1, y2)) (fun y y0 y1 y2 _ _ _ _ _ -> R_add_2 (y, y0,
      y1, y2)) (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_add_3 (y, y0, y1, y2,
      (add k x y2), (y6 (add k x y2) __))) s _res __

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | [] -> []
  | p :: l ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> (k', x) :: (remove k l))

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_remove

  (** val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rect k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rec k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rec k f f0 f1 f2 l _res r0)

  (** val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec remove_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t2, e) = p in
       let f7 = f6 t2 e l __ in
       let f8 = fun _ _ ->
         let hrec = remove_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t2 e l __ in
       let f10 = f4 t2 e l __ in
       (match X.compare k t2 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let remove_rec =
    remove_rect

  (** val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove **)

  let coq_R_remove_correct k s _res =
    Obj.magic remove_rect k (fun y _ _ _ -> R_remove_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_remove_3 (y, y0, y1, y2,
      (remove k y2), (y6 (remove k y2) __))) s _res __

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p :: m' -> let (k, e) = p in fold f m' (f k e acc)

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  (** val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rect f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0
      (coq_R_fold_rect f f0 f1 m' (f k e acc) _res r0)

  (** val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rec f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0 (coq_R_fold_rec f f0 f1 m' (f k e acc) _res r0)

  (** val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let rec fold_rect f1 f0 f m acc =
    let f2 = f0 m acc in
    let f3 = f m acc in
    (match m with
     | [] -> f2 __
     | p :: l ->
       let (t2, e) = p in
       let f4 = f3 t2 e l __ in
       let hrec = fold_rect f1 f0 f l (f1 t2 e acc) in f4 hrec)

  (** val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let fold_rec =
    fold_rect

  (** val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold **)

  let coq_R_fold_correct f m acc _res =
    fold_rect f (fun y y0 _ _ _ -> R_fold_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 _ _ -> R_fold_1 (y, y0, y1, y2, y3,
      (fold f y3 (f y1 y2 y0)), (y5 (fold f y3 (f y1 y2 y0)) __))) m acc _res
      __

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | [] -> (match m' with
             | [] -> true
             | _ :: _ -> false)
    | p :: l ->
      let (x, e) = p in
      (match m' with
       | [] -> false
       | p0 :: l' ->
         let (x', e') = p0 in
         (match X.compare x x' with
          | EQ -> (&&) (cmp e e') (equal cmp l l')
          | _ -> false))

  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

  (** val coq_R_equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rect cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e, l, x', e', l', _res, r0) ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rect cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e, l, x', e', l', _x) ->
    f1 m m' x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val coq_R_equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rec cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e, l, x', e', l', _res, r0) ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rec cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e, l, x', e', l', _x) ->
    f1 m m' x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let rec equal_rect cmp f2 f1 f0 f m m' =
    let f3 = f2 m m' in
    let f4 = f1 m m' in
    let f5 = f0 m m' in
    let f6 = f m m' in
    let f7 = f6 m __ in
    let f8 = f7 m' __ in
    (match m with
     | [] -> let f9 = f3 __ in (match m' with
                                | [] -> f9 __
                                | _ :: _ -> f8 __)
     | p :: l ->
       let (t2, e) = p in
       let f9 = f5 t2 e l __ in
       let f10 = f4 t2 e l __ in
       (match m' with
        | [] -> f8 __
        | p0 :: l0 ->
          let (t3, e0) = p0 in
          let f11 = f9 t3 e0 l0 __ in
          let f12 = let _x = X.compare t2 t3 in f11 _x __ in
          let f13 = f10 t3 e0 l0 __ in
          let f14 = fun _ _ ->
            let hrec = equal_rect cmp f2 f1 f0 f l l0 in f13 __ __ hrec
          in
          (match X.compare t2 t3 with
           | EQ -> f14 __ __
           | _ -> f12 __)))

  (** val equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let equal_rec =
    equal_rect

  (** val coq_R_equal_correct :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal **)

  let coq_R_equal_correct cmp m m' _res =
    equal_rect cmp (fun y y0 _ _ _ _ -> R_equal_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 _ _ -> R_equal_1 (y, y0, y1,
      y2, y3, y5, y6, y7, (equal cmp y3 y7), (y11 (equal cmp y3 y7) __)))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ _ _ -> R_equal_2 (y, y0, y1, y2,
      y3, y5, y6, y7, y9)) (fun y y0 y1 _ y3 _ _ _ _ -> R_equal_3 (y, y0, y1,
      y3)) m m' _res __

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f e)) :: (map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f k e)) :: (mapi f m')

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list **)

  let option_cons k o l =
    match o with
    | Some e -> (k, e) :: l
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | [] -> []
  | p :: l -> let (k, e) = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | [] -> []
  | p :: l' ->
    let (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | [] -> map2_r f
  | p :: l ->
    let (k, e) = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let rec combine m = match m with
  | [] -> map (fun e' -> (None, (Some e')))
  | p :: l ->
    let (k, e) = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e0 -> ((Some e0), None)) m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> (k, ((Some e), None)) :: (combine l m')
       | EQ -> (k, ((Some e), (Some e'))) :: (combine l l')
       | GT -> (k', (None, (Some e'))) :: (combine_aux l'))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 []

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> (match o' with
               | Some _ -> Some (o, o')
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module type Int =
 sig
  type t

  val i2z : t -> Big.big_int

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = Big.big_int

  (** val _0 : Big.big_int **)

  let _0 =
    Big.zero

  (** val _1 : Big.big_int **)

  let _1 =
    Big.one

  (** val _2 : Big.big_int **)

  let _2 =
    (Big.double Big.one)

  (** val _3 : Big.big_int **)

  let _3 =
    (Big.doubleplusone Big.one)

  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)

  let add =
    Z.add

  (** val opp : Big.big_int -> Big.big_int **)

  let opp =
    Z.opp

  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)

  let sub =
    Z.sub

  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)

  let mul =
    Z.mul

  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)

  let max =
    Z.max

  (** val eqb : Big.big_int -> Big.big_int -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : Big.big_int -> Big.big_int -> bool **)

  let ltb =
    Z.ltb

  (** val leb : Big.big_int -> Big.big_int -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : Big.big_int -> Big.big_int -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : Big.big_int -> Big.big_int -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> Big.big_int **)

  let i2z n0 =
    n0
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t3, k, e, t4, t5) ->
    f0 t3 (tree_rect f f0 t3) k e t4 (tree_rect f f0 t4) t5

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t3, k, e, t4, t5) ->
    f0 t3 (tree_rec f f0 t3) k e t4 (tree_rec f f0 t4) t5

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (l, _, _, r, _) -> S (add (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _, _) -> false

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> true
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d2, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d2
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e r =
    Node (l, x, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d2 r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.add hr I._2)
    then (match l with
          | Leaf -> assert_false l x d2 r
          | Node (ll, lx, ld, lr, _) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x d2 r)
            else (match lr with
                  | Leaf -> assert_false l x d2 r
                  | Node (lrl, lrx, lrd, lrr, _) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x d2 r)))
    else if I.gt_le_dec hr (I.add hl I._2)
         then (match r with
               | Leaf -> assert_false l x d2 r
               | Node (rl, rx, rd, rr, _) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x d2 rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x d2 r
                       | Node (rll, rlx, rld, rlr, _) ->
                         create (create l x d2 rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x d2 r

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d2 = function
  | Leaf -> Node (Leaf, x, d2, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d2 l) y d' r
     | EQ -> Node (l, y, d2, r, h)
     | GT -> bal l y d' (add x d2 r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1) **)

  let rec remove_min l x d2 r =
    match l with
    | Leaf -> (r, (x, d2))
    | Node (ll, lx, ld, lr, _) ->
      let (l', m) = remove_min ll lx ld lr in ((bal l' x d2 r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let (s2', p) = remove_min l2 x2 d2 r2 in
         let (x, d3) = p in bal s1 x d3 s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d2, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d2 r
     | EQ -> merge l r
     | GT -> bal l y d2 (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d2 ->
      let rec join_aux r = match r with
      | Leaf -> add x d2 l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.add rh I._2)
        then bal ll lx ld (join lr x d2 r)
        else if I.gt_le_dec rh (I.add lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x d2 r
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t2 =
    t2.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t2 =
    t2.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t2 =
    t2.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d2, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d2 r) }
     | EQ -> { t_left = l; t_opt = (Some d2); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d2 rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d2, r, _) -> elements_aux ((x, d2) :: (elements_aux acc r)) l

  (** val elements : 'a1 tree -> (key * 'a1) list **)

  let elements m =
    elements_aux [] m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d2, r, _) -> fold f r (f x d2 (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t2, e1) -> f0 k e0 t2 e1 (enumeration_rect f f0 e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t2, e1) -> f0 k e0 t2 e1 (enumeration_rec f f0 e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d2, r, _) -> cons l (More (x, d2, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d2 cont = function
  | End -> false
  | More (x2, d3, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> if cmp d2 d3 then cont (cons r2 e3) else false
     | _ -> false)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d2, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d2 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> true
  | More (_, _, _, _) -> false

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d2, r, h) -> Node ((map f l), x, (f d2), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d2, r, h) -> Node ((mapi f l), x, (f x d2), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d2, r, _) ->
    (match f x d2 with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d2, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d2 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d2 o -> f (Some d2) o)
      (map_option (fun _ d2 -> f (Some d2) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    (** val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rect x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rec x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    (** val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rect x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d2, r0, _x, _res, r1) ->
      f0 m l y d2 r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d2, r0, _x) -> f1 m l y d2 r0 _x __ __ __
    | R_find_3 (m, l, y, d2, r0, _x, _res, r1) ->
      f2 m l y d2 r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rec x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d2, r0, _x, _res, r1) ->
      f0 m l y d2 r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d2, r0, _x) -> f1 m l y d2 r0 _x __ __ __
    | R_find_3 (m, l, y, d2, r0, _x, _res, r1) ->
      f2 m l y d2 r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

    (** val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (x, x0, x1, x2) -> f x x0 x1 x2 __ __ __
    | R_bal_1 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_2 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_4 (x, x0, x1, x2) -> f3 x x0 x1 x2 __ __ __ __ __
    | R_bal_5 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_6 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_7 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_8 (x, x0, x1, x2) -> f7 x x0 x1 x2 __ __ __ __

    (** val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rec f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (x, x0, x1, x2) -> f x x0 x1 x2 __ __ __
    | R_bal_1 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_2 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_4 (x, x0, x1, x2) -> f3 x x0 x1 x2 __ __ __ __ __
    | R_bal_5 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_6 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_7 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_8 (x, x0, x1, x2) -> f7 x x0 x1 x2 __ __ __ __

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    (** val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rect x d2 f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d2 f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d2 f f0 f1 f2 r0 _res r1)

    (** val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rec x d2 f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d2 f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d2 f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
       * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

    (** val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rect f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d2, r0) -> f l x d2 r0 __
    | R_remove_min_1 (l, x, d2, r0, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d2 r0 ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rect f f0 ll lx ld lr _res r1) l' m __

    (** val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rec f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d2, r0) -> f l x d2 r0 __
    | R_remove_min_1 (l, x, d2, r0, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d2 r0 ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rec f f0 ll lx ld lr _res r1) l' m __

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key * 'elt) * key * 'elt

    (** val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rect f f0 f1 _ _ _ = function
    | R_merge_0 (x, x0) -> f x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
                 x13, x14) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __

    (** val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rec f f0 f1 _ _ _ = function
    | R_merge_0 (x, x0) -> f x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
                 x13, x14) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove

    (** val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rect x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d2, r0, _x, _res, r1) ->
      f0 m l y d2 r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d2, r0, _x) -> f1 m l y d2 r0 _x __ __ __
    | R_remove_3 (m, l, y, d2, r0, _x, _res, r1) ->
      f2 m l y d2 r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rec x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d2, r0, _x, _res, r1) ->
      f0 m l y d2 r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d2, r0, _x) -> f1 m l y d2 r0 _x __ __ __
    | R_remove_3 (m, l, y, d2, r0, _x, _res, r1) ->
      f2 m l y d2 r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key * 'elt)

    (** val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rect f f0 f1 _ _ _ = function
    | R_concat_0 (x, x0) -> f x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __

    (** val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rec f f0 f1 _ _ _ = function
    | R_concat_0 (x, x0) -> f x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    (** val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rect x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d2, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d2 r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d2, r0, _x) -> f1 m l y d2 r0 _x __ __ __
    | R_split_3 (m, l, y, d2, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d2 r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 r0 _res r1) rl o rr __

    (** val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rec x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d2, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d2 r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d2, r0, _x) -> f1 m l y d2 r0 _x __ __ __
    | R_split_3 (m, l, y, d2, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d2 r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 r0 _res r1) rl o rr __

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    (** val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rect f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d2, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d2 r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d2, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d2 r0 _x __ __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)

    (** val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rec f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d2, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d2 r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d2, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d2 r0 _x __ __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)

    type ('elt, 'x0, 'x) coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'x0 tree
    | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

    (** val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d2, r1, _x) ->
      f1 m1 m2 l1 x1 d2 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d2, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d2 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d2, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d2 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d2, r1, _x) ->
      f1 m1 m2 l1 x1 d2 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d2, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d2 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d2, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d2 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key * 'a1) list **)

    let rec flatten_e = function
    | End -> []
    | More (x, e0, t2, r) -> (x, e0) :: (app (elements t2) (flatten_e r))
   end
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x e m =
    Raw.add x e (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x m =
    Raw.remove x (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x m =
    Raw.mem x (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x m =
    Raw.find x (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> nat **)

  let cardinal m =
    Raw.cardinal (this m)

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
 end

module Make =
 functor (X:OrderedType) ->
 IntMake(Z_as_Int)(X)

module WFacts_fun =
 functor (E:DecidableType) ->
 functor (M:sig
  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 struct
  (** val eqb : E.t -> E.t -> bool **)

  let eqb x y =
    if E.eq_dec x y then true else false

  (** val coq_In_dec : 'a1 M.t -> M.key -> bool **)

  let coq_In_dec m x =
    let b = M.mem x m in if b then true else false
 end

module WFacts =
 functor (M:WS) ->
 WFacts_fun(M.E)(M)

module Facts = WFacts

module WProperties_fun =
 functor (E:DecidableType) ->
 functor (M:sig
  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 struct
  module F = WFacts_fun(E)(M)

  (** val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3 **)

  let uncurry f p =
    f (fst p) (snd p)

  (** val of_list : (M.key * 'a1) list -> 'a1 M.t **)

  let of_list l =
    fold_right (uncurry M.add) M.empty l

  (** val to_list : 'a1 M.t -> (M.key * 'a1) list **)

  let to_list =
    M.elements

  (** val fold_rec :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ ->
      'a3) -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ ->
      'a3 -> 'a3) -> 'a3 **)

  let fold_rec f i m hempty hstep =
    let f0 = uncurry f in
    let l = rev (M.elements m) in
    let hstep' = fun k e a m' m'' x ->
      hstep (fst (k, e)) (snd (k, e)) a m' m'' __ __ __ x
    in
    let rec f1 l0 hstep'0 m0 =
      match l0 with
      | [] -> hempty m0 __
      | y :: l1 ->
        let (k, e) = y in
        hstep'0 k e (fold_right f0 i l1) (of_list l1) m0 __ __ __
          (f1 l1 (fun k0 e0 a m' m'' _ _ _ x ->
            hstep'0 k0 e0 a m' m'' __ __ __ x) (of_list l1))
    in f1 l (fun k e a m' m'' _ _ _ x -> hstep' k e a m' m'' x) m

  (** val fold_rec_bis :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t
      -> __ -> __ -> 'a3 -> 'a3) -> 'a3 **)

  let fold_rec_bis f i m pmorphism pempty pstep =
    fold_rec f i m (fun m0 _ -> pmorphism M.empty m0 i __ pempty)
      (fun k e a m' m'' _ _ _ x ->
      pmorphism (M.add k e m') m'' (f k e a) __ (pstep k e a m' __ __ x))

  (** val fold_rec_nodep :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 **)

  let fold_rec_nodep f i m x x0 =
    fold_rec_bis f i m (fun _ _ _ _ x1 -> x1) x (fun k e a _ _ _ x1 ->
      x0 k e a __ x1)

  (** val fold_rec_weak :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
      -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3
      -> 'a3) -> 'a1 M.t -> 'a3 **)

  let fold_rec_weak f i x x0 x1 m =
    fold_rec_bis f i m x x0 (fun k e a m' _ _ x2 -> x1 k e a m' __ x2)

  (** val fold_rel :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
      'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 ->
      'a4) -> 'a4 **)

  let fold_rel f g i j m rempty rstep =
    let l = rev (M.elements m) in
    let rstep' = fun k e a b x -> rstep k e a b __ x in
    let rec f0 l0 rstep'0 =
      match l0 with
      | [] -> rempty
      | y :: l1 ->
        rstep'0 (fst y) (snd y) (fold_right (uncurry f) i l1)
          (fold_right (uncurry g) j l1) __
          (f0 l1 (fun k e a0 b _ x -> rstep'0 k e a0 b __ x))
    in f0 l (fun k e a b _ x -> rstep' k e a b x)

  (** val map_induction :
      ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
      __ -> __ -> 'a2) -> 'a1 M.t -> 'a2 **)

  let map_induction x x0 m =
    fold_rec (fun _ _ _ -> ()) () m x (fun k e _ m' m'' _ _ _ x1 ->
      x0 m' m'' x1 k e __ __)

  (** val map_induction_bis :
      ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
      M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2 **)

  let map_induction_bis x x0 x1 m =
    fold_rec_bis (fun _ _ _ -> ()) () m (fun m0 m' _ _ x2 -> x m0 m' __ x2)
      x0 (fun k e _ m' _ _ x2 -> x1 k e m' __ x2)

  (** val cardinal_inv_2 : 'a1 M.t -> nat -> (M.key * 'a1) **)

  let cardinal_inv_2 m _ =
    let l = M.elements m in
    (match l with
     | [] -> assert false (* absurd case *)
     | p :: _ -> p)

  (** val cardinal_inv_2b : 'a1 M.t -> (M.key * 'a1) **)

  let cardinal_inv_2b m =
    let n0 = M.cardinal m in
    let x = fun x -> cardinal_inv_2 m x in
    (match n0 with
     | O -> assert false (* absurd case *)
     | S n1 -> x n1)

  (** val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t **)

  let filter f m =
    M.fold (fun k e m0 -> if f k e then M.add k e m0 else m0) m M.empty

  (** val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool **)

  let for_all f m =
    M.fold (fun k e b -> if f k e then b else false) m true

  (** val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool **)

  let exists_ f m =
    M.fold (fun k e b -> if f k e then true else b) m false

  (** val partition :
      (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t **)

  let partition f m =
    ((filter f m), (filter (fun k e -> negb (f k e)) m))

  (** val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t **)

  let update m1 m2 =
    M.fold M.add m2 m1

  (** val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t **)

  let restrict m1 m2 =
    filter (fun k _ -> M.mem k m2) m1

  (** val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t **)

  let diff m1 m2 =
    filter (fun k _ -> negb (M.mem k m2)) m1

  (** val coq_Partition_In :
      'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool **)

  let coq_Partition_In _ m1 _ k =
    F.coq_In_dec m1 k

  (** val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool **)

  let update_dec _ m' k _ =
    F.coq_In_dec m' k

  (** val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t **)

  let filter_dom f =
    filter (fun k _ -> f k)

  (** val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t **)

  let filter_range f =
    filter (fun _ -> f)

  (** val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool **)

  let for_all_dom f =
    for_all (fun k _ -> f k)

  (** val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool **)

  let for_all_range f =
    for_all (fun _ -> f)

  (** val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool **)

  let exists_dom f =
    exists_ (fun k _ -> f k)

  (** val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool **)

  let exists_range f =
    exists_ (fun _ -> f)

  (** val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t **)

  let partition_dom f =
    partition (fun k _ -> f k)

  (** val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t **)

  let partition_range f =
    partition (fun _ -> f)
 end

module WProperties =
 functor (M:WS) ->
 WProperties_fun(M.E)(M)

module Properties = WProperties

(** val map0 : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map0 f = function
| [] -> []
| x :: s' -> (f x) :: (map0 f s')

type ordinal = nat
  (* singleton inductive, whose constructor was Ordinal *)

type d = { num : Big.big_int; den : Big.big_int }

(** val num : d -> Big.big_int **)

let num x = x.num

(** val den : d -> Big.big_int **)

let den x = x.den

(** val d_to_Q : d -> q **)

let d_to_Q d2 =
  { qnum = d2.num; qden = (shift_pos d2.den Big.one) }

(** val d0 : d **)

let d0 =
  { num = Big.zero; den = Big.one }

(** val d1 : d **)

let d1 =
  { num = (Big.double Big.one); den = Big.one }

(** val dadd : d -> d -> d **)

let dadd d2 d3 =
  let { num = x1; den = y1 } = d2 in
  let { num = x2; den = y2 } = d3 in
  if Coq_Pos.ltb y1 y2
  then { num =
         (Z.add
           (Z.mul (Z.pow_pos (Big.double Big.one) (Coq_Pos.sub y2 y1)) x1) x2);
         den = y2 }
  else if Coq_Pos.ltb y2 y1
       then { num =
              (Z.add
                (Z.mul (Z.pow_pos (Big.double Big.one) (Coq_Pos.sub y1 y2))
                  x2) x1); den = y1 }
       else { num = (Z.add x1 x2); den = y1 }

(** val dmult : d -> d -> d **)

let dmult d2 d3 =
  let { num = x1; den = y1 } = d2 in
  let { num = x2; den = y2 } = d3 in
  { num = (Z.mul x1 x2); den = (Coq_Pos.add y1 y2) }

(** val dopp : d -> d **)

let dopp d2 =
  let { num = x; den = y } = d2 in { num = (Z.opp x); den = y }

(** val dsub : d -> d -> d **)

let dsub d2 d3 =
  dadd d2 (dopp d3)

(** val dle_bool : d -> d -> bool **)

let dle_bool d2 d3 =
  qle_bool (d_to_Q d2) (d_to_Q d3)

(** val dlt_bool : d -> d -> bool **)

let dlt_bool d2 d3 =
  match qcompare (d_to_Q d2) (d_to_Q d3) with
  | Lt -> true
  | _ -> false

(** val dred' : Big.big_int -> nat -> Big.big_int * nat **)

let rec dred' n0 d2 = match d2 with
| O -> (n0, d2)
| S d' -> if zeven_dec n0 then dred' (Z.div2 n0) d' else (n0, d2)

(** val d_of_Dred' : (Big.big_int * nat) -> d **)

let d_of_Dred' = function
| (x, y) -> { num = x; den = (Coq_Pos.of_nat (S y)) }

(** val dred : d -> d **)

let dred d2 =
  d_of_Dred' (dred' d2.num (pred (Coq_Pos.to_nat d2.den)))

type 't showable =
  't -> char list
  (* singleton inductive, whose constructor was mkShowable *)

(** val to_string : 'a1 showable -> 'a1 -> char list **)

let to_string showable0 =
  showable0

(** val eprint_natchar : Big.big_int -> 'a1 -> 'a1 **)

let eprint_natchar = fun n s ->  
    Printf.eprintf "%c" (Char.chr (Big.to_int n)); 
    flush stderr; 
    s

(** val eprint_ZdivPos : Big.big_int -> Big.big_int -> 'a1 -> 'a1 **)

let eprint_ZdivPos = fun n p s -> 
    (* let num = float_of_int (Big.to_int n) in *)
    (* let den = float_of_int (Big.to_int p) in *)
    (* Printf.eprintf "%F [%F / %F]" (num /. den) num den; *)
    Printf.eprintf "%s, %s" (Big.to_string n) (Big.to_string p);
    (* Printf.eprintf "%F" (num /. den); *)
    flush stderr;
    s

(** val eprint_ascii : char -> 'a1 -> 'a1 **)

let eprint_ascii c t2 =
  eprint_natchar (n_of_ascii c) t2

(** val eprint_string : char list -> 'a1 -> 'a1 **)

let rec eprint_string s t2 =
  match s with
  | [] -> t2
  | c::s' -> let t'0 = eprint_ascii c t2 in eprint_string s' t'0

(** val nl : char **)

let nl =
  '\n'

(** val cr : char **)

let cr =
  '\r'

(** val newline : char list **)

let newline =
  nl::(cr::[])

(** val eprint_newline : 'a1 -> 'a1 **)

let eprint_newline t2 =
  eprint_string newline t2

(** val eprint_Q : q -> 'a1 -> 'a1 **)

let eprint_Q q0 t2 =
  let { qnum = n0; qden = d2 } = q0 in eprint_ZdivPos n0 d2 t2

(** val print_Qvector : 'a1 showable -> ('a1 * q) list -> 'a2 -> 'a2 **)

let rec print_Qvector h l t2 =
  match l with
  | [] -> t2
  | p :: l' ->
    let (a, w) = p in
    let t3 = eprint_string (to_string h a) t2 in
    let t4 = eprint_string (','::(' '::[])) t3 in
    let t5 = eprint_Q w t4 in
    let t6 = eprint_newline t5 in print_Qvector h l' t6

(** val print_Dvector : 'a1 showable -> ('a1 * d) list -> 'a2 -> 'a2 **)

let print_Dvector h l t2 =
  print_Qvector h (map0 (fun p -> ((fst p), (d_to_Q (snd p)))) l) t2

(** val showable_nat : nat showable **)

let showable_nat = function
| O -> '0'::[]
| S n1 ->
  (match n1 with
   | O -> '1'::[]
   | S n2 ->
     (match n2 with
      | O -> '2'::[]
      | S n3 ->
        (match n3 with
         | O -> '3'::[]
         | S n4 ->
           (match n4 with
            | O -> '4'::[]
            | S n5 ->
              (match n5 with
               | O -> '5'::[]
               | S n6 ->
                 (match n6 with
                  | O -> '6'::[]
                  | S n7 ->
                    (match n7 with
                     | O -> '7'::[]
                     | S n8 ->
                       (match n8 with
                        | O -> '8'::[]
                        | S n9 ->
                          (match n9 with
                           | O -> '9'::[]
                           | S n10 ->
                             (match n10 with
                              | O -> '1'::('0'::[])
                              | S _ ->
                                '<'::('n'::('a'::('t'::(' '::('>'::(' '::('1'::('0'::('>'::[])))))))))))))))))))

(** val showable_N : Coq_N.t showable **)

let showable_N n0 =
  to_string showable_nat (Coq_N.to_nat n0)

module type BOUND =
 sig
  val n : nat
 end

module OrdNatDep =
 functor (B:BOUND) ->
 struct
  type t' = Coq_N.t
    (* singleton inductive, whose constructor was mk *)

  (** val coq_val : t' -> Coq_N.t **)

  let coq_val t2 =
    t2

  type t = t'

  (** val compare : t -> t -> t compare0 **)

  let compare _top_assumption_ _top_assumption_0 =
    let _evar_0_ = fun _ _ ->
      internal_eq_rew_r_dep _top_assumption_ _top_assumption_0 (fun _ _ ->
        EQ) __ __
    in
    let _evar_0_0 = fun _ _ ->
      let _evar_0_0 = fun _ -> LT in
      let _evar_0_1 = fun _ -> GT in
      if Coq_N.ltb _top_assumption_ _top_assumption_0
      then _evar_0_0 __
      else _evar_0_1 __
    in
    if Coq_N.eq_dec _top_assumption_ _top_assumption_0
    then _evar_0_ __ __
    else _evar_0_0 __ __

  (** val eq_dec : t -> t -> bool **)

  let eq_dec _top_assumption_ _top_assumption_0 =
    Coq_N.eq_dec (coq_val _top_assumption_) (coq_val _top_assumption_0)
 end

type 't enumerable = 't list

(** val enumerable_fun : 'a1 enumerable -> 'a1 list **)

let enumerable_fun enumerable0 =
  enumerable0

module type MyOrderedType =
 sig
  type t

  val t0 : t

  val enumerable : t enumerable

  val showable : t showable

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module OrderedType_of_MyOrderedType =
 functor (A:MyOrderedType) ->
 struct
  type t = A.t

  (** val compare : A.t -> A.t -> A.t compare0 **)

  let compare =
    A.compare

  (** val eq_dec : A.t -> A.t -> bool **)

  let eq_dec =
    A.eq_dec
 end

module MyOrdNatDep =
 functor (B:BOUND) ->
 struct
  module N = OrdNatDep(B)

  type t' = Coq_N.t
    (* singleton inductive, whose constructor was mk *)

  (** val coq_val : t' -> Coq_N.t **)

  let coq_val t2 =
    t2

  type t = t'

  (** val compare : t -> t -> t compare0 **)

  let compare =
    N.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    N.eq_dec

  (** val t0 : t' **)

  let t0 =
    Big.zero

  (** val enumerate_rec : nat -> t list **)

  let rec enumerate_rec m = match m with
  | O -> t0 :: []
  | S m' -> (Coq_N.of_nat m) :: (enumerate_rec m')

  (** val lt_dec : nat -> nat -> bool **)

  let lt_dec x y =
    let s = le_lt_dec y x in if s then false else true

  (** val enumerate_t : t list **)

  let enumerate_t =
    if lt_dec O B.n then enumerate_rec (Nat.pred B.n) else []

  (** val enumerable : t enumerable **)

  let enumerable =
    enumerate_t

  (** val showable : t showable **)

  let showable x =
    to_string showable_N (coq_val x)
 end

module MyOrdNatDepProps =
 functor (B:BOUND) ->
 struct
  module M = MyOrdNatDep(B)

  module N = M.N

  type t' = Coq_N.t
    (* singleton inductive, whose constructor was mk *)

  (** val coq_val : t' -> Coq_N.t **)

  let coq_val t2 =
    t2

  type t = t'

  (** val compare : t -> t -> t compare0 **)

  let compare =
    N.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    N.eq_dec

  (** val t0 : t' **)

  let t0 =
    Big.zero

  (** val enumerate_rec : nat -> t list **)

  let rec enumerate_rec m = match m with
  | O -> t0 :: []
  | S m' -> (Coq_N.of_nat m) :: (enumerate_rec m')

  (** val lt_dec : nat -> nat -> bool **)

  let lt_dec x y =
    let s = le_lt_dec y x in if s then false else true

  (** val enumerate_t : t list **)

  let enumerate_t =
    if lt_dec O B.n then enumerate_rec (Nat.pred B.n) else []

  (** val enumerable : t enumerable **)

  let enumerable =
    enumerate_t

  (** val showable : t showable **)

  let showable x =
    to_string showable_N (coq_val x)

  (** val enumerate_rec_erased : nat -> Big.big_int list **)

  let rec enumerate_rec_erased m = match m with
  | O -> (Coq_N.of_nat O) :: []
  | S m' -> (Coq_N.of_nat m) :: (enumerate_rec_erased m')

  (** val enumerate_rec_erased_nat : nat -> nat list **)

  let rec enumerate_rec_erased_nat m = match m with
  | O -> O :: []
  | S m' -> m :: (enumerate_rec_erased_nat m')

  (** val coq_Ordinal_of_t : t -> ordinal **)

  let coq_Ordinal_of_t x =
    Coq_N.to_nat (coq_val x)

  (** val val_of_Ordinal : ordinal -> Big.big_int **)

  let val_of_Ordinal =
    Coq_N.of_nat
 end

type val0 = d
  (* singleton inductive, whose constructor was QVal *)

type binop =
| BPlus
| BMinus
| BMult

type 'a expr =
| EVal of val0
| EOpp of 'a expr
| EWeight of 'a
| ECost of 'a
| EEps
| EBinop of binop * 'a expr * 'a expr

type 'a com =
| CSkip
| CUpdate of ('a -> 'a expr)
| CRecv
| CSend
| CSeq of 'a com * 'a com
| CIter of Coq_N.t * 'a com

(** val mult_weights_body : 'a1 com **)

let mult_weights_body =
  CSeq (CRecv, (CSeq ((CUpdate (fun a -> EBinop (BMult, (EWeight a), (EBinop
    (BMinus, (EVal d1), (EBinop (BMult, EEps, (ECost a)))))))), CSend)))

(** val mult_weights_init : 'a1 com **)

let mult_weights_init =
  CSeq ((CUpdate (fun _ -> EVal d1)), CSend)

(** val mult_weights : Coq_N.t -> 'a1 com **)

let mult_weights n0 =
  CSeq (mult_weights_init, (CIter (n0, mult_weights_body)))

type 'a clientOracle = { oracle_init_state : __; oracle_bogus_chan : 
                         __; oracle_prerecv : (__ -> __ -> bool * __);
                         oracle_recv : (__ -> __ -> ('a * d) list * __);
                         oracle_presend : (__ -> ('a * d) list -> bool);
                         oracle_send : (__ -> ('a * d) list -> __ * __) }

type 'a t1 = __

(** val oracle_init_state : 'a1 clientOracle -> 'a1 t1 **)

let oracle_init_state x = x.oracle_init_state

type 'a oracle_chanty = __

(** val oracle_bogus_chan : 'a1 clientOracle -> 'a1 oracle_chanty **)

let oracle_bogus_chan x = x.oracle_bogus_chan

(** val oracle_prerecv :
    'a1 clientOracle -> 'a1 t1 -> 'a1 oracle_chanty -> bool * 'a1 t1 **)

let oracle_prerecv x = x.oracle_prerecv

(** val oracle_recv :
    'a1 clientOracle -> 'a1 t1 -> 'a1 oracle_chanty -> ('a1 * d) list * 'a1 t1 **)

let oracle_recv x = x.oracle_recv

(** val oracle_presend :
    'a1 clientOracle -> 'a1 t1 -> ('a1 * d) list -> bool **)

let oracle_presend x = x.oracle_presend

(** val oracle_send :
    'a1 clientOracle -> 'a1 t1 -> ('a1 * d) list -> 'a1 oracle_chanty * 'a1 t1 **)

let oracle_send x = x.oracle_send

module MWUPre =
 functor (A:MyOrderedType) ->
 struct
  module A' = OrderedType_of_MyOrderedType(A)

  module M = Make(A')

  module MFacts = Facts(M)

  module MProps = Properties(M)

  (** val cGamma : d M.t -> q **)

  let cGamma weights =
    d_to_Q (M.fold (fun _ -> dadd) weights { num = Big.zero; den = Big.one })

  type cstate = { coq_SCosts : d M.t; coq_SPrevCosts : d M.t list;
                  coq_SWeights : d M.t; coq_SEpsilon : d;
                  coq_SOutputs : (A.t -> q) list;
                  coq_SChan : A.t oracle_chanty; coq_SOracleSt : A.t t1 }

  (** val coq_SCosts : A.t clientOracle -> cstate -> d M.t **)

  let coq_SCosts _ c =
    c.coq_SCosts

  (** val coq_SPrevCosts : A.t clientOracle -> cstate -> d M.t list **)

  let coq_SPrevCosts _ c =
    c.coq_SPrevCosts

  (** val coq_SWeights : A.t clientOracle -> cstate -> d M.t **)

  let coq_SWeights _ c =
    c.coq_SWeights

  (** val coq_SEpsilon : A.t clientOracle -> cstate -> d **)

  let coq_SEpsilon _ c =
    c.coq_SEpsilon

  (** val coq_SOutputs : A.t clientOracle -> cstate -> (A.t -> q) list **)

  let coq_SOutputs _ c =
    c.coq_SOutputs

  (** val coq_SChan : A.t clientOracle -> cstate -> A.t oracle_chanty **)

  let coq_SChan _ c =
    c.coq_SChan

  (** val coq_SOracleSt : A.t clientOracle -> cstate -> A.t t1 **)

  let coq_SOracleSt _ c =
    c.coq_SOracleSt

  (** val mwu_send :
      A.t clientOracle -> d M.t -> A.t t1 -> A.t oracle_chanty * A.t t1 **)

  let mwu_send oracle m oracle_st =
    oracle.oracle_send oracle_st (M.elements m)

  (** val mwu_recv :
      A.t showable -> A.t clientOracle -> A.t oracle_chanty -> A.t t1 -> d
      M.t * A.t t1 **)

  let mwu_recv h oracle ch st =
    let (l, st') = oracle.oracle_recv st ch in
    let l' = print_Dvector h l l in ((MProps.of_list l'), st')

  (** val eval_binopc : binop -> d -> d -> d **)

  let eval_binopc b v1 v2 =
    match b with
    | BPlus -> dadd v1 v2
    | BMinus -> dsub v1 v2
    | BMult -> dmult v1 v2

  (** val evalc : A.t clientOracle -> A.t expr -> cstate -> d option **)

  let rec evalc oracle e s =
    match e with
    | EVal v -> Some v
    | EOpp e' ->
      (match evalc oracle e' s with
       | Some v' -> Some (dopp v')
       | None -> None)
    | EWeight a -> M.find a (coq_SWeights oracle s)
    | ECost a -> M.find a (coq_SCosts oracle s)
    | EEps -> Some (coq_SEpsilon oracle s)
    | EBinop (b, e1, e2) ->
      (match evalc oracle e1 s with
       | Some v1' ->
         (match evalc oracle e2 s with
          | Some v2' -> Some (eval_binopc b v1' v2')
          | None -> None)
       | None -> None)

  (** val update_weights :
      A.t clientOracle -> (A.t -> A.t expr) -> cstate -> d M.t option **)

  let update_weights oracle f s =
    M.fold (fun a _ acc ->
      match acc with
      | Some acc' ->
        (match evalc oracle (f a) s with
         | Some q0 ->
           if dlt_bool d0 q0 then Some (M.add a (dred q0) acc') else None
         | None -> None)
      | None -> None) (coq_SWeights oracle s) (Some M.empty)

  (** val weights_distr : d M.t -> A.t -> q **)

  let weights_distr weights a =
    match M.find a weights with
    | Some d2 -> qdiv (d_to_Q d2) (cGamma weights)
    | None -> { qnum = Big.zero; qden = Big.one }

  (** val interp :
      A.t showable -> A.t clientOracle -> A.t com -> cstate -> cstate option **)

  let rec interp h oracle c s =
    match c with
    | CSkip -> Some s
    | CUpdate f ->
      let w = update_weights oracle f s in
      (match w with
       | Some w' ->
         Some { coq_SCosts = (coq_SCosts oracle s); coq_SPrevCosts =
           (coq_SPrevCosts oracle s); coq_SWeights = w'; coq_SEpsilon =
           (coq_SEpsilon oracle s); coq_SOutputs = (coq_SOutputs oracle s);
           coq_SChan = (coq_SChan oracle s); coq_SOracleSt =
           (coq_SOracleSt oracle s) }
       | None -> None)
    | CRecv ->
      let (b, st') =
        oracle.oracle_prerecv (coq_SOracleSt oracle s) (coq_SChan oracle s)
      in
      if b
      then let (c0, st'') = mwu_recv h oracle (coq_SChan oracle s) st' in
           Some { coq_SCosts = c0; coq_SPrevCosts =
           ((coq_SCosts oracle s) :: (coq_SPrevCosts oracle s));
           coq_SWeights = (coq_SWeights oracle s); coq_SEpsilon =
           (coq_SEpsilon oracle s); coq_SOutputs = (coq_SOutputs oracle s);
           coq_SChan = (coq_SChan oracle s); coq_SOracleSt = st'' }
      else None
    | CSend ->
      if oracle.oracle_presend (coq_SOracleSt oracle s)
           (M.elements (coq_SWeights oracle s))
      then let (ch, st') =
             mwu_send oracle (coq_SWeights oracle s) (coq_SOracleSt oracle s)
           in
           let d2 = weights_distr (coq_SWeights oracle s) in
           Some { coq_SCosts = (coq_SCosts oracle s); coq_SPrevCosts =
           (coq_SPrevCosts oracle s); coq_SWeights = (coq_SWeights oracle s);
           coq_SEpsilon = (coq_SEpsilon oracle s); coq_SOutputs =
           (d2 :: (coq_SOutputs oracle s)); coq_SChan = ch; coq_SOracleSt =
           st' }
      else None
    | CSeq (c1, c2) ->
      (match interp h oracle c1 s with
       | Some s' -> interp h oracle c2 s'
       | None -> None)
    | CIter (n0, c0) ->
      Coq_N.iter n0 (fun s0 ->
        match s0 with
        | Some s' -> interp h oracle c0 s'
        | None -> None) (Some s)

  (** val init_map : A.t enumerable -> d M.t **)

  let init_map h1 =
    MProps.of_list (map (fun a -> (a, d1)) (enumerable_fun h1))

  (** val init_cstate : A.t clientOracle -> A.t enumerable -> d -> cstate **)

  let init_cstate oracle h1 epsQ =
    { coq_SCosts = (init_map h1); coq_SPrevCosts = []; coq_SWeights =
      (init_map h1); coq_SEpsilon = epsQ; coq_SOutputs = []; coq_SChan =
      oracle.oracle_bogus_chan; coq_SOracleSt = oracle.oracle_init_state }

  (** val mwu :
      A.t showable -> A.t enumerable -> A.t clientOracle -> d -> Coq_N.t ->
      cstate option **)

  let mwu h h0 oracle eps nx =
    interp h oracle (mult_weights nx) (init_cstate oracle h0 eps)
 end

module MWU =
 functor (A__1:MyOrderedType) ->
 struct
  module A = A__1

  module MWUPre = MWUPre(A__1)

  module A' = MWUPre.A'

  module M = MWUPre.M

  module MFacts = MWUPre.MFacts

  module MProps = MWUPre.MProps

  (** val cGamma : d M.t -> q **)

  let cGamma weights =
    d_to_Q (M.fold (fun _ -> dadd) weights { num = Big.zero; den = Big.one })

  type cstate = MWUPre.cstate = { coq_SCosts : d M.t;
                                  coq_SPrevCosts : d M.t list;
                                  coq_SWeights : d M.t; coq_SEpsilon : 
                                  d; coq_SOutputs : (A__1.t -> q) list;
                                  coq_SChan : A__1.t oracle_chanty;
                                  coq_SOracleSt : A__1.t t1 }

  (** val coq_SCosts : A__1.t clientOracle -> cstate -> d M.t **)

  let coq_SCosts _ c =
    c.coq_SCosts

  (** val coq_SPrevCosts : A__1.t clientOracle -> cstate -> d M.t list **)

  let coq_SPrevCosts _ c =
    c.coq_SPrevCosts

  (** val coq_SWeights : A__1.t clientOracle -> cstate -> d M.t **)

  let coq_SWeights _ c =
    c.coq_SWeights

  (** val coq_SEpsilon : A__1.t clientOracle -> cstate -> d **)

  let coq_SEpsilon _ c =
    c.coq_SEpsilon

  (** val coq_SOutputs :
      A__1.t clientOracle -> cstate -> (A__1.t -> q) list **)

  let coq_SOutputs _ c =
    c.coq_SOutputs

  (** val coq_SChan :
      A__1.t clientOracle -> cstate -> A__1.t oracle_chanty **)

  let coq_SChan _ c =
    c.coq_SChan

  (** val coq_SOracleSt : A__1.t clientOracle -> cstate -> A__1.t t1 **)

  let coq_SOracleSt _ c =
    c.coq_SOracleSt

  (** val mwu_send :
      A__1.t clientOracle -> d M.t -> A__1.t t1 -> A__1.t
      oracle_chanty * A__1.t t1 **)

  let mwu_send oracle m oracle_st =
    oracle.oracle_send oracle_st (M.elements m)

  (** val mwu_recv :
      A__1.t showable -> A__1.t clientOracle -> A__1.t oracle_chanty ->
      A__1.t t1 -> d M.t * A__1.t t1 **)

  let mwu_recv h oracle ch st =
    let (l, st') = oracle.oracle_recv st ch in
    let l' = print_Dvector h l l in ((MProps.of_list l'), st')

  (** val eval_binopc : binop -> d -> d -> d **)

  let eval_binopc b v1 v2 =
    match b with
    | BPlus -> dadd v1 v2
    | BMinus -> dsub v1 v2
    | BMult -> dmult v1 v2

  (** val evalc : A__1.t clientOracle -> A__1.t expr -> cstate -> d option **)

  let rec evalc oracle e s =
    match e with
    | EVal v -> Some v
    | EOpp e' ->
      (match evalc oracle e' s with
       | Some v' -> Some (dopp v')
       | None -> None)
    | EWeight a -> M.find a (coq_SWeights oracle s)
    | ECost a -> M.find a (coq_SCosts oracle s)
    | EEps -> Some (coq_SEpsilon oracle s)
    | EBinop (b, e1, e2) ->
      (match evalc oracle e1 s with
       | Some v1' ->
         (match evalc oracle e2 s with
          | Some v2' -> Some (eval_binopc b v1' v2')
          | None -> None)
       | None -> None)

  (** val update_weights :
      A__1.t clientOracle -> (A__1.t -> A__1.t expr) -> cstate -> d M.t option **)

  let update_weights oracle f s =
    M.fold (fun a _ acc ->
      match acc with
      | Some acc' ->
        (match evalc oracle (f a) s with
         | Some q0 ->
           if dlt_bool d0 q0 then Some (M.add a (dred q0) acc') else None
         | None -> None)
      | None -> None) (coq_SWeights oracle s) (Some M.empty)

  (** val weights_distr : d M.t -> A__1.t -> q **)

  let weights_distr weights a =
    match M.find a weights with
    | Some d2 -> qdiv (d_to_Q d2) (cGamma weights)
    | None -> { qnum = Big.zero; qden = Big.one }

  (** val interp :
      A__1.t showable -> A__1.t clientOracle -> A__1.t com -> cstate ->
      cstate option **)

  let rec interp h oracle c s =
    match c with
    | CSkip -> Some s
    | CUpdate f ->
      let w = update_weights oracle f s in
      (match w with
       | Some w' ->
         Some { coq_SCosts = (coq_SCosts oracle s); coq_SPrevCosts =
           (coq_SPrevCosts oracle s); coq_SWeights = w'; coq_SEpsilon =
           (coq_SEpsilon oracle s); coq_SOutputs = (coq_SOutputs oracle s);
           coq_SChan = (coq_SChan oracle s); coq_SOracleSt =
           (coq_SOracleSt oracle s) }
       | None -> None)
    | CRecv ->
      let (b, st') =
        oracle.oracle_prerecv (coq_SOracleSt oracle s) (coq_SChan oracle s)
      in
      if b
      then let (c0, st'') = mwu_recv h oracle (coq_SChan oracle s) st' in
           Some { coq_SCosts = c0; coq_SPrevCosts =
           ((coq_SCosts oracle s) :: (coq_SPrevCosts oracle s));
           coq_SWeights = (coq_SWeights oracle s); coq_SEpsilon =
           (coq_SEpsilon oracle s); coq_SOutputs = (coq_SOutputs oracle s);
           coq_SChan = (coq_SChan oracle s); coq_SOracleSt = st'' }
      else None
    | CSend ->
      if oracle.oracle_presend (coq_SOracleSt oracle s)
           (M.elements (coq_SWeights oracle s))
      then let (ch, st') =
             mwu_send oracle (coq_SWeights oracle s) (coq_SOracleSt oracle s)
           in
           let d2 = weights_distr (coq_SWeights oracle s) in
           Some { coq_SCosts = (coq_SCosts oracle s); coq_SPrevCosts =
           (coq_SPrevCosts oracle s); coq_SWeights = (coq_SWeights oracle s);
           coq_SEpsilon = (coq_SEpsilon oracle s); coq_SOutputs =
           (d2 :: (coq_SOutputs oracle s)); coq_SChan = ch; coq_SOracleSt =
           st' }
      else None
    | CSeq (c1, c2) ->
      (match interp h oracle c1 s with
       | Some s' -> interp h oracle c2 s'
       | None -> None)
    | CIter (n0, c0) ->
      Coq_N.iter n0 (fun s0 ->
        match s0 with
        | Some s' -> interp h oracle c0 s'
        | None -> None) (Some s)

  (** val init_map : A__1.t enumerable -> d M.t **)

  let init_map h1 =
    MProps.of_list (map (fun a -> (a, d1)) (enumerable_fun h1))

  (** val init_cstate :
      A__1.t clientOracle -> A__1.t enumerable -> d -> cstate **)

  let init_cstate oracle h1 epsQ =
    { coq_SCosts = (init_map h1); coq_SPrevCosts = []; coq_SWeights =
      (init_map h1); coq_SEpsilon = epsQ; coq_SOutputs = []; coq_SChan =
      oracle.oracle_bogus_chan; coq_SOracleSt = oracle.oracle_init_state }

  (** val mwu :
      A__1.t showable -> A__1.t enumerable -> A__1.t clientOracle -> d ->
      Coq_N.t -> cstate option **)

  let mwu h h0 oracle eps nx =
    interp h oracle (mult_weights nx) (init_cstate oracle h0 eps)
 end

(** val r_InA_bool : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec r_InA_bool r_bool a = function
| [] -> false
| a' :: l' -> if r_bool a a' then true else r_InA_bool r_bool a l'

(** val r_NoDupA_bool : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool **)

let rec r_NoDupA_bool r_bool = function
| [] -> true
| a :: l' -> if r_InA_bool r_bool a l' then false else r_NoDupA_bool r_bool l'

(** val inRel_bool : ('a1 -> 'a2 -> bool) -> 'a1 -> 'a2 list -> bool **)

let rec inRel_bool aB_b a = function
| [] -> false
| b :: l' -> if aB_b a b then true else inRel_bool aB_b a l'

(** val inRel_list_bool :
    ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool **)

let rec inRel_list_bool aB_b lA lB =
  match lA with
  | [] -> true
  | a :: lA' ->
    if inRel_bool aB_b a lB then inRel_list_bool aB_b lA' lB else false

(** val inRel_list_complete_bool :
    ('a1 -> 'a2 -> bool) -> 'a1 enumerable -> 'a2 list -> bool **)

let inRel_list_complete_bool =
  inRel_list_bool

(** val num_strategies : nat **)

let num_strategies =
  S (S (S (S (S (S (S (S (S (S O)))))))))

(** val eta : d **)

let eta =
  { num = (Big.doubleplusone Big.one); den = (Big.doubleplusone Big.one) }

(** val num_rounds : Big.big_int **)

let num_rounds =
  Coq_N.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val inputChanName : char list **)

let inputChanName =
  '.'::('/'::('c'::('l'::('i'::('e'::('n'::('t'::('I'::('n'::('p'::('u'::('t'::[]))))))))))))

(** val outputChanName : char list **)

let outputChanName =
  '.'::('/'::('c'::('l'::('i'::('e'::('n'::('t'::('O'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))

module Coq_strategies_bound =
 struct
  (** val n : nat **)

  let n =
    num_strategies

  (** val n_gt0 : __ **)

  let n_gt0 =
    __
 end

module MProps = MyOrdNatDepProps(Coq_strategies_bound)

module M = MProps.M
module Coq__2 = M

type oracleState = (M.t * d) list * unit

(** val bogus_result : oracleState **)

let bogus_result =
  ([], ())

type inChan = in_channel

type outChan = out_channel

(** val open_in : char list -> inChan **)

let open_in = let charlToString l : string =
        String.concat "" (List.map (String.make 1) l) in
          (fun x -> open_in (charlToString x))

(** val open_out : char list -> outChan **)

let open_out = let charlToString l : string =
        String.concat "" (List.map (String.make 1) l) in
          (fun x -> open_out (charlToString x))

(** val inChan_recv : inChan -> (M.t * d) list **)

let inChan_recv = fun chan -> Marshal.from_channel chan

(** val outChan_send : outChan -> (M.t * d) list -> unit **)

let outChan_send = fun chan data -> Marshal.to_channel chan data []; flush chan

type chan = inChan * outChan

(** val openChan : char list -> char list -> chan **)

let openChan inS outS =
  ((open_in inS), (open_out outS))

(** val defaultChan : chan **)

let defaultChan =
  openChan inputChanName outputChanName

(** val prerecv_recv : chan -> oracleState **)

let prerecv_recv x =
  ((inChan_recv (fst x)), ())

(** val send : oracleState -> (M.t * d) list -> chan * oracleState **)

let send st data =
  (defaultChan, ((fst st), (outChan_send (snd defaultChan) data)))

(** val mt_eqb : M.t -> M.t -> bool **)

let mt_eqb p q0 =
  N.eqb (M.coq_val p) (M.coq_val q0)

(** val uniqR_bool : (M.t * d) -> (M.t * d) -> bool **)

let uniqR_bool p q0 =
  mt_eqb (fst p) (fst q0)

(** val prerecv_chk_nodup : (M.t * d) list -> bool **)

let prerecv_chk_nodup =
  r_NoDupA_bool uniqR_bool

(** val in_range_bool : M.t -> (M.t * d) -> bool **)

let in_range_bool n0 p =
  (&&) ((&&) (mt_eqb n0 (fst p)) (dle_bool (dopp d1) (snd p)))
    (dle_bool (snd p) d1)

(** val prerecv_chk_complete_in_range_bool : (M.t * d) list -> bool **)

let prerecv_chk_complete_in_range_bool =
  inRel_list_complete_bool in_range_bool M.enumerable

(** val prerecv : oracleState -> chan -> bool * oracleState **)

let prerecv _ c =
  let message = prerecv_recv c in
  (((&&) (prerecv_chk_complete_in_range_bool (fst message))
     (prerecv_chk_nodup (fst message))), message)

(** val recv : oracleState -> chan -> (M.t * d) list * oracleState **)

let recv s _ =
  ((fst s), s)

(** val presend : oracleState -> (M.t * d) list -> bool **)

let presend _ _ =
  true

(** val myOracle : M.t clientOracle **)

let myOracle =
  { oracle_init_state = (Obj.magic bogus_result); oracle_bogus_chan =
    (Obj.magic defaultChan); oracle_prerecv = (Obj.magic prerecv);
    oracle_recv = (Obj.magic recv); oracle_presend = (Obj.magic presend);
    oracle_send = (Obj.magic send) }

module MWUextract = MWU(M)

(** val extractedMW : MWUextract.cstate option **)

let extractedMW =
  MWUextract.mwu M.showable M.enumerable myOracle eta num_rounds
